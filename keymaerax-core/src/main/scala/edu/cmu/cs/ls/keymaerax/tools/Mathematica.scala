/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.InvGenTool
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.SimulationTool.{SimRun, SimState, Simulation}

import scala.collection.immutable.{Map, Seq}

/**
 * Mathematica/Wolfram Engine tool for quantifier elimination and solving differential equations.
 * @param link How to connect to the tool, either JLink or WolframScript.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 * @todo Code Review: Move non-critical tool implementations into a separate package tactictools
 */
class Mathematica(private[tools] val link: MathematicaLink, override val name: String) extends ToolBase(name) with QETool with InvGenTool with ODESolverTool with CounterExampleTool
    with SimulationTool with DerivativeTool with EquationSolverTool with SimplificationTool with AlgebraTool
    with PDESolverTool with ToolOperationManagement {

  private val mQE = new MathematicaQETool(link)
  private val mPegasus = new MathematicaInvGenTool(link)
  private val mSmt = new MathematicaToSMT(link, "Mathematica2SMT")
  private val mCEX = new MathematicaCEXTool(link)
  private val mODE = new MathematicaODESolverTool(link)
  private val mPDE = new MathematicaPDESolverTool(link)
  private val mSim = new MathematicaSimulationTool(link)
  private val mSolve = new MathematicaEquationSolverTool(link)
  private val mAlgebra = new MathematicaAlgebraTool(link)
  private val mSimplify = new MathematicaSimplificationTool(link)

  private val qeInitialTimeout = Integer.parseInt(Configuration(Configuration.Keys.QE_TIMEOUT_INITIAL))
  private val qeCexTimeout = Integer.parseInt(Configuration(Configuration.Keys.QE_TIMEOUT_CEX))
  private var qeMaxTimeout = Integer.parseInt(Configuration(Configuration.Keys.QE_TIMEOUT_MAX))

  private val memoryLimit: Long = Configuration.getOption(Configuration.Keys.MATHEMATICA_MEMORY_LIMIT).map(java.lang.Long.parseLong).getOrElse(-1)

  override def init(config: Map[String,String]): Unit = {
    mQE.memoryLimit = memoryLimit
    mPegasus.memoryLimit = memoryLimit
    mCEX.memoryLimit = memoryLimit
    mODE.memoryLimit = memoryLimit
    mSim.memoryLimit = memoryLimit
    mSolve.memoryLimit = memoryLimit
    mAlgebra.memoryLimit = memoryLimit
    mSimplify.memoryLimit = memoryLimit

    initialized = link match {
      case l: JLinkMathematicaLink =>
        val linkName = config.get("linkName") match {
          case Some(ln) => ln
          case None =>
            throw new IllegalArgumentException(
              """Mathematica not configured. Missing configuration parameter 'linkName'
                |Please configure settings in the UI.
                |Or specify the paths explicitly from command line by running
                |  java -jar keymaerax.jar -mathkernel pathtokernel -jlink pathtojlink
              """.stripMargin)
        }
        val libDir = config.get("libDir") // doesn't need to be defined
        l.init(linkName, libDir, config.getOrElse("tcpip", "true"))
      case l: WolframScript => l.init()
    }
  }

  /** Closes the connection to Mathematica */
  override def shutdown(): Unit = {
    mQE.shutdown()
    mPegasus.shutdown()
    mSmt.shutdown()
    mCEX.shutdown()
    mODE.shutdown()
    mPDE.shutdown()
    mSim.shutdown()
    mSolve.shutdown()
    mAlgebra.shutdown()
    mSimplify.shutdown()
    //@note last, because we want to shut down all executors (tool threads) before shutting down the JLink interface
    link match {
      case l: JLinkMathematicaLink => l.shutdown()
      case l: WolframScript => l.shutdown()
    }
    initialized = false
  }

  /** Quantifier elimination on the specified formula, returns an equivalent quantifier-free formula plus Mathematica input/output as evidence */
  override def qeEvidence(formula: Formula): (Formula, Evidence) = {
    mQE.timeout = qeInitialTimeout
    try {
      mQE.qeEvidence(formula)
    } catch {
      case _: MathematicaComputationAbortedException =>
        mCEX.timeout = qeCexTimeout
        val cex = try {
          mCEX.findCounterExample(stripUniversalClosure(formula))
        } catch {
          case _: MathematicaComputationAbortedException => None
          case _: MathematicaComputationFailedException => None
          case _: ToolException => None
          case ex: MathematicaComputationExternalAbortException =>
            //@note external abort means do not try any further
            throw ex
        }
        cex match {
          case None =>
            mQE.timeout = qeMaxTimeout
            mQE.qeEvidence(formula)
          case Some(cexFml) => (False, ToolEvidence(List("input" -> formula.prettyString, "output" -> cexFml.mkString(","))))
        }
      case ex: MathematicaComputationExternalAbortException => throw ex
    }
  }

  /** Strips the universal quantifiers from a formula. Assumes shape \forall x (p(x) -> q(x)) */
  private def stripUniversalClosure(fml: Formula): Formula = fml match {
    case f: Imply => f
    case Forall(_, f) => stripUniversalClosure(f)
  }

  /** Returns a formula describing the symbolic solution of the specified differential equation system.
   * @param diffSys The differential equation system
   * @param diffArg The independent variable of the ODE, usually time
   * @param iv Names of initial values per variable, e.g., x -> x_0
   * @return The solution, if found. None otherwise.
   */
  override def odeSolve(diffSys: DifferentialProgram, diffArg: Variable,
                        iv: Predef.Map[Variable, Variable]): Option[Formula] = mODE.odeSolve(diffSys, diffArg, iv)

  override def deriveBy(term: Term, v: Variable): Term = mODE.deriveBy(term, v)

  /**
   * Returns a counterexample for the specified formula.
   * @param formula The formula.
   * @return A counterexample, if found. None otherwise.
   */
  override def findCounterExample(formula: Formula): Option[Predef.Map[NamedSymbol, Expression]] = {
    mCEX.timeout = Integer.parseInt(Configuration.getOption(Configuration.Keys.CEX_SEARCH_DURATION).getOrElse("10"))
    mCEX.findCounterExample(formula)
  }

  /**
    * Returns a list of simulated states, where consecutive states in the list satisfy 'stateRelation'. The state
    * relation is a modality-free first-order formula. The simulation starts in a state where initial holds (first-order
    * formula).
    * @param initial A first-order formula describing the initial state.
    * @param stateRelation A first-order formula describing the relation between consecutive states. The relationship
    *                      is by name convention: postfix 'pre': prior state; no postfix: posterior state.
    * @param steps The length of the simulation run (i.e., number of states).
    * @param n The number of simulations (different initial states) to create.
    * @return 'n' lists (length 'steps') of simulated states.
    */
  override def simulate(initial: Formula, stateRelation: Formula, steps: Int = 10, n: Int = 1): Simulation = mSim.simulate(initial, stateRelation, steps, n)

  /**
    * Returns a list of simulated states, where consecutive states in the list satisfy 'stateRelation'. The state
    * relation is a modality-free first-order formula. The simulation starts in the specified initial state.
    * @param initial The initial state: concrete values .
    * @param stateRelation A first-order formula describing the relation between consecutive states. The relationship
    *                      is by name convention: postfix 'pre': prior state; no postfix: posterior state.
    * @param steps The length of the simulation run (i.e., number of states).
    * @return A list (length 'steps') of simulated states.
    */
  override def simulateRun(initial: SimState, stateRelation: Formula, steps: Int = 10): SimRun = mSim.simulateRun(initial, stateRelation, steps)

  /*override*/ def pdeSolve(diffSys: DifferentialProgram): Iterator[Term] = mPDE.pdeSolve(diffSys)
  override def solve(equations: Formula, vars: List[Expression]): Option[Formula] = mSolve.solve(equations,vars)
  override def quotientRemainder(term: Term, div: Term, x:Variable): (Term,Term) = mAlgebra.quotientRemainder(term,div,x)
  override def groebnerBasis(polynomials: List[Term]): List[Term] = mAlgebra.groebnerBasis(polynomials)
  override def polynomialReduce(polynomial: Term, GB: List[Term]): (List[Term], Term) = mAlgebra.polynomialReduce(polynomial, GB)
  override def simplify(expr: Expression, assumptions: List[Formula]): Expression = mSimplify.simplify(expr, assumptions)
  override def simplify(expr: Formula, assumptions: List[Formula]): Formula = mSimplify.simplify(expr, assumptions)
  override def simplify(expr: Term, assumptions: List[Formula]): Term = mSimplify.simplify(expr, assumptions)
  override def invgen(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): Seq[Either[Seq[(Formula, String)],Seq[(Formula, String)]]] = mPegasus.invgen(ode, assumptions, postCond)
  override def lzzCheck(ode: ODESystem, inv: Formula): Boolean = mPegasus.lzzCheck(ode, inv)
  override def refuteODE(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): Option[Map[NamedSymbol, Expression]] = mPegasus.refuteODE(ode, assumptions, postCond)
  override def genODECond(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): (List[Formula],List[Formula]) = mPegasus.genODECond(ode, assumptions, postCond)

  def invarToSMT(name : String, seq : Sequent) : String = mSmt.invarToSMT(name, seq)

  /** Restarts the MathKernel with the current configuration */
  override def restart(): Unit = link match {
    case l: JLinkMathematicaLink => l.restart()
    case l: WolframScript => l.restart()
  }

  override def cancel(): Boolean = link.cancel()

  override def setOperationTimeout(timeout: Int): Unit = qeMaxTimeout = timeout
  override def getOperationTimeout: Int = qeMaxTimeout
  override def getAvailableWorkers: Int = mQE.availableWorkers
}
