package edu.cmu.cs.ls.keymaerax.tools


import java.io._
import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.InvGenTool
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.SimulationTool.{SimRun, SimState, Simulation}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable.{Map, Seq}

import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.{KExpr, MExpr}

import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper

import edu.cmu.cs.ls.keymaerax.btactics.Generator.Generator
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._

import spray.json._
import DefaultJsonProtocol._

/**
 * Mathematica/Wolfram Engine tool for quantifier elimination and solving differential equations.
 * @param link How to connect to the tool, either JLink or WolframScript.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 * @todo Code Review: Move non-critical tool implementations into a separate package tactictools
 */
class MathematicaToSMT(private[tools] val link: MathematicaLink,
  override val name: String) extends ToolBase(name) {

  /** Restarts the MathKernel with the current configuration */
  override def restart(): Unit = link match {
    case l: JLinkMathematicaLink => l.restart()
    case l: WolframScript => l.restart()
  }

  override def shutdown(): Unit = {
    //@note last, because we want to shut down all executors (tool threads) before shutting down the JLink interface
    link match {
      case l: JLinkMathematicaLink => l.shutdown()
      case l: WolframScript => l.shutdown()
    }
    initialized = false
  }

  override def init(config: Map[String,String]): Unit = {
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

  def toSMT() : Unit = {
    val converter = DefaultSMTConverter
    val ml = new BaseKeYmaeraMathematicaBridge[KExpr](link, KeYmaeraToMathematica, MathematicaToKeYmaera) {}
    val command = s"""
strings = Import["/Users/sergiomover/works/scratch/lzz_files/lzzfast.txt"];
ToExpression[strings, InputForm]""".stripMargin.trim()

// kyx`

    try {
      val (output, result) = ml.runUnchecked(command)
      println("Result of command: " + result.prettyString + " from raw output " + output)

      val formula = result match {
        case fml : Formula => fml
        case _ => {
          println(result.kind)
          throw ToolException("not a formula!")
        }
      }

      val smt  = converter(formula)
      val pw = new PrintWriter(new File("/tmp/lzzfast.smt2" ))
      pw.write(smt)
      pw.close

    } catch {
      case ex: ConversionException =>
        println("conversion exception", ex)
        ()
    }
  }
}

abstract class MyConverter extends SMTConverter {
  override def apply(expr: Formula): String = {
    val res = convertToSMT(expr)
    res
  }

  protected def convertToSMT(expr: Expression) : String = expr match {
    case t: Term  => convertTerm(t)
    case f: Formula => convertFormula(f)
    case _ => throw new SMTConversionException("The input expression: \n" + expr + "\nis expected to be formula.")
  }
}

object DefaultMySMTConverter extends MyConverter {
  def getSmt(expr : Expression) : (List[String], String) = {
    generateSMTInner(expr)
  }
}

case class LzzProblem(name : String,
  contVars : List[String],
  varsDecl : Set[String],
  vectorField : List[String],
  constraints : String,
  candidate : String
)

case class InvarProblem(name : String,
  contVars : List[String],
  varsDecl : Set[String],
  vectorField : List[String],
  constraints : String,
  antecedent : String,
  consequent : String,
  predicates : List[String],
)

case class ODERepr(contVars : List[String],
  varsDecl : Set[String],
  vectorField : List[String],
  constraints : String)

object MathematicaToSMT {

  def getSMTForODE(converter : MyConverter, ode : ODESystem) : ODERepr = {
    // Hack representing vars and terms as equalities
    var contVarsSymb = DifferentialHelper.getPrimedVariables(ode)
    val appVars = contVarsSymb.map(v =>
      DefaultMySMTConverter.getSmt(Equal(v, "0".asTerm)))
    val varsTmp = appVars.map(v => v._1)
    val contVars = varsTmp.foldLeft (List[String]()) ((vList, varList) => {
      varList.foldLeft (vList) ( (vList, varDecl) => {varDecl :: vList})
    })

    val atomicOdes : List[AtomicODE] = DifferentialHelper.atomicOdes(ode)
    val var2ode : Map[Variable,Term] =
      atomicOdes.foldLeft(Map[Variable,Term]()) ( (map, atomicOde) =>
        map + (atomicOde.xp.x -> atomicOde.e))

    // Extracts the odes with the same order of contVars
    val vfAll = contVarsSymb.foldLeft (List[(List[String], String)]()) ( (acc, contVar) => {
      val term : Term = var2ode(contVar)
      DefaultMySMTConverter.getSmt(Equal(term, "0".asTerm)) :: acc
    })

    // val vfAll  = DifferentialHelper.atomicOdes(ode).map(o =>
    //   DefaultMySMTConverter.getSmt(Equal(o.e, "0".asTerm)))
    val vfVars = vfAll.map(l => l._1)
    val vfSMT = vfAll.map(l => l._2)
    val vfSet = vfVars.foldLeft (Set[String]()) ((vset, varList) => {
      varList.foldLeft (vset) ( (vset, varDecl) => {vset + varDecl})
    })
    val (constraintsVars, constraintsSMT) = DefaultMySMTConverter.getSmt(ode.constraint)

    ODERepr(contVars, vfSet ++ constraintsVars, vfSMT, constraintsSMT)
  }

  def lzzToSMT(name : String, ode : ODESystem, invar : Formula) : String = {
    val converter = DefaultMySMTConverter

    val odeRepr = MathematicaToSMT.getSMTForODE(converter, ode)
    val (invarVars, invarSMT) = DefaultMySMTConverter.getSmt(invar)

    implicit val lzzProblemFormat: JsonFormat[LzzProblem] = jsonFormat6(LzzProblem)
    val problemJson = LzzProblem(name,
      odeRepr.contVars,
      odeRepr.varsDecl ++ invarVars,
      odeRepr.vectorField,
      odeRepr.constraints,
      invarSMT
    )

    val jsonAst = problemJson.toJson
    return jsonAst.prettyPrint
  }

  /**
    * Converts an invariant generation problem to "SMT"
    * 
    * The output file is a json file containing SMT formulas.
    */
  def invarToSMT(name : String, seq : Sequent) : String = {
    val converter = DefaultMySMTConverter

    def getSingleInvProblem(): Generator[InvarProblem] = (sequent,pos) => sequent.sub(pos) match {
      // The semantics of sequent `ante |- succ` is the conjunction of the
      // formulas in `ante` implying the disjunction of the formulas in `succ`.

      case Some(Box(ode: ODESystem, post: Formula)) if post.isFOL => {
        val odeRepr = MathematicaToSMT.getSMTForODE(converter, ode)
        val (antVars, antSMT) : (List[String], String) = DefaultMySMTConverter.getSmt(
          sequent.ante.reduce(And)
        )
        val (subVars, subSMT) : (List[String], String) = DefaultMySMTConverter.getSmt(post)

        val invarProblem = InvarProblem(name,
          odeRepr.contVars,
          odeRepr.varsDecl ++ antVars ++ subVars,
          odeRepr.vectorField,
          odeRepr.constraints,
          antSMT,
          subSMT,
          List()
        )
        List(invarProblem).toStream
      }
      case _ => {
        throw new IllegalArgumentException("")
      }
    }

    lazy val problemsCandidate: Generator[InvarProblem] = getSingleInvProblem()
    val problems = problemsCandidate(seq, SuccPos(0)).toList

    implicit val invarProblemFormat: JsonFormat[InvarProblem] = jsonFormat8(InvarProblem)
    val jsonAst = problems.toJson
    return jsonAst.prettyPrint
  }
}
