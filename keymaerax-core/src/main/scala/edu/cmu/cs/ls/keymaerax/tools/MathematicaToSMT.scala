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

object MathematicaToSMT {
  def lzzToSMT(name : String, ode : ODESystem, invar : Formula) : String = {
    val converter = DefaultMySMTConverter

    // Hack representing vars and terms as equalities
    val appVars = DifferentialHelper.getPrimedVariables(ode).map(v =>
      DefaultMySMTConverter.getSmt(Equal(v, "0".asTerm)))
    val varsTmp = appVars.map(v => v._1)
    val contVars = varsTmp.foldLeft (List[String]()) ((vList, varList) => {
      varList.foldLeft (vList) ( (vList, varDecl) => {varDecl :: vList})
    })

    val vfAll  = DifferentialHelper.atomicOdes(ode).map(o =>
      DefaultMySMTConverter.getSmt(Equal(o.e, "0".asTerm)))
    val vfVars = vfAll.map(l => l._1)
    val vfSMT = vfAll.map(l => l._2)
    val vfSet = vfVars.foldLeft (Set[String]()) ((vset, varList) => {
      varList.foldLeft (vset) ( (vset, varDecl) => {vset + varDecl})
    })

    val (invarVars, invarSMT) = DefaultMySMTConverter.getSmt(invar)

    val (constraintsVars, constraintsSMT) = DefaultMySMTConverter.getSmt(invar)

    val allVars = vfSet ++ invarVars ++ constraintsVars

    implicit val lzzProblemFormat: JsonFormat[LzzProblem] = jsonFormat6(LzzProblem)
    val problemJson = LzzProblem(name,
      contVars,
      allVars,
      vfSMT,
      constraintsSMT,
      invarSMT
    )


    val jsonAst = problemJson.toJson
    return jsonAst.prettyPrint
  }
}
