package edu.cmu.cs.ls.keymaerax.tools


import java.io._
import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.InvGenTool
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.SimulationTool.{SimRun, SimState, Simulation}

import scala.collection.immutable.{Map, Seq}

import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.{KExpr, MExpr}

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
