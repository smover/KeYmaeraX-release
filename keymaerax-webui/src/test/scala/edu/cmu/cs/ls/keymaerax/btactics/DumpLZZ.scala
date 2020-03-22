package edu.cmu.cs.ls.keymaerax.btactics

import java.io.PrintWriter

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.{AnnotationProofHint, PegasusProofHint}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import testHelper.KeYmaeraXTestTags.{ExtremeTest, SlowTest}

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.MathematicaComputationAbortedException

import edu.cmu.cs.ls.keymaerax.tools.MathematicaToSMT

import scala.collection.immutable.IndexedSeq
import org.scalatest.prop.TableDrivenPropertyChecks.forEvery
import org.scalatest.prop.Tables._
import org.scalatest.time.SpanSugar._
import org.scalatest.LoneElement._

/**
 * DumpLZZ problem
 */
class DumpLZZ extends TacticTestBase {
  val randomTrials = 500
  val randomComplexity = 6
  val rand = new RandomFormula()

  it should "print LZZ benchmarks as output" taggedAs SlowTest in withMathematica { tool =>
    withTemporaryConfig(Map(Configuration.Keys.PEGASUS_INVCHECK_TIMEOUT -> "-1")) {
      val entries = KeYmaeraXArchiveParser.parse(io.Source.fromInputStream(
        getClass.getResourceAsStream("/keymaerax-projects/benchmarks/nonlinear.kyx")).mkString)
      val annotatedInvariants: ConfigurableGenerator[Formula] = TactixLibrary.invGenerator match {
        case gen: ConfigurableGenerator[Formula] => gen
      }

      forEvery(Table(("Name", "Model"),
        entries.map(e => e.name -> e.model): _*).
        filter({ case (_, Imply(_, Box(_: ODESystem, _))) => true case _ => false })) {
        (name, model) =>
          val Imply(_, Box(ode@ODESystem(_, _), _)) = model
          annotatedInvariants.products.get(ode) match {
            case Some(invs) => {
              val myRes = invs.foldLeft("true".asFormula) { (acc : Formula, i : Object) => 
                i match {
                  case (a : Formula, _) => And(acc, a)
                  case _ => acc
                }
              }
              val jsonRepr = MathematicaToSMT.lzzToSMT(name, ode, myRes)

              val fileName = name.replaceAll("[^a-zA-Z0-9\\.\\-]", "_");
              val filePath = "/tmp/" + fileName + ".lzz"

              new PrintWriter(filePath) {
                write(jsonRepr);
                close
              }

              println(s"Dumped $name into $filePath")
            }
            case None => // no invariant to fast-check
          }

      }
    }
  }

  it should "print invariant generation problem as output" taggedAs SlowTest in withMathematica { tool =>
    withTemporaryConfig(Map(Configuration.Keys.PEGASUS_INVCHECK_TIMEOUT -> "-1")) {
      val entries = KeYmaeraXArchiveParser.parse(io.Source.fromInputStream(
        getClass.getResourceAsStream("/keymaerax-projects/benchmarks/nonlinear.kyx")).mkString)
      val annotatedInvariants: ConfigurableGenerator[Formula] = TactixLibrary.invGenerator match {
        case gen: ConfigurableGenerator[Formula] => gen
      }

      forEvery(Table(("Name", "Model"),
        entries.map(e => e.name -> e.model): _*).
        filter({ case (_, Imply(_, Box(_: ODESystem, _))) => true case _ => false })) {
        (name, model) =>
        // val (model, _) = parseStripHints(modelContent)
        model match {
          case Imply(ante, succ@Box(_: ODESystem, _)) =>
            {
              val seq = Sequent(IndexedSeq(ante), IndexedSeq(succ))
              println(s"Generating invariants $name")

              val jsonRepr = MathematicaToSMT.invarToSMT(name, seq)
              val fileName = name.replaceAll("[^a-zA-Z0-9\\.\\-]", "_");
              val filePath = "/tmp/" + fileName + ".invar"

              new PrintWriter(filePath) {
                write(jsonRepr);
                close
              }

              println(s"Dumped $name into $filePath")
            }
          case _ => ()
        }
      }
    }
  }
}
