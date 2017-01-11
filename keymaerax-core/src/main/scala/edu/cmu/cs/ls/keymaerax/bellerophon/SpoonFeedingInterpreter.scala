/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

/**
  * Sequential interpreter for Bellerophon tactic expressions: breaks apart combinators and spoon-feeds "atomic" tactics
  * to another interpreter.
  * @param listeners Creates listeners from tactic names.
  * @param inner Processes atomic tactics.
  * @author Nathan Fulton
  * @author Andre Platzer
  * @author Stefan Mitsch
  */
case class SpoonFeedingInterpreter(listeners: (String, Int) => Seq[IOListener], inner: Seq[IOListener] => Interpreter, descend: Int = 0) extends Interpreter {
  override def apply(expr: BelleExpr, v: BelleValue): BelleValue = runTactic((expr, v)::Nil, 0, descend)

  private def runTactic(branches: Seq[(BelleExpr, BelleValue)], branch: Int, level: Int): BelleValue = {
    branches(branch)._1 match {
      // combinators
      case SeqTactic(left, right) =>
        val leftResult = try {
          runTactic(branches.updated(branch, (left, branches(branch)._2)), branch, level)
        } catch {
          case e: BelleThrowable => throw e.inContext(SeqTactic(e.context, right), "Failed left-hand side of &: " + left)
        }
        try {
          runTactic(branches.updated(branch, (right, leftResult)), branch, level)
        } catch {
          case e: BelleThrowable => throw e.inContext(SeqTactic(left, e.context), "Failed right-hand side of &: " + right)
        }
      case EitherTactic(left, right) => try {
        val leftResult = runTactic(branches.updated(branch, (left, branches(branch)._2)), branch, level)
        (leftResult, left) match {
          case (BelleProvable(p, _), _) /*if p.isProved*/ => leftResult
          case (_, x: PartialTactic) => leftResult
          case _ => throw new BelleThrowable("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(EitherTactic(BelleDot, right), "Failed left-hand side of |:" + left)
        }
      } catch {
        //@todo catch a little less. Just catching proper tactic exceptions, maybe some ProverExceptions et al., not swallow everything
        case eleft: BelleThrowable =>
          val rightResult = try {
            runTactic(branches.updated(branch, (right, branches(branch)._2)), branch, level)
          } catch {
            case e: BelleThrowable => throw e.inContext(EitherTactic(eleft.context, e.context), "Failed: both left-hand side and right-hand side " + branches(branch)._1)
          }
          (rightResult, right) match {
            case (BelleProvable(p, _), _) /*if p.isProved*/ => rightResult
            case (_, x: PartialTactic) => rightResult
            case _ => throw new BelleThrowable("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(EitherTactic(left, BelleDot), "Failed right-hand side of |: " + right)
          }
      }
      case SaturateTactic(child) =>
        var prev: BelleValue = null
        var result: BelleValue = branches(branch)._2
        do {
          prev = result
          //@todo effect on listeners etc.
          try {
            result = runTactic(branches.updated(branch, (child, result)), branch, level)
          } catch {
            case e: BelleThrowable => /*@note child no longer applicable */ result = prev
          }
        } while (result != prev)
        result
      case RepeatTactic(child, times) =>
        var result = branches(branch)._2
        for (i <- 1 to times) try {
          result = runTactic(branches.updated(branch, (child, result)), branch, level)
        } catch {
          case e: BelleThrowable => throw e.inContext(RepeatTactic(e.context, times),
            "Failed while repating tactic " + i + "th iterate of " + times + ": " + child)
        }
        result
      case BranchTactic(children) => branches(branch)._2 match {
        case BelleProvable(p, labels) =>
          if (children.length != p.subgoals.length)
            throw new BelleThrowable("<(e)(v) is only defined when len(e) = len(v), but " + children.length + "!=" + p.subgoals.length).inContext(branches(branch)._1, "")

          //@todo might be unnecessarily complicated
          val branchTactics: Seq[(BelleExpr, BelleValue)] = children.zip(p.subgoals.map(sg => BelleProvable(ProvableSig.startProof(sg), labels)))
          val newBranches = branches.updated(branch, branchTactics.head) ++ branchTactics.tail
          val newBranchIdx = branches.length until newBranches.length
          val BelleProvable(first, _) = runTactic(newBranches, branch, level)
          val result = newBranchIdx.foldLeft((branch, newBranches, p(first, branch)))({
            case ((previ, remainingBranches, mergedProvable), i) =>
              val remainder =
                if (mergedProvable.subgoals.size < p.subgoals.size) remainingBranches.patch(previ, Nil, 1)
                else remainingBranches
              val closed = newBranches.size - remainder.size
              val BelleProvable(branchResult, _) = runTactic(remainder, i-closed, level)
              val branchIdx = i - branches.length + 1
              val closedOverall = p.subgoals.size - mergedProvable.subgoals.size
              (i-closed, remainder, mergedProvable(branchResult, branchIdx - closedOverall))
          })._3
          BelleProvable(result)
        case _ => throw new BelleThrowable("Cannot perform branching on a goal that is not a BelleValue of type Provable.").inContext(branches(branch)._1, "")
      }
      case OnAll(e) =>
        val provable = branches(branch)._2 match {
          case BelleProvable(p, _) => p
          case _ => throw new BelleThrowable("Cannot attempt OnAll with a non-Provable value.").inContext(branches(branch)._1, "")
        }
        //@todo actually it would be nice to throw without wrapping inside an extra BranchTactic context
        try {
          runTactic(branches.updated(branch, (BranchTactic(Seq.tabulate(provable.subgoals.length)(_ => e)), branches(branch)._2)), branch, level)
        } catch {
          case e: BelleThrowable => throw e.inContext(OnAll(e.context), "")
        }

      case ChooseSome(options, e) =>
        //@todo specialization to A=Formula should be undone
        val opts = options().asInstanceOf[Iterator[Formula]]
        var errors = ""
        while (opts.hasNext) {
          val o = opts.next()
          if (BelleExpr.DEBUG) println("ChooseSome: try " + o)
          val someResult: Option[BelleValue] = try {
            Some(runTactic(branches.updated(branch, (e.asInstanceOf[Formula=>BelleExpr](o.asInstanceOf[Formula]), branches(branch)._2)), branch, level))
          } catch { case err: BelleThrowable => errors += "in " + o + " " + err + "\n"; None }
          if (BelleExpr.DEBUG) println("ChooseSome: try " + o + " got " + someResult)
          (someResult, e) match {
            case (Some(BelleProvable(p, _)), _) /*if p.isProved*/ => return someResult.get
            case (Some(_), x: PartialTactic) => return someResult.get
            case (Some(_), _) => errors += "option " + o + " " + new BelleThrowable("Tactics must close their proof unless declared as partial. Use \"t partial\" instead of \"t\".").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o) + "\n" // throw new BelleThrowable("Non-partials must close proof.").inContext(ChooseSome(options, e), "Failed option in ChooseSome: " + o)
            case (None, _) => // option o had an error, so consider next option
          }
        }
        throw new BelleThrowable("ChooseSome did not succeed with any of its options").inContext(ChooseSome(options, e), "Failed all options in ChooseSome: " + options() + "\n" + errors)

      // look into tactics
      case d: DependentTactic if level > 0 || d.name == "ANON" => try {
        val v = branches(branch)._2
        val valueDependentTactic = d.computeExpr(v)
        val levelDecrement = if (d.name == "ANON") 0 else 1
        runTactic(branches.updated(branch, (valueDependentTactic, branches(branch)._2)), branch, level-levelDecrement)
      } catch {
        case e: BelleThrowable => throw e.inContext(d, branches(branch)._2.prettyString)
        //@todo unable to create is a serious error in the tactic not just an "oops whatever try something else exception"
        case e: Throwable => throw new BelleThrowable("Unable to create dependent tactic", e).inContext(d, "")
      }

      // forward to inner interpreter
      case _ => branches(branch)._2 match {
        case BelleProvable(provable, labels) if provable.subgoals.isEmpty=> inner(Seq())(branches(branch)._1, branches(branch)._2)
        case BelleProvable(provable, labels) if provable.subgoals.nonEmpty =>
          inner(listeners(branches(branch)._1.prettyString, branch))(branches(branch)._1, BelleProvable(provable.sub(0), labels)) match {
            case BelleProvable(innerProvable, _) => BelleProvable(provable(innerProvable, 0), labels)
          }
      }
    }
  }
}