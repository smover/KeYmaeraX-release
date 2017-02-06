/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._

import scala.annotation.switch

/**
 * Tactic indexing data structures for canonical proof strategies.
 * @author Stefan Mitsch
 * @see [[edu.cmu.cs.ls.keymaerax.btactics.AxiomInfo]]
 */
object TacticIndex {

  /** A list of things to do on a branch */
  type Branch = List[PositionLocator]

  /** Branch recursors (parent tactics may branch). */
  type Branches = List[Branch]

  /**
    * TacticIndex (recursors) where the recursors list resulting siblings for subsequent chase (every recursor is itself
    * a list, since tactics may branch).
    */
  type TacticIndex = List[(Sequent, SeqPos) => Branches]

  private def one(pos: PositionLocator): Branches = (pos::Nil) :: Nil

  /**
   * Return tactic index with list of recursors on other sibling, i.e., for chasing after the tactic is applied.
   */
  def tacticRecursors(tactic: PositionalTactic): TacticIndex = (tactic: @switch) match {
    //@note expected formulas are used to fall back to search
    case TactixLibrary.notL =>
      ((s: Sequent, p: SeqPos) => one(Fixed(SuccPosition.base0(s.succ.length), child(s(p))))) :: Nil
    case TactixLibrary.andL =>
      ((s: Sequent, p: SeqPos) => one(Fixed(AntePosition.base0(s.ante.length), right(s(p))))) ::
      ((s: Sequent, p: SeqPos) => one(Fixed(AntePosition.base0(s.ante.length-1), left(s(p))))) :: Nil
    case TactixLibrary.orL =>
      ((s: Sequent, p: SeqPos) => (new Fixed(p, left(s(p)))::Nil)::(new Fixed(p, right(s(p)))::Nil)::Nil) :: Nil
    case TactixLibrary.implyL =>
      ((s: Sequent, p: SeqPos) =>
        (Fixed(SuccPosition.base0(s.succ.length), left(s(p)))::Nil)::
        (new Fixed(p, right(s(p)))::Nil)::Nil) :: Nil
    case TactixLibrary.equivL =>
      ((s: Sequent, p: SeqPos) =>
        (new Fixed(p, Some(And(left(s(p)).get, right(s(p)).get)))::Nil)::
        (new Fixed(p, Some(And(Not(left(s(p)).get), Not(right(s(p)).get))))::Nil)::Nil) :: Nil
    case TactixLibrary.notR =>
      ((s: Sequent, p: SeqPos) => one(Fixed(AntePosition.base0(s.ante.length), child(s(p))))) :: Nil
    case TactixLibrary.implyR =>
      ((s: Sequent, p: SeqPos) => one(Fixed(AntePosition.base0(s.ante.length), left(s(p))))) ::
      ((s: Sequent, p: SeqPos) => one(Fixed(SuccPosition.base0(s.succ.length-1), right(s(p))))) :: Nil
    case TactixLibrary.orR =>
      ((s: Sequent, p: SeqPos) => one(Fixed(SuccPosition.base0(s.succ.length), right(s(p))))) ::
      ((s: Sequent, p: SeqPos) => one(Fixed(SuccPosition.base0(s.succ.length-1), left(s(p))))) :: Nil
    case TactixLibrary.andR =>
      ((s: Sequent, p: SeqPos) => (new Fixed(p, left(s(p)))::Nil)::(new Fixed(p, right(s(p)))::Nil)::Nil) :: Nil
    case TactixLibrary.equivR =>
      ((s: Sequent, p: SeqPos) =>
        (Fixed(AntePosition.base0(s.ante.length), left(s(p)))::Fixed(SuccPosition.base0(s.succ.length-1), right(s(p)))::Nil)::
        (Fixed(AntePosition.base0(s.ante.length), right(s(p)))::Fixed(SuccPosition.base0(s.succ.length-1), left(s(p)))::Nil)::Nil) :: Nil
    // default position: stop searching
    case _ => Nil
  }

  private def child(fml: Formula) = fml match { case f: UnaryCompositeFormula => Some(f.child) }
  private def left(fml: Formula) = fml match { case f: BinaryCompositeFormula => Some(f.left) }
  private def right(fml: Formula) = fml match { case f: BinaryCompositeFormula => Some(f.right) }

  // lookup canonical axioms for an expression (index)

  /** Give the first canonical (derived) axiom name or tactic name that simplifies the expression `expr`. */
  def tacticFor(expr: Expression, restrictTo: List[PositionalTactic]): (Option[PositionalTactic], Option[PositionalTactic]) = {
    val tactics = tacticsFor(expr)
    (tactics._1.intersect(restrictTo).headOption, tactics._2.intersect(restrictTo).headOption)
  }

  /** Return ordered list of all canonical tactic names that simplifies the expression `expr` (ante, succ). */
  def tacticsFor(expr: Expression): (List[PositionalTactic], List[PositionalTactic]) = {
    if (expr.kind == TermKind) expr match {
      case _ => (Nil, Nil)
    } else expr match {
      case Not(_) => (TactixLibrary.notL::Nil, TactixLibrary.notR::Nil)
      case And(_, _) => (TactixLibrary.andL::Nil, TactixLibrary.andR::Nil)
      case Or(_, _) => (TactixLibrary.orL::Nil, TactixLibrary.orR::Nil)
      case Imply(_, _) => (TactixLibrary.implyL::Nil, TactixLibrary.implyR::Nil)
      case Equiv(_, _) => (TactixLibrary.equivL::Nil, TactixLibrary.equivR::Nil)
      case _ => (Nil, Nil)
    }
  }

}
