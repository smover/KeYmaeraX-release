package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{ConstructionTactic, Tactic, PositionTactic}
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.{AndRightT, diffCutT,
  alphaRenamingT, boxNDetAssign, skolemizeT, boxTestT, ImplyRightT}
import Tactics.NilT
import AlphaConversionHelper._

import scala.collection.immutable.List

/**
 * Created by smitsch on 1/9/15.
 * @author Stefan Mitsch
 */
object ODETactics {

  /**
   * Returns a tactic to use the solution of an ODE as a differential invariant.
   * @param solution The solution. If None, the tactic uses Mathematica to find a solution.
   * @return The tactic.
   */
  def diffSolution(solution: Option[Formula]): PositionTactic = new PositionTactic("differential solution") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && (s(p) match {
      case BoxModality(_: NFContEvolve, _) => true
      case BoxModality(_: ContEvolveProduct, _) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new Tactic("") {
      def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      def apply(tool: Tool, node: ProofNode) = {
        val t = constructTactic(p)
        t.scheduler = Tactics.MathematicaScheduler
        t.continuation = continuation
        t.dispatch(this, node)
      }
    }

    private def constructTactic(p: Position) = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        import BranchLabels.{cutShowLbl, cutUseLbl}
        def createTactic(solution: Formula, diffEqPos: Position) = {
          val cut = diffCutT(solution)(p) & AndRightT(p)
          val proveSol = onBranch(cutShowLbl, NilT /*differentialInduction(diffEqPos)*/)
          val useSol = onBranch(cutUseLbl, diffWeakenT(diffEqPos))
          Some(cut ~ proveSol ~ useSol)
        }

        // HACK assumes presence of variable t and variables for starting values
        // TODO ghost time
        // TODO ghosts for starting values
        val diffEq: Either[NFContEvolve, ContEvolveProduct] = node.sequent(p) match {
          case BoxModality(e: NFContEvolve, _) => Left(e)
          case BoxModality(e: ContEvolveProduct, _) => Right(e)
          case _ => ???
        }

        var actualTime: Variable = null
        ExpressionTraversal.traverse(new ExpressionTraversalFunction {

          import ExpressionTraversal.stop

          override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
            case v@Variable(n, _, _) if n == "t" => actualTime = v.asInstanceOf[Variable]; Left(Some(stop))
            case _ => Left(None)
          }
        }, node.sequent(p))

        val theSolution = solution match {
          case sol@Some(_) => sol
          case None => tool match {
            case x: Mathematica if diffEq.isLeft => x.diffSolver.diffSol(diffEq.left.get, actualTime)
            case x: Mathematica if diffEq.isRight => x.diffSolver.diffSol(diffEq.right.get, actualTime)
            case _ => ???
          }
        }

        val diffEqPos = SuccPosition(p.index)
        theSolution match {
          case Some(s) => createTactic(s, diffEqPos)
          case None => ???
        }
      }
    }
  }

  /**
   * Returns the differential weaken tactic.
   * @return The tactic.
   */
  def diffWeakenT: PositionTactic = new PositionTactic("DW differential weaken system") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && (s(p) match {
      case BoxModality(_: ContEvolveProduct, _) => true
      case BoxModality(_: NFContEvolve, _) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        import scala.language.postfixOps
        node.sequent(p) match {
          case BoxModality(_: ContEvolveProduct, _) => Some(
            // introduce $$ markers
            diffWeakenSystemIntroT(p) &
              // pull out heads until empty
              ((diffWeakenSystemHeadT(p) & boxNDetAssign(p) & skolemizeT(p)) *) &
              // remove empty marker and handle tests
              diffWeakenSystemNilT(p) & ((boxTestT(p) & ImplyRightT(p)) *)
          )
        }
      }
    }
  }

  /**
   * Returns a tactic to introduce a marker around an ODE for differential weakening.
   * @return The tactic.
   */
  def diffWeakenSystemIntroT: PositionTactic = new AxiomTactic("DW differential weaken system introduce",
    "DW differential weaken system introduce") {
    def applies(f: Formula) = f match {
      case BoxModality(ContEvolveProduct(_, _), _) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && super.applies(s, p)

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(c: ContEvolveProduct, p) =>
        // construct instance
        val g = BoxModality(IncompleteSystem(c), p)
        val axiomInstance = Imply(g, f)

        // construct substitution
        val aP = PredicateConstant("p")
        val aC = ContEvolveProgramConstant("c")
        val l = List(new SubstitutionPair(aP, p), new SubstitutionPair(aC, c))

        Some(ax, axiomInstance, Substitution(l), None)
      case _ => None
    }
  }

  /**
   * Returns a tactic to pull out an ODE from a marked system of differential equations, and to convert
   * that ODE into a nondeterministic assignment and a test of its evolution domain constraint.
   * @return The tactic.
   */
  def diffWeakenSystemHeadT: PositionTactic = new AxiomTactic("DW differential weaken system head",
    "DW differential weaken system head") {
    def applies(f: Formula) = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(NFContEvolve(_, d: Derivative, t, h), _)), _) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && super.applies(s, p)

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(NFContEvolve(_, d: Derivative, t, h), c)), p) =>
        // construct instance
        val x = d.child match {
          case v: Variable => v
          case _ => throw new IllegalArgumentException("Normal form expects v in v' being a Variable")
        }
        val lhs = BoxModality(NDetAssign(x), BoxModality(IncompleteSystem(c), BoxModality(Test(h), p)))
        val axiomInstance = Imply(lhs, f)

        // construct substitution
        val aX = Variable("x", None, Real)
        val aH = ApplyPredicate(Function("H", None, Real, Bool), CDot)
        val aP = ApplyPredicate(Function("p", None, Real, Bool), CDot)
        val aT = Apply(Function("f", None, Real, Real), CDot)
        val aC = ContEvolveProgramConstant("c")
        import Substitution.maybeFreeVariables
        val l = List(new SubstitutionPair(aH, replaceFree(h)(x, CDot)), new SubstitutionPair(aP, replaceFree(p)(x, CDot)),
                     new SubstitutionPair(aT, replaceFree(t)(x, CDot, Some(maybeFreeVariables(t)))), new SubstitutionPair(aC, c))

        // alpha renaming of x if necessary
        val (axiom, cont) =
          if (x.name != aX.name || x.index != None) (replaceFree(ax)(aX, x), Some(alphaInWeakenSystems(x, aX)))
          else (ax, None)

        Some(axiom, axiomInstance, Substitution(l), cont)
      case _ => None
    }
  }

  /**
   * Returns a tactic to weaken a system of differential equations where only the empty marker $$ remained (i.e., all
   * ODEs are already converted into nondeterministic assignments and tests of the evolution domain constraint).
   * @return The tactic.
   */
  def diffWeakenSystemNilT: PositionTactic = new AxiomTactic("DW differential weaken system nil",
    "DW differential weaken system nil") {
    def applies(f: Formula) = f match {
      case BoxModality(IncompleteSystem(_: EmptyContEvolveProgram), _) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && super.applies(s, p)

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(IncompleteSystem(_: EmptyContEvolveProgram), BoxModality(b@Test(h), p)) =>
        // construct instance
        val lhs = BoxModality(b, p)
        val axiomInstance = Imply(lhs, f)

        // construct substitution
        val aP = PredicateConstant("p")
        val aH = PredicateConstant("H")
        val l = List(new SubstitutionPair(aP, p), new SubstitutionPair(aH, h))

        Some(ax, axiomInstance, Substitution(l), None)
      case _ => None
    }
  }

  /**
   * Creates an alpha renaming tactic that fits the structure of weakening systems. The tactic renames the old symbol
   * to the new symbol.
   * @param oldSymbol The old symbol.
   * @param newSymbol The new symbol.
   * @return The alpha renaming tactic.
   */
  private def alphaInWeakenSystems(oldSymbol: NamedSymbol, newSymbol: NamedSymbol) = new PositionTactic("Alpha") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Imply(BoxModality(_: NDetAssign, _), BoxModality(_: ContEvolveProgram, _)) => true
      case Imply(BoxModality(_: NDetAssign, _), BoxModality(_: IncompleteSystem, _)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
        Some(alphaRenamingT(oldSymbol.name, oldSymbol.index, newSymbol.name, None)(p.first)
          & alphaRenamingT(oldSymbol.name, oldSymbol.index, newSymbol.name, None)(p.second))

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section DI.1: Systems of differential equations.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  @deprecated("Unsound", "Jan 2015")
  def diffInvariantSystemIntroduction: PositionTactic = new AxiomTactic("DI System Introduction", "DI System Introduction") {
    //@todo I think this always has to be a contevolveproduct because otherwise we would not be handling a system.
    def applies(f: Formula) = f match {
      case BoxModality(ContEvolveProduct(NFContEvolve(_, d: Derivative, t, h), lhs), _) => !lhs.isInstanceOf[EmptyContEvolveProgram]
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && super.applies(s, p)

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(c: ContEvolveProduct, p) =>
        val g = BoxModality(IncompleteSystem(c), p)
        val axiomInstance = Imply(g, f)

        // construct substitution
        val aP = PredicateConstant("p")
        val aC = ContEvolveProgramConstant("c")
        val l = List(new SubstitutionPair(aP, p), new SubstitutionPair(aC, c))

        //@todo do we need to do the "rename x" thing here?
        Some(ax, axiomInstance, Substitution(l), None)
      case _ => None
    }
  }

  // Peel off a single equation of a system of differential equations and turn it into a derivative-assign-and-test.
  // Two versions, depending upon whether there is already a [?H;] at the end of the chain of box modalities.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  @deprecated("Unsound", "Jan 2015")
  def diffInvariantHeadEliminationWithTest: PositionTactic = new AxiomTactic("DI System Head Elimination (test)",
    "DI System Head Elimination (test)") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(NFContEvolve(sort, Derivative(_, Variable(_, _, _)), theta_x, h_x), c)), BoxModality(Test(h), p: Formula)) => {
        true
      }
      case _ => false
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(NFContEvolve(sort, dx: Derivative, theta_x, h_x), c)), BoxModality(Test(h), p: Formula)) =>
        val x = dx match {
          case Derivative(_, variable: Variable) => variable
          case _ => throw new Exception("Expected variable but didn't find one.")
        }

        val g = BoxModality(
          Assign(dx, theta_x),
          BoxModality(
            IncompleteSystem(c),
            BoxModality(
              Test(And(h, h_x)), //is this the correct order? Tests should happen in roughly the same order at last as at first.
              p
            )
          )
        )
        val axiomInstance = Imply(g, f)

        import Substitution.maybeFreeVariables
        //Original axiom: [ $$x' = f(x) & H(x), c; ][?H;]p <- [x' := f(x);] [c;][?H & H(x);]p
        //@todo it would be nice to factor this out these substitutions so that they can be tested in isolation from the rest of the tactics framework.
        // construct the substitution
        // variable substitution
        val aX = Variable("x", None, Real)
        // theta substitution @todo this seems fishy; where is the x in f(x)?
        val aTheta = Apply(Function("f", None, Real, Real), CDot)
        val theta_cdot = replaceFree(theta_x)(x, CDot, Some(maybeFreeVariables(theta_x)))
      val thetaSubstitution = new SubstitutionPair(aTheta, theta_cdot)
        // x' constraint substitution
        val aH_x = ApplyPredicate(Function("H", None, Real, Bool), CDot)
        val h_cdot = replaceFree(h_x)(x, CDot, Some(maybeFreeVariables(h_x)))
        val xConstraintSubstitution = new SubstitutionPair(aH_x, h_cdot)
        // remaining system substitution
        val aSystem = ContEvolveProgramConstant("c", None)
        val systemSubstitution = new SubstitutionPair(aSystem, c)
        // existing test substitution
        val aH = PredicateConstant("H", None)
        val constraintSubstitution = new SubstitutionPair(aH, h)
        // post-condition substitution
        val aP = PredicateConstant("p")
        val predicateSubst = new SubstitutionPair(aP, p)

        val l = thetaSubstitution ::
          xConstraintSubstitution ::
          systemSubstitution ::
          constraintSubstitution ::
          predicateSubst ::
          Nil

        // alpha renaming of x if necessary
        val (axiom, cont) =
          if (x.name != aX.name || x.index != None) (replaceFree(ax)(aX, x), Some(alphaInWeakenSystems(x, aX)))
          else (ax, None)

        Some(axiom, axiomInstance, Substitution(l), cont)
      case _ => None
    }
  }
  @deprecated("Unsound", "Jan 2015")
  def diffInvariantHeadEliminationNoTest: PositionTactic = new AxiomTactic("DI System Head Elimination (no test)",
    "DI System Head Elimination (no test)") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(NFContEvolve(sort, Derivative(_, Variable(_, _, _)), theta_x, h_x), c)), p: Formula) => {
        p match {
          case BoxModality(Test(h),_) => false
          case _ => true
        }
      }
      case _ => false
    }
    @deprecated("Unsound", "Jan 2015")
    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(NFContEvolve(sort, dx: Derivative, theta_x, h_x), c)), p: Formula) =>
        val x = dx match {
          case Derivative(_, variable: Variable) => variable
          case _ => throw new Exception("Expected variable but didn't find one.")
        }

        val g = BoxModality(
          Assign(dx, theta_x),
          BoxModality(
            IncompleteSystem(c),
            BoxModality(Test(h_x), p)
          )
        )
        val axiomInstance = Imply(g, f)

        //@todo it would be nice to factor this out these substitutions so that they can be tested in isolation from the rest of the tactics framework.
        // construct the substitution
        // variable substitution
        val aX = Variable("x", None, Real)
        // theta substitution @todo this seems fishy; where is the x in f(x)?
        val aTheta = Apply(Function("f", None, Real, Real), CDot)
        import Substitution.maybeFreeVariables
        val theta_cdot = replaceFree(theta_x)(x, CDot, Some(maybeFreeVariables(theta_x)))
      val thetaSubstitution = new SubstitutionPair(aTheta, theta_cdot)
        // x' constraint substitution
        val aH_x = ApplyPredicate(Function("H", None, Real, Bool), CDot)
        val h_cdot = replaceFree(h_x)(x, CDot, Some(maybeFreeVariables(h_x)))
        val xConstraintSubstitution = new SubstitutionPair(aH_x, h_cdot)
        // remaining system substitution
        val aSystem = ContEvolveProgramConstant("c", None)
        val systemSubstitution = new SubstitutionPair(aSystem, c)
        // post-condition substitution
        val aP = PredicateConstant("p")
        val predicateSubst = new SubstitutionPair(aP, p)

        val l = thetaSubstitution ::
          xConstraintSubstitution ::
          systemSubstitution ::
          predicateSubst ::
          Nil

        // alpha renaming of x if necessary
        val (axiom, cont) =
          if (x.name != aX.name || x.index != None) (replaceFree(ax)(aX, x), Some(alphaInWeakenSystems(x, aX)))
          else (ax, None)

        Some(axiom, axiomInstance, Substitution(l), cont)
      case _ => None
    }
  }

  // Eliminate an empty system.
  // @todo this should additionally compute the derivative of the formula p.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  @deprecated("Unsound", "Jan 2015")
  def diffInvariantNilElimination: PositionTactic = new AxiomTactic("DI System Nil Elimination", "DI System Nil Elimination") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(empty:EmptyContEvolveProgram, BoxModality(Test(h), p)) => true
      case _ => false
    }

    //[[$$$$;]][?H;]p <- [?H;]p'
    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(empty:EmptyContEvolveProgram, BoxModality(Test(h), p)) => {
        val g = BoxModality(Test(h), p)
        val axiomInstance = Imply(g, f)

        val aH = PredicateConstant("H")
        val aP = PredicateConstant("P")
        val subst = Substitution(
          new SubstitutionPair(aH, h) ::
            new SubstitutionPair(aP, FormulaDerivative(p)) :: Nil
        )

        Some(ax, axiomInstance, subst, None)
      }
      case _ => None
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section DI.2: Differential invariant for normal forms.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   * Returns the differential invariant tactic for a single normal form ODE.
   * @return The tactic.
   */
  @deprecated("Unsound", "Jan 2015")
  def diffInvariantNormalFormT: PositionTactic = new AxiomTactic("DI differential invariant", "DI differential invariant") {
    def applies(f: Formula) = {
      f match {
        case BoxModality(ContEvolveProduct(_: NFContEvolve, e:EmptyContEvolveProgram),_) => true
        case _ => false
      }
    }
    override def applies(s: Sequent, p: Position): Boolean = {
      val isntAnte = !p.isAnte
      val isInExpr = p.inExpr == HereP
      val superApplies = super.applies(s,p)
      isntAnte && isInExpr && superApplies
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(ContEvolveProduct(NFContEvolve(_, d: Derivative, t, h), empty:EmptyContEvolveProgram), p) => {
        // construct instance
        val x = d.child match {
          case v: Variable => v
          case _ => throw new IllegalArgumentException("Normal form expects primes of variables, not of entire terms.")
        }
        // [x'=t&H;]p <- ([x'=t&H;](H->[x':=t;](p')))
        val g = BoxModality(
          ContEvolveProduct(NFContEvolve(Nil, Derivative(Real,x), t, h),empty:EmptyContEvolveProgram),
          Imply(
            h,
            BoxModality(
              Assign(Derivative(Real,x), t),
              FormulaDerivative(p)
            )
          )
        )
        val axiomInstance = Imply(g, f)


        // construct substitution
        // [x'=t&H;]p <- ([x'=t&H;](H->[x':=t;](p')))
        val aX = Variable("x", None, Real)
        val aH = PredicateConstant("H", None)
        val aP = PredicateConstant("p", None)
        val aT = Variable("t", None, Real)
        val l = List(new SubstitutionPair(aH, h), new SubstitutionPair(aP, p), new SubstitutionPair(aT, t))

        val (axiom, cont) =
          if (x.name != aX.name || x.index != None) (replaceFree(ax)(aX, x), Some(alphaInWeakenSystems(x, aX)))
          else (ax, None)

        Some(axiom, axiomInstance, Substitution(l), cont)
      }
      case _ => None
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section DI.3: General DI.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   * Returns the differential weaken tactic.
   * @return The tactic.
   */
  @deprecated("Unsound", "Jan 2015")
  def diffInvariantT: PositionTactic = new PositionTactic("DI Differential Invariant General Rule") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && (s(p) match {
      case BoxModality(_: ContEvolveProduct, _) => true
      case BoxModality(_: NFContEvolve, _) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        import scala.language.postfixOps
        node.sequent(p) match {
          case BoxModality(_: ContEvolveProduct, _) => Some(
            // introduce $$ markers
            diffInvariantSystemIntroduction(p) &
              // pull out heads until empty
              ( ((diffInvariantHeadEliminationWithTest(p) & boxNDetAssign(p) & skolemizeT(p)) | (diffInvariantHeadEliminationNoTest(p) & boxNDetAssign(p) & skolemizeT(p)))* ) &
            // remove empty marker and handle tests
              //@todo this isn't actually correct; the next thing should do assign after the nilelim.
              diffInvariantNilElimination(p) & ((boxTestT(p) & ImplyRightT(p)) *)
          )
        }
      }
    }
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Differential Invariants Section
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  /*
    Axiom "DI System Marker Intro".
      [c;]p <- p & [$$c$$;]p'
    End.
  */
  def diffInvSystemIntro = new AxiomTactic("DI System Marker Intro", "DI System Marker Intro") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(ContEvolveProduct(_, _), _) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(c: ContEvolveProduct, p) => {
        //[c]p <- p & [{c}]p'

        //construct instance
        val g = BoxModality(
          IncompleteSystem(c), FormulaDerivative(p)
        )
        val axiomInstance = Imply(f, g)

        //construct substitution.
        val aC = ContEvolveProgramConstant("c")
        val aP = PredicateConstant("p")
        val subst = Substitution(List(
          new SubstitutionPair(aC, c),
          new SubstitutionPair(aP, p)
        ))

        Some(ax, axiomInstance, subst, None)
      }
      case _ => None
    }
  }

  /*
    Axiom "DI System Head No Test".
      [$$x'=f(x), c$$;]p(x) <- [$$c, x'$=$f(x)$$;][x' := f(x);]p(x)
    End.
  */
  def diffInvSystemHeadNoTest = new AxiomTactic("DI System Head No Test", "DI System Head No Test") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(ContEvolve(Equals(_,Derivative(Real, x:Variable), t:Term)), _))) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(ContEvolve(Equals(sort:Sort, Derivative(Real, x:Variable), t:Term)), c:ContEvolveProgram)), p:Formula) => {
        //construct instance
        val g = BoxModality(
          ContEvolve(Equals(sort,Derivative(Real,x),t)),
          BoxModality(
            IncompleteSystem(ContEvolveProduct(c, ContEvolve(Equals(sort,Derivative(Real,x),t)))),
            BoxModality(Assign(Derivative(Real,x), t), p)
          )
        )
        val instance = Imply(f,g)

        //construct substitution
        import Substitution.maybeFreeVariables
        val aX = Variable("x", None, Real)

        val aT = Apply(Function("f", None, Real, Real), CDot)
        val t_cdot = replaceFree(t)(x, CDot, Some(maybeFreeVariables(t)))

        val aC = ContEvolveProgramConstant("c")

        val aP = PredicateConstant("p")

        val subst = Substitution(List(
          new SubstitutionPair(aT, t_cdot),
          new SubstitutionPair(aC,c),
          new SubstitutionPair(aP, p)
        ))

        val (axiom, cont) =
          if (x.name != aX.name || x.index != None) (replaceFree(ax)(aX, x), Some(alphaInWeakenSystems(x, aX)))
          else (ax, None)

        Some(axiom, instance, subst, cont)
      }
      case _ => None
    }
  }

  /*
    Axiom "DI System Head Test".
      [$$x'=f(x) & H(x), c$$;]p(x) <- [$$c, x'$=$f(x)$$;][x' := f(x);](H(x) -> p(x))
    End.
   */
  def diffInvSystemHeadTest = new AxiomTactic("DI System Head Test", "DI System Head Test") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(NFContEvolve(_,Derivative(Real, v:Variable),_,_),_)), _) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(NFContEvolve(bound,Derivative(Real,x:Variable),t,h), c)), p) => {
        //construct instance
        val g = BoxModality(
          NFContEvolve(bound, Derivative(Real,x), t, h),
          BoxModality(
            IncompleteSystem(ContEvolveProduct(c, CheckedContEvolveFragment(NFContEvolve(bound, Derivative(Real,x), t, h)))),
            Imply(h, BoxModality(Assign(Derivative(Real,x), t), p))
          )
        )
        val instance = Imply(f,g)

        //construct substitution
        import Substitution.maybeFreeVariables
        val aX = Variable("x", None, Real)

        val aT = Apply(Function("f", None, Real, Real), CDot)
        val t_cdot = replaceFree(t)(x, CDot, Some(maybeFreeVariables(t)))

        val aH = ApplyPredicate(Function("H", None, Real, Bool), CDot)
        val h_cdot = replaceFree(h)(x, CDot, Some(maybeFreeVariables(h)))

        val aC = ContEvolveProgramConstant("c")

        val aP = PredicateConstant("p")

        val subst = Substitution(List(
          new SubstitutionPair(aT, t_cdot),
          new SubstitutionPair(aH, h_cdot),
          new SubstitutionPair(aC,c),
          new SubstitutionPair(aP, p)
        ))

        val (axiom, cont) =
          if (x.name != aX.name || x.index != None) (replaceFree(ax)(aX, x), Some(alphaInWeakenSystems(x, aX)))
          else (ax, None)

        Some(axiom, instance, subst, cont)
      }
      case _ => None
    }
  }

  /*
    Axiom "DI System Complete".
      [$$x' $=$ e, c$$;]p <- p
    End.
  */
  def diffInvSystemTail = new AxiomTactic("DI differential system tail", "DI differential system tail") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(CheckedContEvolveFragment(_),_)), _) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(IncompleteSystem(ContEvolveProduct(CheckedContEvolveFragment(_), _)), p) => {
        //construct instance
        val axiomInstance = Imply(f, p)

        //construct substitution.
        val aP = PredicateConstant("p")
        val subst = Substitution(List(
          new SubstitutionPair(aP, p)
        ))

        Some(ax, axiomInstance, subst, None)
      }
      case _ => None
    }
  }
}


