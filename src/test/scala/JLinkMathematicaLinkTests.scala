import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tools.JLinkMathematicaLink
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter._

/**
 * Tests the JLink Mathematica implementation.
 * @author Stefan Mitsch
 */
class JLinkMathematicaLinkTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  private var link: JLinkMathematicaLink = null

  private val x = Variable("x", None, Real)
  private val y = Variable("y", None, Real)
  private val z = Variable("z", None, Real)
  private val t = Variable("t", None, Real)
  private val x0 = Function("x0", None, Unit, Real)
  private val y0 = Function("y0", None, Unit, Real)
  private val one = Number(BigDecimal(1))

  override def beforeEach() = {
    link = new JLinkMathematicaLink
    link.init("/Applications/Mathematica.app/Contents/MacOS/MathKernel", None)
  }

  override def afterEach() = {
    link.shutdown()
    link = null
  }

  "x'=1" should "x=x0+y*t with AtomicODE" in {
    val eq = AtomicODE(Derivative(Real, x), one)
    val expected = Some("x=1*t+x0()".asFormula)
    link.diffSol(eq, t,  Map(x->x0)) should be (expected)
  }

  "x'=y, y'=z" should "y=y0+z*t and x=x0+y0*t+z/2*t^2 with ContProduct" in {
    val eq = ODEProduct(
      AtomicODE(Derivative(Real, x), y),
      AtomicODE(Derivative(Real, y), z))
    val expected = Some("x=1/2*(t^2*z + 2*x0() + 2*t*y0()) & y=t*z + y0()".asFormula)
    link.diffSol(eq, t, Map(x->x0, y->y0)) should be (expected)
  }

  "x'=y, t'=1" should "x=x0+y*t with ContProduct" in {
    // special treatment of t for now
    val eq = ODEProduct(
      AtomicODE(Derivative(Real, x), y),
      AtomicODE(Derivative(Real, t), one))
    val expected = Some("x=t*y+x0()".asFormula)
    link.diffSol(eq, t, Map(x->x0)) should be (expected)
  }
}
