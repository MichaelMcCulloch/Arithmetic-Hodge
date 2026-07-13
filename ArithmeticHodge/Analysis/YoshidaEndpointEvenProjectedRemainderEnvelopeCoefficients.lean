import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeMoments

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeCoefficients

open YoshidaConstantBounds
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenProjectedRemainderEnvelopeMoments
open YoshidaEndpointEvenProjectedRemainderEnvelopePolynomials
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound

noncomputable section

private abbrev A : ℝ := yoshidaEndpointA
private abbrev C0 : ℝ := yoshidaEndpointCoshMoment centeredEvenP0
private abbrev C2 : ℝ := yoshidaEndpointCoshMoment centeredEvenP2

/-- Constant coefficient of the constant-basis shifted envelope. -/
def projectedEnvelopeD00 : ℝ :=
  -883 / 480 - A / 2 + A ^ 2 / 48 + A ^ 3 / 48 -
    7 * A ^ 4 / 23040 - A ^ 5 / 768 +
    31 * A ^ 6 / 5806080 + 61 * A ^ 7 / 645120 + 2 * A * C0

/-- Quadratic coefficient of the constant-basis shifted envelope. -/
def projectedEnvelopeD01 : ℝ :=
  -35 / 32 + A ^ 2 / 48 + A ^ 3 / 16 -
    7 * A ^ 4 / 3840 - 5 * A ^ 5 / 384 +
    31 * A ^ 6 / 387072 + 61 * A ^ 7 / 30720 + A ^ 3 * C0 / 4

/-- Quartic coefficient of the constant-basis shifted envelope. -/
def projectedEnvelopeD02 : ℝ :=
  -7 * A ^ 4 / 23040 - 5 * A ^ 5 / 768 +
    31 * A ^ 6 / 387072 + 61 * A ^ 7 / 18432 + A ^ 5 * C0 / 192

/-- Sextic coefficient of the constant-basis shifted envelope. -/
def projectedEnvelopeD03 : ℝ :=
  31 * A ^ 6 / 5806080 + 61 * A ^ 7 / 92160 + A ^ 7 * C0 / 23040

/-- Constant coefficient of the degree-two-basis shifted envelope. -/
def projectedEnvelopeD20 : ℝ :=
  107 / 240 + A ^ 2 / 192 + A ^ 3 / 120 -
    7 * A ^ 4 / 46080 - A ^ 5 / 1344 +
    31 * A ^ 6 / 9289728 + 61 * A ^ 7 / 967680 + 2 * A * C2

/-- Quadratic coefficient of the degree-two-basis shifted envelope. -/
def projectedEnvelopeD21 : ℝ :=
  -71 / 40 - A ^ 2 / 96 - 7 * A ^ 4 / 15360 - A ^ 5 / 192 +
    31 * A ^ 6 / 774144 + 61 * A ^ 7 / 53760 + A ^ 3 * C2 / 4

/-- Quartic coefficient of the degree-two-basis shifted envelope. -/
def projectedEnvelopeD22 : ℝ :=
  A ^ 2 / 192 + 7 * A ^ 4 / 46080 +
    31 * A ^ 6 / 1548288 + 61 * A ^ 7 / 46080 + A ^ 5 * C2 / 192

/-- Sextic coefficient of the degree-two-basis shifted envelope. -/
def projectedEnvelopeD23 : ℝ :=
  -7 * A ^ 4 / 230400 - 31 * A ^ 6 / 11612160 + A ^ 7 * C2 / 23040

/-- Octic coefficient of the degree-two-basis shifted envelope. -/
def projectedEnvelopeD24 : ℝ := 31 * A ^ 6 / 108380160

/-- Coefficient presentation of the constant-basis polynomial envelope. -/
def shiftedRemainderPolynomial6_0_explicit (x : ℝ) : ℝ :=
  projectedEnvelopeD00 + projectedEnvelopeD01 * x ^ 2 +
    projectedEnvelopeD02 * x ^ 4 + projectedEnvelopeD03 * x ^ 6

/-- Coefficient presentation of the degree-two-basis polynomial envelope. -/
def shiftedRemainderPolynomial6_2_explicit (x : ℝ) : ℝ :=
  projectedEnvelopeD20 + projectedEnvelopeD21 * x ^ 2 +
    projectedEnvelopeD22 * x ^ 4 + projectedEnvelopeD23 * x ^ 6 +
    projectedEnvelopeD24 * x ^ 8

/-- The integral-defined constant envelope has the displayed four
coefficients on the endpoint interval. -/
theorem fixedProjectedShiftedRemainderPolynomial6_0_eq_explicit
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    fixedProjectedShiftedRemainderPolynomial6_0 x =
      shiftedRemainderPolynomial6_0_explicit x := by
  unfold fixedProjectedShiftedRemainderPolynomial6_0
    fixedProjectedSmoothRemainderPolynomial6_0
  rw [regularRepresenterPolynomial6_p0_eq hx]
  unfold shiftedRemainderPolynomial6_0_explicit projectedEnvelopeD00
    projectedEnvelopeD01 projectedEnvelopeD02 projectedEnvelopeD03
    regularRepresenterPolynomial6_0_explicit yoshidaEndpointCoshPolynomial6
  dsimp only [C0, A]
  ring

/-- The integral-defined degree-two envelope has the displayed five
coefficients on the endpoint interval. -/
theorem fixedProjectedShiftedRemainderPolynomial6_2_eq_explicit
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    fixedProjectedShiftedRemainderPolynomial6_2 x =
      shiftedRemainderPolynomial6_2_explicit x := by
  unfold fixedProjectedShiftedRemainderPolynomial6_2
    fixedProjectedSmoothRemainderPolynomial6_2
  rw [regularRepresenterPolynomial6_p2_eq hx]
  unfold shiftedRemainderPolynomial6_2_explicit projectedEnvelopeD20
    projectedEnvelopeD21 projectedEnvelopeD22 projectedEnvelopeD23
    projectedEnvelopeD24 regularRepresenterPolynomial6_2_explicit
    yoshidaEndpointCoshPolynomial6
  dsimp only [C2, A]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeCoefficients
