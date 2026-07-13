import ArithmeticHodge.Analysis.YoshidaEndpointEvenTailRepresenter

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedDualIdentity

open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound

noncomputable section

/-!
# Exact extraction of the endpoint potential from the projected dual square

The fixed rational projection is close to the weighted orthogonal projection,
but its role here is entirely algebraic.  After expanding a projected low-tail
representer as `V p + h`, division by `W = 41/60 + V` leaves one square whose
numerator contains only the bounded regular, hyperbolic, and polynomial terms.
-/

/-- Fixed rational representative of the constant low-tail functional. -/
def fixedProjectedTailRepresenter0 : ℝ → ℝ :=
  yoshidaEndpointEvenProjectedTailRepresenter0 (73 / 48) (35 / 48)

/-- Fixed rational representative of the degree-two low-tail functional. -/
def fixedProjectedTailRepresenter2 : ℝ → ℝ :=
  yoshidaEndpointEvenProjectedTailRepresenter2 (7 / 48) (1 / 2)

/-- The low profile represented by coefficients `(c,b)`. -/
def fixedEvenLowProfile (c b x : ℝ) : ℝ :=
  c * centeredEvenP0 x + b * centeredEvenP2 x

/-- The polynomial removed from the two raw representers. -/
def fixedProjectionPolynomial (c b x : ℝ) : ℝ :=
  c * ((73 / 48 : ℝ) * centeredEvenP0 x +
      (35 / 48 : ℝ) * centeredEvenP2 x) +
    b * ((7 / 48 : ℝ) * centeredEvenP0 x +
      (1 / 2 : ℝ) * centeredEvenP2 x)

/-- Everything in the projected representer except the singular endpoint
potential factor.  This term is bounded on the closed endpoint interval. -/
def fixedProjectedBoundedRemainder (c b x : ℝ) : ℝ :=
  -yoshidaEndpointA *
      (c * yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x +
        b * yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x) +
    2 * yoshidaEndpointA *
      (c * yoshidaEndpointCoshMoment centeredEvenP0 +
        b * yoshidaEndpointCoshMoment centeredEvenP2) *
      Real.cosh (yoshidaEndpointA * x / 2) -
    fixedProjectionPolynomial c b x

/-- The bounded numerator left after division by `W = 41/60 + V`. -/
def fixedProjectedShiftedRemainder (c b x : ℝ) : ℝ :=
  fixedProjectedBoundedRemainder c b x -
    (41 / 60 : ℝ) * fixedEvenLowProfile c b x

theorem fixedProjectedTailRepresenter_linear (c b x : ℝ) :
    c * fixedProjectedTailRepresenter0 x +
        b * fixedProjectedTailRepresenter2 x =
      yoshidaEndpointPotential x * fixedEvenLowProfile c b x +
        fixedProjectedBoundedRemainder c b x := by
  unfold fixedProjectedTailRepresenter0 fixedProjectedTailRepresenter2
    yoshidaEndpointEvenProjectedTailRepresenter0
    yoshidaEndpointEvenProjectedTailRepresenter2
    yoshidaEndpointEvenProjectedTailRepresenter
    yoshidaEndpointEvenTailRepresenter
    fixedEvenLowProfile fixedProjectedBoundedRemainder
    fixedProjectionPolynomial
  ring

private theorem sq_div_add_decomposition
    (V d p h : ℝ) (hne : d + V ≠ 0) :
    (V * p + h) ^ 2 / (d + V) =
      V * p ^ 2 + 2 * p * h - d * p ^ 2 +
        (h - d * p) ^ 2 / (d + V) := by
  field_simp [hne]
  ring

theorem yoshidaEndpointEvenTailWeight_pos_on_Icc
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    0 < yoshidaEndpointEvenTailWeight x := by
  have hV := yoshidaEndpointPotential_nonneg_on_Icc hx
  unfold yoshidaEndpointEvenTailWeight
  linarith

/-- Pointwise exact division identity for the fixed projected dual square.
The only remaining quotient numerator is the bounded shifted remainder. -/
theorem fixedProjectedTailRepresenter_sq_div_weight
    (c b x : ℝ) (hx : x ∈ Icc (-1) 1) :
    (c * fixedProjectedTailRepresenter0 x +
        b * fixedProjectedTailRepresenter2 x) ^ 2 /
        yoshidaEndpointEvenTailWeight x =
      yoshidaEndpointPotential x * fixedEvenLowProfile c b x ^ 2 +
        2 * fixedEvenLowProfile c b x *
          fixedProjectedBoundedRemainder c b x -
        (41 / 60 : ℝ) * fixedEvenLowProfile c b x ^ 2 +
        fixedProjectedShiftedRemainder c b x ^ 2 /
          yoshidaEndpointEvenTailWeight x := by
  rw [fixedProjectedTailRepresenter_linear]
  have hne : (41 / 60 : ℝ) + yoshidaEndpointPotential x ≠ 0 := by
    have hpos := yoshidaEndpointEvenTailWeight_pos_on_Icc hx
    unfold yoshidaEndpointEvenTailWeight at hpos
    exact ne_of_gt hpos
  have h := sq_div_add_decomposition
    (yoshidaEndpointPotential x) (41 / 60 : ℝ)
      (fixedEvenLowProfile c b x)
      (fixedProjectedBoundedRemainder c b x) hne
  unfold yoshidaEndpointEvenTailWeight fixedProjectedShiftedRemainder
  exact h

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedDualIdentity
