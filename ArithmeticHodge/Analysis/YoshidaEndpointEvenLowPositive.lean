import ArithmeticHodge.Analysis.TwoByTwoSchur
import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowHyperbolic
import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowMatrixAlgebra
import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowProfile
import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowRegular
import ArithmeticHodge.Analysis.YoshidaEndpointEvenSharpScalar

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenLowPositive

open TwoByTwoSchur
open UnitIntervalLogEnergyAffine
open YoshidaConstantBounds
open YoshidaEndpointEvenLowHyperbolic
open YoshidaEndpointEvenLowMatrixAlgebra
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenLowRegular
open YoshidaEndpointEvenSharpScalar
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddSharpMassLoss
open YoshidaRegularKernelSchur

noncomputable section

def yoshidaEndpointEvenLowC0 : ℝ :=
  ∫ x : ℝ in -1..1, Real.cosh (yoshidaEndpointA * x / 2)

def yoshidaEndpointEvenLowC2 : ℝ :=
  ∫ x : ℝ in -1..1,
    Real.cosh (yoshidaEndpointA * x / 2) * centeredEvenP2 x

def yoshidaEndpointEvenLow00 : ℝ :=
  evenLow00 (Real.log 2) yoshidaEndpointEvenSharpMassLoss
    yoshidaEndpointEvenLowC0

def yoshidaEndpointEvenLow02 : ℝ :=
  evenLow02 (Real.log 2) yoshidaEndpointEvenLowC0 yoshidaEndpointEvenLowC2

def yoshidaEndpointEvenLow22 : ℝ :=
  evenLow22 (Real.log 2) yoshidaEndpointEvenSharpMassLoss
    yoshidaEndpointEvenLowC2

/-- The named fixed low Gram inherits the rational entry bounds and positive
determinant proved by the abstract low-matrix arithmetic. -/
theorem yoshidaEndpointEvenLow_matrix_bounds :
    (3563 / 10000 : ℝ) < yoshidaEndpointEvenLow00 ∧
      0 < yoshidaEndpointEvenLow02 ∧
      yoshidaEndpointEvenLow02 < (3391 / 10000 : ℝ) ∧
      (807 / 2500 : ℝ) < yoshidaEndpointEvenLow22 ∧
      0 < yoshidaEndpointEvenLow00 * yoshidaEndpointEvenLow22 -
        yoshidaEndpointEvenLow02 ^ 2 := by
  have h := low_matrix_bounds
    (Real.log 2) yoshidaEndpointEvenSharpMassLoss
      yoshidaEndpointEvenLowC0 yoshidaEndpointEvenLowC2
    strict_log_two_bounds.1 strict_log_two_bounds.2
    yoshidaEndpointEvenSharpMassLoss_lt_eight_hundred_fifty_four_div_six_hundred_twenty_five
    (by simpa only [yoshidaEndpointEvenLowC0] using
      ArithmeticHodge.Analysis.YoshidaEndpointEvenLowHyperbolic.two_hundred_one_div_hundred_lt_integral_yoshidaEndpoint_cosh)
    (by simpa only [yoshidaEndpointEvenLowC0] using
      integral_yoshidaEndpoint_cosh_lt_sixty_one_div_thirty)
    (by simpa only [yoshidaEndpointEvenLowC2] using
      integral_yoshidaEndpoint_cosh_mul_centeredEvenP2_pos)
    (by simpa only [yoshidaEndpointEvenLowC2] using
      integral_yoshidaEndpoint_cosh_mul_centeredEvenP2_lt_one_div_two_hundred_forty_five)
  simpa only [yoshidaEndpointEvenLow00, yoshidaEndpointEvenLow02,
    yoshidaEndpointEvenLow22] using h

/-- The explicit fixed low Gram is a lower bound for the complete clean
quadratic on every `c P₀ + b P₂`. -/
theorem yoshidaEndpointEvenLow_quadratic_le_clean (c b : ℝ) :
    yoshidaEndpointEvenLow00 * c ^ 2 +
        2 * yoshidaEndpointEvenLow02 * c * b +
        yoshidaEndpointEvenLow22 * b ^ 2 ≤
      yoshidaEndpointOddCleanQuadratic
        (yoshidaEndpointEvenLowProfile c b) := by
  have hlog := centeredRawLogEnergy_yoshidaEndpointEvenLowProfile c b
  have hpotential :=
    integral_endpointPotential_mul_yoshidaEndpointEvenLowProfile_sq c b
  have hmass := integral_yoshidaEndpointEvenLowProfile_sq c b
  have hregular :=
    yoshidaEndpointRegularQuadratic_one_add_p2_re_le c b
  have hregularScaled := mul_le_mul_of_nonneg_left hregular
    yoshidaEndpointA_pos.le
  have hhyper := yoshidaEndpointHyperbolicQuadratic_zero_two_eq c b
  rw [← integral_yoshidaEndpoint_cosh,
    ← integral_yoshidaEndpoint_cosh_mul_centeredEvenP2] at hhyper
  unfold yoshidaEndpointOddCleanQuadratic
  rw [hlog, hpotential, hmass]
  have hprofile : (fun x : ℝ ↦
      ((yoshidaEndpointEvenLowProfile c b x : ℝ) : ℂ)) =
      fun x ↦ ((c + b * centeredEvenP2 x : ℝ) : ℂ) := by
    funext x
    rfl
  dsimp only
  rw [hprofile, hhyper]
  unfold yoshidaEndpointEvenLow00 yoshidaEndpointEvenLow02
    yoshidaEndpointEvenLow22 evenLow00 evenLow02 evenLow22
    yoshidaEndpointEvenLowC0 yoshidaEndpointEvenLowC2
    yoshidaEndpointEvenSharpMassLoss yoshidaEndpointScalarMassLoss at ⊢
  unfold yoshidaEndpointA at hregularScaled ⊢
  nlinarith

/-- Structural positivity of the complete clean endpoint quadratic on the
entire fixed `{P₀,P₂}` block. -/
theorem yoshidaEndpointOddCleanQuadratic_nonneg_on_evenLow (c b : ℝ) :
    0 ≤ yoshidaEndpointOddCleanQuadratic
      (yoshidaEndpointEvenLowProfile c b) := by
  have hbounds := yoshidaEndpointEvenLow_matrix_bounds
  have hlow := quadratic_add_tail_nonneg
    yoshidaEndpointEvenLow00 yoshidaEndpointEvenLow02
      yoshidaEndpointEvenLow22 0 0 0 c b
    (lt_trans (by norm_num) hbounds.1) hbounds.2.2.2.2
    (by norm_num)
  norm_num at hlow
  exact hlow.trans (yoshidaEndpointEvenLow_quadratic_le_clean c b)

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenLowPositive
