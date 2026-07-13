import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeClosure

set_option autoImplicit false

open MeasureTheory

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeFinal

open YoshidaEndpointEvenP2LogEnergy
open YoshidaEndpointEvenProjectedBaseIntegrable
open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenProjectedGapMoments
open YoshidaEndpointEvenProjectedMatrixClosure
open YoshidaEndpointEvenProjectedRemainderEnvelopeClosure
open YoshidaEndpointEvenProjectedRemainderEnvelopeTrueGram
open YoshidaEndpointEvenProjectedRemainderIntegrable
open YoshidaEndpointEvenProjectedRemainderMoments
open YoshidaEndpointEvenTailRepresenter

noncomputable section

/-- Quantitative lower bound for the first principal entry of gap minus
remainder. -/
theorem fixedProjectedGap_sub_remainder00_gt :
    (14463 / 50000 : ℝ) <
      fixedProjectedGapGram00 - fixedProjectedPolynomialRemainderGram00 := by
  have hgap := fixedProjectedGapGram00_gt
  have hrem := fixedProjectedPolynomialRemainderGram00_lt
  norm_num at hgap hrem ⊢
  linarith

/-- Quantitative lower bound for the second diagonal entry of gap minus
remainder. -/
theorem fixedProjectedGap_sub_remainder22_gt :
    (11789 / 50000 : ℝ) <
      fixedProjectedGapGram22 - fixedProjectedPolynomialRemainderGram22 := by
  have hgap := fixedProjectedGapGram22_gt
  have hrem := fixedProjectedPolynomialRemainderGram22_lt
  norm_num at hgap hrem ⊢
  linarith

/-- The mixed entry of gap minus remainder is positive and has the displayed
upper enclosure. -/
theorem fixedProjectedGap_sub_remainder02_bounds :
    (26073 / 100000 : ℝ) <
        fixedProjectedGapGram02 - fixedProjectedPolynomialRemainderGram02 ∧
      fixedProjectedGapGram02 - fixedProjectedPolynomialRemainderGram02 <
        (26077 / 100000 : ℝ) := by
  have hgap := fixedProjectedGapGram02_bounds
  have hrem := fixedProjectedPolynomialRemainderGram02_bounds
  constructor <;> norm_num at hgap hrem ⊢ <;> linarith

/-- First principal minor of the exact gap-minus-remainder matrix. -/
theorem fixedProjectedGap_sub_remainder00_pos :
    0 < fixedProjectedGapGram00 - fixedProjectedPolynomialRemainderGram00 :=
  (by norm_num : (0 : ℝ) < 14463 / 50000).trans
    fixedProjectedGap_sub_remainder00_gt

/-- Quantitative determinant lower bound for the exact gap-minus-remainder
matrix. -/
theorem fixedProjectedGap_sub_remainder_det_gt :
    (2007299 / 10000000000 : ℝ) <
      (fixedProjectedGapGram00 - fixedProjectedPolynomialRemainderGram00) *
          (fixedProjectedGapGram22 - fixedProjectedPolynomialRemainderGram22) -
        (fixedProjectedGapGram02 - fixedProjectedPolynomialRemainderGram02) ^ 2 := by
  let d00 : ℝ := fixedProjectedGapGram00 - fixedProjectedPolynomialRemainderGram00
  let d02 : ℝ := fixedProjectedGapGram02 - fixedProjectedPolynomialRemainderGram02
  let d22 : ℝ := fixedProjectedGapGram22 - fixedProjectedPolynomialRemainderGram22
  have h00 : (14463 / 50000 : ℝ) < d00 :=
    fixedProjectedGap_sub_remainder00_gt
  have h22 : (11789 / 50000 : ℝ) < d22 :=
    fixedProjectedGap_sub_remainder22_gt
  have h02 : (26073 / 100000 : ℝ) < d02 ∧
      d02 < (26077 / 100000 : ℝ) :=
    fixedProjectedGap_sub_remainder02_bounds
  have hprod :
      (14463 / 50000 : ℝ) * (11789 / 50000 : ℝ) < d00 * d22 := by
    exact mul_lt_mul h00 h22.le (by norm_num) (by linarith [h00])
  have h02pos : 0 < d02 :=
    (by norm_num : (0 : ℝ) < 26073 / 100000).trans h02.1
  have hsq : d02 ^ 2 < (26077 / 100000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ h02.2 h02pos.le (by norm_num)
  dsimp only [d00, d02, d22] at hprod hsq ⊢
  norm_num at hprod hsq ⊢
  linarith

/-- Second principal minor of the exact gap-minus-remainder matrix. -/
theorem fixedProjectedGap_sub_remainder_det_pos :
    0 <
      (fixedProjectedGapGram00 - fixedProjectedPolynomialRemainderGram00) *
          (fixedProjectedGapGram22 - fixedProjectedPolynomialRemainderGram22) -
        (fixedProjectedGapGram02 - fixedProjectedPolynomialRemainderGram02) ^ 2 :=
  (by norm_num : (0 : ℝ) < 2007299 / 10000000000).trans
    fixedProjectedGap_sub_remainder_det_gt

/-- Unconditional fixed-endpoint weighted-dual inequality.  All ordinary
integrability obligations and both principal minors are discharged here. -/
theorem fixedProjectedWeightedDual_le_exactLowGram (c b : ℝ) :
    (∫ x : ℝ in -1..1,
      (c * fixedProjectedTailRepresenter0 x +
        b * fixedProjectedTailRepresenter2 x) ^ 2 /
          yoshidaEndpointEvenTailWeight x) ≤
      yoshidaEndpointEvenLowGram00 * c ^ 2 +
        2 * yoshidaEndpointEvenLowGram02 * c * b +
        yoshidaEndpointEvenLowGram22 * b ^ 2 := by
  exact fixedProjectedWeightedDual_le_exactLowGram_of_matrix_pos c b
    intervalIntegrable_fixedProjectedPolynomialRemainderGram00Integrand
    intervalIntegrable_fixedProjectedPolynomialRemainderGram02Integrand
    intervalIntegrable_fixedProjectedPolynomialRemainderGram22Integrand
    (intervalIntegrable_fixedProjectedDualBaseIntegrand 1 0)
    intervalIntegrable_fixedProjectedDualBaseCrossIntegrand
    (intervalIntegrable_fixedProjectedDualBaseIntegrand 0 1)
    (intervalIntegrable_fixedProjectedTrueRemainderIntegrand c b)
    (intervalIntegrable_fixedProjectedAtanhRemainderIntegrand c b)
    fixedProjectedGap_sub_remainder00_pos
    fixedProjectedGap_sub_remainder_det_pos

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeFinal
