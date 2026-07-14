import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep12Structural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowControlMonotonicity
open YoshidaFactorTwoPhaseIntrinsicLowControlStep12Step23Positive
open YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
open YoshidaFactorTwoPhaseIntrinsicLowControlsPositive
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseLowSchur
open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseOddLowEndpointPositive
open YoshidaFactorTwoPhaseOddLowSchur

/-!
# Structural reduction of intrinsic control Step12

The middle Bernstein difference is kept as one coupled `2 x 2` form.  Its
endpoint part is the sum of the two complete odd endpoint quadratics; its
only negative term is the adjugate form of the even negative perturbation on
the complete alternating row.  No entry of the Step12 Gram is expanded into
phase samples or modes.
-/

private theorem oddDirection_eq_minus_sub_plus (c d : ℝ) :
    factorTwoIntrinsicOddDirectionQuadratic c d =
      factorTwoIntrinsicOddPhaseQuadratic (-1) c d -
        factorTwoIntrinsicOddPhaseQuadratic 1 c d := by
  unfold factorTwoIntrinsicOddDirectionQuadratic
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicOddPhaseLow33
  ring

/-- Exact endpoint/adjugate presentation of the middle Bernstein step. -/
theorem three_mul_factorTwoIntrinsicBoundaryControlStep12_eq_endpoints
    (c d : ℝ) :
    3 * factorTwoIntrinsicBoundaryControlStep12 c d =
      (factorTwoIntrinsicEvenDetCoefficient0 +
          factorTwoIntrinsicEvenDetCoefficient1) *
          factorTwoIntrinsicOddPhaseQuadratic (-1) c d +
        (factorTwoIntrinsicEvenDetCoefficient2 -
          factorTwoIntrinsicEvenDetCoefficient0) *
          factorTwoIntrinsicOddPhaseQuadratic 1 c d -
        factorTwoIntrinsicAdjugateCoefficient1 c d := by
  rw [three_mul_factorTwoIntrinsicBoundaryControlStep12,
    oddDirection_eq_minus_sub_plus]
  ring

/-! ## A structural upper Loewner matrix for the adjugate penalty -/

def step12EvenNegativeUpper00 : ℝ := 4569 / 20000

def step12EvenNegativeUpper02 : ℝ := 20487 / 100000

def step12EvenNegativeUpper22 : ℝ := 9467 / 50000

theorem evenNegativePerturbation_quadratic_le_step12Upper (c d : ℝ) :
    evenNegativePerturbation00 * c ^ 2 +
        2 * evenNegativePerturbation02 * c * d +
        evenNegativePerturbation22 * d ^ 2 ≤
      step12EvenNegativeUpper00 * c ^ 2 +
        2 * step12EvenNegativeUpper02 * c * d +
        step12EvenNegativeUpper22 * d ^ 2 := by
  have hp := evenPositivePerturbationSharp_quadratic_le c d
  have hq := evenNegativePerturbation_profile_eq c d
  unfold step12EvenNegativeUpper00 step12EvenNegativeUpper02
    step12EvenNegativeUpper22
  unfold evenPositivePerturbationSharp00 evenPositivePerturbationSharp02
    evenPositivePerturbationSharp22 at hp
  nlinarith

/-- In dimension two, adjugation preserves Loewner order: the adjugate
quadratic of a defect is its original quadratic at the rotated vector
`(j₂,-j₀)`.  Thus the complete alternating row stays coupled. -/
theorem factorTwoIntrinsicAdjugateCoefficient1_le_step12Upper
    (c d : ℝ) :
    factorTwoIntrinsicAdjugateCoefficient1 c d ≤
      2 * (step12EvenNegativeUpper22 *
            factorTwoIntrinsicAlternatingRow0 c d ^ 2 -
          2 * step12EvenNegativeUpper02 *
            factorTwoIntrinsicAlternatingRow0 c d *
            factorTwoIntrinsicAlternatingRow2 c d +
          step12EvenNegativeUpper00 *
            factorTwoIntrinsicAlternatingRow2 c d ^ 2) := by
  have hrot := evenNegativePerturbation_quadratic_le_step12Upper
    (factorTwoIntrinsicAlternatingRow2 c d)
    (-factorTwoIntrinsicAlternatingRow0 c d)
  unfold evenNegativePerturbation00 evenNegativePerturbation02
    evenNegativePerturbation22 at hrot
  unfold factorTwoIntrinsicAdjugateCoefficient1
    factorTwoIntrinsicEvenDirection00 factorTwoIntrinsicEvenDirection02
    factorTwoIntrinsicEvenDirection22
  nlinarith

/-! ## Cancellation-preserving clean/perturbation coordinates -/

/-- Determinant of the complete clean even Gram. -/
def step12EvenCleanDet : ℝ :=
  yoshidaEndpointEvenLowGram00 * yoshidaEndpointEvenLowGram22 -
    yoshidaEndpointEvenLowGram02 ^ 2

/-- Determinant of the complete negative even perturbation `Q`. -/
def step12EvenNegativeDet : ℝ :=
  evenNegativePerturbation00 * evenNegativePerturbation22 -
    evenNegativePerturbation02 ^ 2

/-- Mixed determinant of the clean even Gram and `Q`. -/
def step12EvenCleanNegativeMixedDet : ℝ :=
  yoshidaEndpointEvenLowGram00 * evenNegativePerturbation22 +
    yoshidaEndpointEvenLowGram22 * evenNegativePerturbation00 -
    2 * yoshidaEndpointEvenLowGram02 * evenNegativePerturbation02

/-- The complete clean odd form, before either endpoint perturbation is
inserted. -/
def step12OddCleanQuadratic (c d : ℝ) : ℝ :=
  yoshidaEndpointOddCleanQuadratic
    (factorTwoOddStructuralLowProfile c d)

/-- The signed odd perturbation form. -/
def step12OddPerturbationQuadratic (c d : ℝ) : ℝ :=
  factorTwoCenteredSymmetricPerturbation
    (factorTwoOddStructuralLowProfile c d)

/-- Half of the direction-adjugate penalty.  Keeping this as one rotated
quadratic is essential: its three entries have large cancellations. -/
def step12NegativeAdjugateCore (c d : ℝ) : ℝ :=
  evenNegativePerturbation22 *
      factorTwoIntrinsicAlternatingRow0 c d ^ 2 -
    2 * evenNegativePerturbation02 *
      factorTwoIntrinsicAlternatingRow0 c d *
      factorTwoIntrinsicAlternatingRow2 c d +
    evenNegativePerturbation00 *
      factorTwoIntrinsicAlternatingRow2 c d ^ 2

private theorem oddPhase_eq_clean_add_perturbation
    (a c d : ℝ) :
    factorTwoIntrinsicOddPhaseQuadratic a c d =
      step12OddCleanQuadratic c d +
        a * step12OddPerturbationQuadratic c d := by
  unfold factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicOddPhaseLow33 step12OddCleanQuadratic
    step12OddPerturbationQuadratic
  simpa only [factorTwoOddStructuralPhaseLow11,
    factorTwoOddStructuralPhaseLow13, factorTwoOddStructuralPhaseLow33]
    using factorTwoOddStructuralPhaseLow_quadratic a c d

theorem factorTwoIntrinsicEvenDetCoefficient0_add_one_eq_clean_negative
    :
    factorTwoIntrinsicEvenDetCoefficient0 +
        factorTwoIntrinsicEvenDetCoefficient1 =
      step12EvenCleanDet + step12EvenCleanNegativeMixedDet -
        3 * step12EvenNegativeDet := by
  unfold step12EvenCleanDet step12EvenNegativeDet
    step12EvenCleanNegativeMixedDet
  unfold evenNegativePerturbation00 evenNegativePerturbation02
    evenNegativePerturbation22
  unfold factorTwoIntrinsicEvenDetCoefficient0
    factorTwoIntrinsicEvenDetCoefficient1 factorTwoIntrinsicEvenPhaseDet
    factorTwoIntrinsicEvenDirection00 factorTwoIntrinsicEvenDirection02
    factorTwoIntrinsicEvenDirection22 factorTwoStructuralPhaseLow00
    factorTwoStructuralPhaseLow02 factorTwoStructuralPhaseLow22
  ring

theorem factorTwoIntrinsicEvenDetCoefficient2_sub_zero_eq_clean_negative
    :
    factorTwoIntrinsicEvenDetCoefficient2 -
        factorTwoIntrinsicEvenDetCoefficient0 =
      -step12EvenCleanDet + step12EvenCleanNegativeMixedDet +
        3 * step12EvenNegativeDet := by
  unfold step12EvenCleanDet step12EvenNegativeDet
    step12EvenCleanNegativeMixedDet
  unfold evenNegativePerturbation00 evenNegativePerturbation02
    evenNegativePerturbation22
  unfold factorTwoIntrinsicEvenDetCoefficient0
    factorTwoIntrinsicEvenDetCoefficient2 factorTwoIntrinsicEvenPhaseDet
    factorTwoIntrinsicEvenDirection00 factorTwoIntrinsicEvenDirection02
    factorTwoIntrinsicEvenDirection22 factorTwoStructuralPhaseLow00
    factorTwoStructuralPhaseLow02 factorTwoStructuralPhaseLow22
  ring

theorem factorTwoIntrinsicAdjugateCoefficient1_eq_two_mul_core
    (c d : ℝ) :
    factorTwoIntrinsicAdjugateCoefficient1 c d =
      2 * step12NegativeAdjugateCore c d := by
  unfold step12NegativeAdjugateCore
  unfold evenNegativePerturbation00 evenNegativePerturbation02
    evenNegativePerturbation22
  unfold factorTwoIntrinsicAdjugateCoefficient1
    factorTwoIntrinsicEvenDirection00 factorTwoIntrinsicEvenDirection02
    factorTwoIntrinsicEvenDirection22
  ring

/-- Exact clean/perturbation normal form of Step12.  The two endpoint
determinant coefficients collapse to one mixed determinant and the signed
difference of the two complete determinants. -/
theorem three_mul_factorTwoIntrinsicBoundaryControlStep12_eq_clean_negative
    (c d : ℝ) :
    3 * factorTwoIntrinsicBoundaryControlStep12 c d =
      2 * (step12EvenCleanNegativeMixedDet *
            step12OddCleanQuadratic c d +
          (3 * step12EvenNegativeDet - step12EvenCleanDet) *
            step12OddPerturbationQuadratic c d -
          step12NegativeAdjugateCore c d) := by
  rw [three_mul_factorTwoIntrinsicBoundaryControlStep12_eq_endpoints,
    factorTwoIntrinsicEvenDetCoefficient0_add_one_eq_clean_negative,
    factorTwoIntrinsicEvenDetCoefficient2_sub_zero_eq_clean_negative,
    factorTwoIntrinsicAdjugateCoefficient1_eq_two_mul_core,
    oddPhase_eq_clean_add_perturbation,
    oddPhase_eq_clean_add_perturbation]
  ring

/-! ## The two scalar signs in the normal form -/

private theorem twoByTwo_coefficients_nonneg_of_quadratic_nonneg_step12
    (q00 q02 q22 : ℝ)
    (hq : ∀ c d : ℝ,
      0 ≤ q00 * c ^ 2 + 2 * q02 * c * d + q22 * d ^ 2) :
    0 ≤ q00 ∧ 0 ≤ q22 ∧ 0 ≤ q00 * q22 - q02 ^ 2 := by
  have h00 : 0 ≤ q00 := by
    have h := hq 1 0
    norm_num at h ⊢
    exact h
  have h22 : 0 ≤ q22 := by
    have h := hq 0 1
    norm_num at h ⊢
    exact h
  refine ⟨h00, h22, ?_⟩
  by_cases hq00 : q00 = 0
  · subst q00
    by_cases hq22 : q22 = 0
    · subst q22
      have hp := hq 1 1
      have hm := hq 1 (-1)
      norm_num at hp hm ⊢
      have hq02 : q02 = 0 := by linarith
      norm_num [hq02]
    · have hq22pos : 0 < q22 := lt_of_le_of_ne h22 (Ne.symm hq22)
      have hspecial := hq q22 (-q02)
      norm_num at hspecial ⊢
      have hq02 : q02 = 0 := by
        by_contra hne
        have hsq : 0 < q02 ^ 2 := sq_pos_of_ne_zero hne
        nlinarith [mul_pos hq22pos hsq]
      norm_num [hq02]
  · have hq00pos : 0 < q00 := lt_of_le_of_ne h00 (Ne.symm hq00)
    have hspecial := hq q02 (-q00)
    have hid :
        q00 * q02 ^ 2 + 2 * q02 * q02 * (-q00) +
            q22 * (-q00) ^ 2 =
          q00 * (q00 * q22 - q02 ^ 2) := by
      ring
    rw [hid] at hspecial
    exact nonneg_of_mul_nonneg_right hspecial hq00pos

private theorem twoByTwo_mixedDet_nonneg_of_quadratics_nonneg_step12
    (a b d u v w : ℝ)
    (hA : ∀ c e : ℝ,
      0 ≤ a * c ^ 2 + 2 * b * c * e + d * e ^ 2)
    (hU : ∀ c e : ℝ,
      0 ≤ u * c ^ 2 + 2 * v * c * e + w * e ^ 2) :
    0 ≤ a * w + d * u - 2 * b * v := by
  have hAc := twoByTwo_coefficients_nonneg_of_quadratic_nonneg_step12
    a b d hA
  have hUc := twoByTwo_coefficients_nonneg_of_quadratic_nonneg_step12
    u v w hU
  by_cases hu : u = 0
  · subst u
    have hv : v = 0 := by
      by_cases hw : w = 0
      · subst w
        have hp := hU 1 1
        have hm := hU 1 (-1)
        norm_num at hp hm
        linarith
      · have hwpos : 0 < w := lt_of_le_of_ne hUc.2.1 (Ne.symm hw)
        have hspecial := hU w (-v)
        norm_num at hspecial
        by_contra hne
        have hsq : 0 < v ^ 2 := sq_pos_of_ne_zero hne
        nlinarith [mul_pos hwpos hsq]
    subst v
    norm_num
    exact mul_nonneg hAc.1 hUc.2.1
  · have hupos : 0 < u := lt_of_le_of_ne hUc.1 (Ne.symm hu)
    have hAeval := hA v (-u)
    have hid :
        u * (a * w + d * u - 2 * b * v) =
          a * (u * w - v ^ 2) +
            (a * v ^ 2 + 2 * b * v * (-u) + d * (-u) ^ 2) := by
      ring
    have hscaled : 0 ≤ u * (a * w + d * u - 2 * b * v) := by
      rw [hid]
      exact add_nonneg (mul_nonneg hAc.1 hUc.2.2) hAeval
    exact nonneg_of_mul_nonneg_right hscaled hupos

private theorem twoByTwo_det_le_of_quadratic_order_step12
    (a b d u v w : ℝ)
    (hA : ∀ c e : ℝ,
      0 ≤ a * c ^ 2 + 2 * b * c * e + d * e ^ 2)
    (hdefect : ∀ c e : ℝ,
      0 ≤ (u - a) * c ^ 2 + 2 * (v - b) * c * e +
        (w - d) * e ^ 2) :
    a * d - b ^ 2 ≤ u * w - v ^ 2 := by
  have hmixed := twoByTwo_mixedDet_nonneg_of_quadratics_nonneg_step12
    a b d (u - a) (v - b) (w - d) hA hdefect
  have hdet :=
    (twoByTwo_coefficients_nonneg_of_quadratic_nonneg_step12
      (u - a) (v - b) (w - d) hdefect).2.2
  nlinarith

private theorem evenNegativePerturbation_quadratic_nonneg_step12
    (c d : ℝ) :
    0 ≤ evenNegativePerturbation00 * c ^ 2 +
      2 * evenNegativePerturbation02 * c * d +
      evenNegativePerturbation22 * d ^ 2 := by
  have hlo := evenNegativePerturbationSharp_quadratic_le c d
  rw [← evenNegativePerturbation_profile_eq] at hlo
  have hsharp : 0 ≤
      evenNegativePerturbationSharp00 * c ^ 2 +
        2 * evenNegativePerturbationSharp02 * c * d +
        evenNegativePerturbationSharp22 * d ^ 2 := by
    by_cases hne : c ≠ 0 ∨ d ≠ 0
    · exact (real_twoByTwo_quadratic_pos _ _ _ c d
        evenNegativePerturbationSharp_principal_minors_pos.1
        evenNegativePerturbationSharp_principal_minors_pos.2.2 hne).le
    · push_neg at hne
      rcases hne with ⟨rfl, rfl⟩
      norm_num
  exact hsharp.trans hlo

theorem step12EvenCleanNegativeMixedDet_nonneg :
    0 ≤ step12EvenCleanNegativeMixedDet := by
  have hclean : ∀ c d : ℝ,
      0 ≤ yoshidaEndpointEvenLowGram00 * c ^ 2 +
        2 * yoshidaEndpointEvenLowGram02 * c * d +
        yoshidaEndpointEvenLowGram22 * d ^ 2 := by
    intro c d
    by_cases hne : c ≠ 0 ∨ d ≠ 0
    · exact (real_twoByTwo_quadratic_pos _ _ _ c d
        yoshidaEndpointEvenLowGram00_pos
        yoshidaEndpointEvenLowGram_det_pos hne).le
    · push_neg at hne
      rcases hne with ⟨rfl, rfl⟩
      norm_num
  have hnegative : ∀ c d : ℝ,
      0 ≤ evenNegativePerturbation00 * c ^ 2 +
        2 * evenNegativePerturbation02 * c * d +
        evenNegativePerturbation22 * d ^ 2 :=
    evenNegativePerturbation_quadratic_nonneg_step12
  exact twoByTwo_mixedDet_nonneg_of_quadratics_nonneg_step12
    yoshidaEndpointEvenLowGram00 yoshidaEndpointEvenLowGram02
    yoshidaEndpointEvenLowGram22 evenNegativePerturbation00
    evenNegativePerturbation02 evenNegativePerturbation22 hclean hnegative

theorem step12EvenNegativeDet_le_upper :
    step12EvenNegativeDet ≤
      step12EvenNegativeUpper00 * step12EvenNegativeUpper22 -
        step12EvenNegativeUpper02 ^ 2 := by
  have hnegative : ∀ c d : ℝ,
      0 ≤ evenNegativePerturbation00 * c ^ 2 +
        2 * evenNegativePerturbation02 * c * d +
        evenNegativePerturbation22 * d ^ 2 :=
    evenNegativePerturbation_quadratic_nonneg_step12
  have hdefect : ∀ c d : ℝ,
      0 ≤
        (step12EvenNegativeUpper00 - evenNegativePerturbation00) * c ^ 2 +
          2 * (step12EvenNegativeUpper02 - evenNegativePerturbation02) * c * d +
          (step12EvenNegativeUpper22 - evenNegativePerturbation22) * d ^ 2 := by
    intro c d
    have h := evenNegativePerturbation_quadratic_le_step12Upper c d
    nlinarith
  unfold step12EvenNegativeDet
  exact twoByTwo_det_le_of_quadratic_order_step12
    evenNegativePerturbation00 evenNegativePerturbation02
    evenNegativePerturbation22 step12EvenNegativeUpper00
    step12EvenNegativeUpper02 step12EvenNegativeUpper22 hnegative hdefect

theorem three_mul_step12EvenNegativeDet_lt_step12EvenCleanDet :
    3 * step12EvenNegativeDet < step12EvenCleanDet := by
  have hclean00 := intrinsicEven_cleanGram00_gt
  have hclean02 := intrinsicEven_cleanGram02_bounds
  have hclean22 := intrinsicEven_cleanGram22_gt
  have hclean02pos : 0 < yoshidaEndpointEvenLowGram02 := by
    linarith [hclean02.1]
  have hcleanProduct :
      (3665 / 10000 : ℝ) * (3269 / 10000) <
        yoshidaEndpointEvenLowGram00 * yoshidaEndpointEvenLowGram22 := by
    calc
      (3665 / 10000 : ℝ) * (3269 / 10000) <
          yoshidaEndpointEvenLowGram00 * (3269 / 10000) :=
        mul_lt_mul_of_pos_right hclean00 (by norm_num)
      _ < yoshidaEndpointEvenLowGram00 * yoshidaEndpointEvenLowGram22 :=
        mul_lt_mul_of_pos_left hclean22
          (by linarith [hclean00] : 0 < yoshidaEndpointEvenLowGram00)
  have hcleanSquare :
      yoshidaEndpointEvenLowGram02 ^ 2 < (3403 / 10000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hclean02.2 hclean02pos.le (by norm_num)
  have hupper := step12EvenNegativeDet_le_upper
  unfold step12EvenNegativeDet step12EvenNegativeUpper00
    step12EvenNegativeUpper02 step12EvenNegativeUpper22 at hupper
  unfold step12EvenNegativeDet step12EvenCleanDet
  have hrational :
      3 * ((4569 / 20000 : ℝ) * (9467 / 50000) -
          (20487 / 100000) ^ 2) <
        (3665 / 10000 : ℝ) * (3269 / 10000) -
          (3403 / 10000) ^ 2 := by
    norm_num
  nlinarith

/-! ## The remaining coupled Schur form -/

def step12OddCleanLower (c d : ℝ) : ℝ :=
  (1777 / 10000 : ℝ) * c ^ 2 +
    2 * (2001 / 10000 : ℝ) * c * d +
    (3314 / 10000 : ℝ) * d ^ 2

def step12OddPerturbationUpper (c d : ℝ) : ℝ :=
  oddPerturbationUpper11 * c ^ 2 +
    2 * oddPerturbationUpper13 * c * d +
    oddPerturbationUpper33 * d ^ 2

/-- After the two proved scalar signs are used, every analytic odd term is
replaced in the favorable Loewner direction.  This is the sole remaining
coupled `2 x 2` form. -/
def step12ReducedResidual (c d : ℝ) : ℝ :=
  step12EvenCleanNegativeMixedDet * step12OddCleanLower c d +
    (3 * step12EvenNegativeDet - step12EvenCleanDet) *
      step12OddPerturbationUpper c d -
    step12NegativeAdjugateCore c d

theorem factorTwoIntrinsicBoundaryControlStep12_nonneg_of_reducedResidual
    (c d : ℝ) (hres : 0 ≤ step12ReducedResidual c d) :
    0 ≤ factorTwoIntrinsicBoundaryControlStep12 c d := by
  have hclean := oddClean_rationalGram_le c d
  have hpert := oddPerturbation_quadratic_le_upper c d
  have hM := step12EvenCleanNegativeMixedDet_nonneg
  have hT : 3 * step12EvenNegativeDet - step12EvenCleanDet ≤ 0 := by
    linarith [three_mul_step12EvenNegativeDet_lt_step12EvenCleanDet]
  have hcleanScaled :
      step12EvenCleanNegativeMixedDet * step12OddCleanLower c d ≤
        step12EvenCleanNegativeMixedDet * step12OddCleanQuadratic c d := by
    apply mul_le_mul_of_nonneg_left _ hM
    simpa only [step12OddCleanLower, step12OddCleanQuadratic] using hclean
  have hpertScaled :
      (3 * step12EvenNegativeDet - step12EvenCleanDet) *
          step12OddPerturbationUpper c d ≤
        (3 * step12EvenNegativeDet - step12EvenCleanDet) *
          step12OddPerturbationQuadratic c d := by
    apply mul_le_mul_of_nonpos_left _ hT
    simpa only [step12OddPerturbationUpper,
      step12OddPerturbationQuadratic] using hpert
  have hexact :=
    three_mul_factorTwoIntrinsicBoundaryControlStep12_eq_clean_negative c d
  unfold step12ReducedResidual at hres
  nlinarith

theorem factorTwoIntrinsicBoundaryControlStep12_nonneg_of_reducedResidual_all
    (hres : ∀ c d : ℝ, 0 ≤ step12ReducedResidual c d) :
    ∀ c d : ℝ, 0 ≤ factorTwoIntrinsicBoundaryControlStep12 c d := by
  intro c d
  exact factorTwoIntrinsicBoundaryControlStep12_nonneg_of_reducedResidual
    c d (hres c d)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep12Structural
