import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusPositive

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusStructural
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural positivity of the intrinsic static-minus split

The even and odd endpoint forms are bounded below by fixed rational Grams.
The odd Gram is assembled before taking principal minors: its clean lower
Gram is added directly to the odd symmetric-perturbation lower Gram.  The
remaining alternating estimate is exactly the rational Schur theorem.

There is no phase subdivision, sampling, or finite certificate.
-/

/-- The rational odd Gram lies below the complete odd-plus endpoint.  This
is the exact sum of the clean and symmetric-perturbation lower Grams. -/
theorem intrinsicStaticMinusOddLower_le (c1 c3 : ℝ) :
    intrinsicStaticMinusOddLower c1 c3 ≤
      factorTwoIntrinsicStaticOddQuadratic (-1) c1 c3 := by
  have hclean := oddClean_rationalGram_le c1 c3
  have hpert := oddPerturbationLoewner_quadratic_le c1 c3
  have hprofile :
      factorTwoIntrinsicStaticOddQuadratic (-1) c1 c3 =
        yoshidaEndpointOddCleanQuadratic
            (factorTwoOddStructuralLowProfile c1 c3) +
          factorTwoCenteredSymmetricPerturbation
            (factorTwoOddStructuralLowProfile c1 c3) := by
    rw [factorTwoIntrinsicStaticOddQuadratic_eq_profile]
    norm_num [factorTwoEndpointPhaseDiagonal]
  rw [hprofile]
  calc
    intrinsicStaticMinusOddLower c1 c3 =
        ((1777 / 10000 : ℝ) * c1 ^ 2 +
            2 * (2001 / 10000 : ℝ) * c1 * c3 +
            (3314 / 10000 : ℝ) * c3 ^ 2) +
          (oddPerturbationLoewner11 * c1 ^ 2 +
            2 * oddPerturbationLoewner13 * c1 * c3 +
            oddPerturbationLoewner33 * c3 ^ 2) := by
      norm_num [intrinsicStaticMinusOddLower,
        intrinsicStaticMinusOddLower11, intrinsicStaticMinusOddLower13,
        intrinsicStaticMinusOddLower33, oddPerturbationLoewner11,
        oddPerturbationLoewner13, oddPerturbationLoewner33]
      ring
    _ ≤ yoshidaEndpointOddCleanQuadratic
          (factorTwoOddStructuralLowProfile c1 c3) +
        factorTwoCenteredSymmetricPerturbation
          (factorTwoOddStructuralLowProfile c1 c3) :=
      add_le_add hclean hpert

/-- Positivity of the fixed even lower form follows from its two exact
principal minors. -/
theorem intrinsicStaticMinusEvenLower_nonneg (c0 c2 : ℝ) :
    0 ≤ intrinsicStaticMinusEvenLower c0 c2 := by
  rcases intrinsicStaticMinusEvenLower_principal_minors_pos with ⟨h00, hdet⟩
  by_cases hne : c0 ≠ 0 ∨ c2 ≠ 0
  · simpa only [intrinsicStaticMinusEvenLower] using
      (real_twoByTwo_quadratic_pos
        intrinsicStaticMinusEvenLower00 intrinsicStaticMinusEvenLower02
        intrinsicStaticMinusEvenLower22 c0 c2 h00 hdet hne).le
  · push_neg at hne
    rcases hne with ⟨rfl, rfl⟩
    norm_num [intrinsicStaticMinusEvenLower]

/-- Positivity of the fixed odd lower form follows from its two exact
principal minors. -/
theorem intrinsicStaticMinusOddLower_nonneg (c1 c3 : ℝ) :
    0 ≤ intrinsicStaticMinusOddLower c1 c3 := by
  rcases intrinsicStaticMinusOddLower_principal_minors_pos with ⟨h11, hdet⟩
  by_cases hne : c1 ≠ 0 ∨ c3 ≠ 0
  · simpa only [intrinsicStaticMinusOddLower] using
      (real_twoByTwo_quadratic_pos
        intrinsicStaticMinusOddLower11 intrinsicStaticMinusOddLower13
        intrinsicStaticMinusOddLower33 c1 c3 h11 hdet hne).le
  · push_neg at hne
    rcases hne with ⟨rfl, rfl⟩
    norm_num [intrinsicStaticMinusOddLower]

/-- The sharp structural alternating bounds close the exact static-minus
Cauchy gate through the two fixed rational lower Grams. -/
theorem factorTwoIntrinsicStaticMinusCauchy_of_alternatingSharpBounds
    (hJ : FactorTwoIntrinsicAlternatingSharpBounds) :
    FactorTwoIntrinsicStaticCauchy (-1) := by
  exact factorTwoIntrinsicStaticMinusCauchy_of_lower_quadratics
    intrinsicStaticMinusEvenLower intrinsicStaticMinusOddLower
    _root_.ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur.intrinsicStaticMinusEvenLower_le
    intrinsicStaticMinusOddLower_le
    intrinsicStaticMinusEvenLower_nonneg intrinsicStaticMinusOddLower_nonneg
    (intrinsicStaticMinus_rationalCauchy_of_alternatingSharpBounds hJ)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusPositive
