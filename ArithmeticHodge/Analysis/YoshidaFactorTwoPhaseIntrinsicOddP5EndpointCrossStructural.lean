import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationCrossStructural

/-!
# Structural odd `P5` endpoint crosses

The exact affine endpoint formulas combine the independently certified clean
and perturbation boxes.  This gives rational enclosures for all four new
entries of the two odd `P1/P3/P5` endpoint matrices without sampling either
matrix or expanding a determinant.
-/

/-- The plus-endpoint `P1`--`P5` cross lies in a strict rational box. -/
theorem factorTwoIntrinsicFourP45Cross15_one_bounds :
    (131727 / 1000000 : ℝ) < factorTwoIntrinsicFourP45Cross15 1 ∧
      factorTwoIntrinsicFourP45Cross15 1 < (131929 / 1000000 : ℝ) := by
  have hclean := cleanBilinear_p1_p5_bounds
  have hpert :=
    factorTwoCenteredSymmetricPerturbationBilinear_p1_p5_bounds
  unfold factorTwoIntrinsicFourP45Cross15
  constructor <;> norm_num at * <;> linarith

/-- The minus-endpoint `P1`--`P5` cross lies in a strict rational box. -/
theorem factorTwoIntrinsicFourP45Cross15_neg_one_bounds :
    (10927 / 1000000 : ℝ) < factorTwoIntrinsicFourP45Cross15 (-1) ∧
      factorTwoIntrinsicFourP45Cross15 (-1) < (11129 / 1000000 : ℝ) := by
  have hclean := cleanBilinear_p1_p5_bounds
  have hpert :=
    factorTwoCenteredSymmetricPerturbationBilinear_p1_p5_bounds
  unfold factorTwoIntrinsicFourP45Cross15
  constructor <;> norm_num at * <;> linarith

/-- The plus-endpoint `P3`--`P5` cross lies in a strict rational box. -/
theorem factorTwoIntrinsicFourP45Cross35_one_bounds :
    (172324 / 1000000 : ℝ) < factorTwoIntrinsicFourP45Cross35 1 ∧
      factorTwoIntrinsicFourP45Cross35 1 < (172427 / 1000000 : ℝ) := by
  have hclean := cleanBilinear_p3_p5_bounds
  have hpert :=
    factorTwoCenteredSymmetricPerturbationBilinear_p3_p5_bounds
  unfold factorTwoIntrinsicFourP45Cross35
  constructor <;> norm_num at * <;> linarith

/-- The minus-endpoint `P3`--`P5` cross lies in a strict rational box. -/
theorem factorTwoIntrinsicFourP45Cross35_neg_one_bounds :
    (49824 / 1000000 : ℝ) < factorTwoIntrinsicFourP45Cross35 (-1) ∧
      factorTwoIntrinsicFourP45Cross35 (-1) < (49927 / 1000000 : ℝ) := by
  have hclean := cleanBilinear_p3_p5_bounds
  have hpert :=
    factorTwoCenteredSymmetricPerturbationBilinear_p3_p5_bounds
  unfold factorTwoIntrinsicFourP45Cross35
  constructor <;> norm_num at * <;> linarith

/-- All four odd `P5` endpoint-cross boxes, packaged for matrix assembly. -/
theorem factorTwoIntrinsicFourP45_oddP5_endpoint_cross_bounds :
    ((131727 / 1000000 : ℝ) < factorTwoIntrinsicFourP45Cross15 1 ∧
      factorTwoIntrinsicFourP45Cross15 1 < (131929 / 1000000 : ℝ)) ∧
    ((10927 / 1000000 : ℝ) < factorTwoIntrinsicFourP45Cross15 (-1) ∧
      factorTwoIntrinsicFourP45Cross15 (-1) < (11129 / 1000000 : ℝ)) ∧
    ((172324 / 1000000 : ℝ) < factorTwoIntrinsicFourP45Cross35 1 ∧
      factorTwoIntrinsicFourP45Cross35 1 < (172427 / 1000000 : ℝ)) ∧
    ((49824 / 1000000 : ℝ) < factorTwoIntrinsicFourP45Cross35 (-1) ∧
      factorTwoIntrinsicFourP45Cross35 (-1) < (49927 / 1000000 : ℝ)) :=
  ⟨factorTwoIntrinsicFourP45Cross15_one_bounds,
    factorTwoIntrinsicFourP45Cross15_neg_one_bounds,
    factorTwoIntrinsicFourP45Cross35_one_bounds,
    factorTwoIntrinsicFourP45Cross35_neg_one_bounds⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
