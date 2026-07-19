import ArithmeticHodge.Analysis.MultiplicativeWeilFejerLinearResidualStructural

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFejerResidualCrossTestStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilFejerLocalizationStructural
open MultiplicativeWeilFejerLinearResidualStructural

/-!
# Test-level realization of a weighted finite Bombieri cross sum

The real weighted lag sum is itself the real Bombieri functional of one
explicit Bombieri test.  Each mixed quadratic cross has functional real part
twice the complete local-minus-prime cross, so its test coefficient is
`w k / 2`.
-/

/-- Test-valued crosses between one cell and every later cell in a tail,
weighted by their positive linear lag. -/
def bombieriHeadWeightedLagCrossTest
    (w : ℕ → ℝ) (f : BombieriTest) : ℕ → List BombieriTest → BombieriTest
  | _k, [] => 0
  | k, g :: tail =>
      ((w k / 2 : ℝ) : ℂ) • bombieriQuadraticCrossTest f g +
        bombieriHeadWeightedLagCrossTest w f (k + 1) tail

/-- One Bombieri test containing every unordered weighted cross of a finite
line. -/
def bombieriWeightedLinearLagCrossTest
    (w : ℕ → ℝ) : List BombieriTest → BombieriTest
  | [] => 0
  | f :: tail =>
      bombieriHeadWeightedLagCrossTest w f 1 tail +
        bombieriWeightedLinearLagCrossTest w tail

private theorem bombieriFunctional_weightedQuadraticCrossTest_re
    (w : ℝ) (f g : BombieriTest) :
    (bombieriFunctional
      (((w / 2 : ℝ) : ℂ) • bombieriQuadraticCrossTest f g)).re =
      w * bombieriGlobalCrossRealValue f g := by
  rw [map_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have hcross := bombieriFunctional_quadraticCross_twoBlock_re
    f g (1 : ℂ)
  simp only [one_smul, one_mul] at hcross
  unfold bombieriGlobalCrossRealValue
  rw [hcross]
  ring

/-- The real functional of the head test is exactly the recursive real head
cross sum already used by the Fejer residual expansion. -/
theorem bombieriFunctional_headWeightedLagCrossTest_re
    (w : ℕ → ℝ) (f : BombieriTest) (k : ℕ)
    (cells : List BombieriTest) :
    (bombieriFunctional
      (bombieriHeadWeightedLagCrossTest w f k cells)).re =
      bombieriHeadWeightedLagCross w f k cells := by
  induction cells generalizing k with
  | nil =>
      simp only [bombieriHeadWeightedLagCrossTest,
        bombieriHeadWeightedLagCross]
      rw [map_zero]
      rfl
  | cons g tail ih =>
      simp only [bombieriHeadWeightedLagCrossTest,
        bombieriHeadWeightedLagCross, map_add, Complex.add_re]
      rw [bombieriFunctional_weightedQuadraticCrossTest_re, ih]

/-- The complete weighted real lag sum is represented by the real functional
of the corresponding single combined Bombieri test. -/
theorem bombieriFunctional_weightedLinearLagCrossTest_re
    (w : ℕ → ℝ) (cells : List BombieriTest) :
    (bombieriFunctional
      (bombieriWeightedLinearLagCrossTest w cells)).re =
      bombieriWeightedLinearLagCross w cells := by
  induction cells with
  | nil =>
      simp only [bombieriWeightedLinearLagCrossTest,
        bombieriWeightedLinearLagCross]
      rw [map_zero]
      rfl
  | cons f tail ih =>
      simp only [bombieriWeightedLinearLagCrossTest,
        bombieriWeightedLinearLagCross, map_add, Complex.add_re]
      rw [bombieriFunctional_headWeightedLagCrossTest_re, ih]

/-- The explicit test whose functional is the order-three Fejer residual. -/
def bombieriFejerThreeResidualCrossTest
    (cells : List BombieriTest) : BombieriTest :=
  bombieriWeightedLinearLagCrossTest
    bombieriFejerThreeResidualLagWeight cells

theorem bombieriFunctional_fejerThreeResidualCrossTest_re
    (cells : List BombieriTest) :
    (bombieriFunctional
      (bombieriFejerThreeResidualCrossTest cells)).re =
      bombieriWeightedLinearLagCross
        bombieriFejerThreeResidualLagWeight cells := by
  exact bombieriFunctional_weightedLinearLagCrossTest_re
    bombieriFejerThreeResidualLagWeight cells

/-- The test-level residual realizes exactly the difference between the full
finite Bombieri quadratic and its positive order-three Fejer reserve. -/
theorem bombieriFunctional_fejerThreeResidualCrossTest_re_eq_sub_fejer
    (cells : List BombieriTest) :
    (bombieriFunctional
      (bombieriFejerThreeResidualCrossTest cells)).re =
      bombieriQuadraticRealValue cells.sum -
        bombieriLinearFejerThree cells := by
  rw [bombieriFunctional_fejerThreeResidualCrossTest_re,
    bombieriQuadraticRealValue_list_sum_sub_linearFejerThree]

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFejerResidualCrossTestStructural
