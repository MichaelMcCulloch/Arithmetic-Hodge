import ArithmeticHodge.Analysis.YoshidaFactorTwoParityRealification
import ArithmeticHodge.Analysis.YoshidaFactorTwoCoreReduction

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoRealChannel

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilRestrictedSupportEndpointPositive
open YoshidaBombieriDiagonalResidual
open YoshidaBombieriResidualPairing
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoCoreReduction
open YoshidaFactorTwoDiagonalPhysical
open YoshidaFactorTwoParityRealification
open YoshidaFactorTwoResidualDecomposition

/-!
# Exact signed factor-two real channels

The symmetric real factor-two cross is combined with the physical diagonal
without discarding the positive digamma residual.  Each signed channel is the
indefinite core plus one half of the complete structural residual energy of
the explicit test `g ± normalizedDilation 2 g`.
-/

private theorem tsum_bombieriDiagonalResidual_sub_dilation_two
    (g : BombieriTest) :
    (∑' n : ℕ, bombieriDiagonalResidual
        (g - normalizedDilation 2 (by norm_num) g) n) =
      2 * ((∑' n : ℕ, bombieriDiagonalResidual g n) -
        (∑' n : ℕ, bombieriResidualCross g
          (normalizedDilation 2 (by norm_num) g) n).re) := by
  have hg := summable_bombieriDiagonalResidual g
  have hd := summable_bombieriDiagonalResidual
    (normalizedDilation 2 (by norm_num) g)
  have hcross := summable_factorTwoResidualCross g
  have hcrossRe : Summable (fun n : ℕ ↦
      (bombieriResidualCross g
        (normalizedDilation 2 (by norm_num) g) n).re) := by
    change Summable (fun n : ℕ ↦ Complex.reCLM
      (bombieriResidualCross g
        (normalizedDilation 2 (by norm_num) g) n))
    exact Complex.reCLM.summable hcross
  have hscale :
      (∑' n : ℕ, 2 * (bombieriResidualCross g
          (normalizedDilation 2 (by norm_num) g) n).re) =
        2 * ∑' n : ℕ, (bombieriResidualCross g
          (normalizedDilation 2 (by norm_num) g) n).re :=
    (hcrossRe.hasSum.mul_left 2).tsum_eq
  have hsplit :
      (∑' n : ℕ,
          (bombieriDiagonalResidual g n +
            bombieriDiagonalResidual
              (normalizedDilation 2 (by norm_num) g) n -
            2 * (bombieriResidualCross g
              (normalizedDilation 2 (by norm_num) g) n).re)) =
        (∑' n : ℕ, bombieriDiagonalResidual g n) +
          (∑' n : ℕ, bombieriDiagonalResidual
            (normalizedDilation 2 (by norm_num) g) n) -
          2 * ∑' n : ℕ, (bombieriResidualCross g
            (normalizedDilation 2 (by norm_num) g) n).re := by
    calc
      _ = (∑' n : ℕ,
            (bombieriDiagonalResidual g n +
              bombieriDiagonalResidual
                (normalizedDilation 2 (by norm_num) g) n)) -
            ∑' n : ℕ, 2 * (bombieriResidualCross g
              (normalizedDilation 2 (by norm_num) g) n).re := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          (hg.add hd).tsum_sub (hcrossRe.mul_left 2)
      _ = _ := by
        rw [show (∑' n : ℕ,
              (bombieriDiagonalResidual g n +
                bombieriDiagonalResidual
                  (normalizedDilation 2 (by norm_num) g) n)) =
              (∑' n : ℕ, bombieriDiagonalResidual g n) +
                ∑' n : ℕ, bombieriDiagonalResidual
                  (normalizedDilation 2 (by norm_num) g) n by
            simpa only [Pi.add_apply] using hg.tsum_add hd,
          hscale]
  have hdilation :
      (∑' n : ℕ, bombieriDiagonalResidual
          (normalizedDilation 2 (by norm_num) g) n) =
        ∑' n : ℕ, bombieriDiagonalResidual g n := by
    apply tsum_congr
    intro n
    exact bombieriDiagonalResidual_normalizedDilation_two g n
  have hreal :
      (∑' n : ℕ, bombieriResidualCross g
        (normalizedDilation 2 (by norm_num) g) n).re =
        ∑' n : ℕ, (bombieriResidualCross g
          (normalizedDilation 2 (by norm_num) g) n).re := by
    change Complex.reCLM (∑' n : ℕ, bombieriResidualCross g
      (normalizedDilation 2 (by norm_num) g) n) = _
    simpa only [Function.comp_apply] using Complex.reCLM.map_tsum hcross
  calc
    (∑' n : ℕ, bombieriDiagonalResidual
        (g - normalizedDilation 2 (by norm_num) g) n) =
        ∑' n : ℕ,
          (bombieriDiagonalResidual g n +
            bombieriDiagonalResidual
              (normalizedDilation 2 (by norm_num) g) n -
            2 * (bombieriResidualCross g
              (normalizedDilation 2 (by norm_num) g) n).re) := by
      apply tsum_congr
      intro n
      exact bombieriDiagonalResidual_sub g
        (normalizedDilation 2 (by norm_num) g) n
    _ = _ := by
      rw [hsplit, hdilation, ← hreal]
      ring

private theorem tsum_bombieriDiagonalResidual_add_dilation_two
    (g : BombieriTest) :
    (∑' n : ℕ, bombieriDiagonalResidual
        (g + normalizedDilation 2 (by norm_num) g) n) =
      2 * ((∑' n : ℕ, bombieriDiagonalResidual g n) +
        (∑' n : ℕ, bombieriResidualCross g
          (normalizedDilation 2 (by norm_num) g) n).re) := by
  have hg := summable_bombieriDiagonalResidual g
  have hd := summable_bombieriDiagonalResidual
    (normalizedDilation 2 (by norm_num) g)
  have hcross := summable_factorTwoResidualCross g
  have hcrossRe : Summable (fun n : ℕ ↦
      (bombieriResidualCross g
        (normalizedDilation 2 (by norm_num) g) n).re) := by
    change Summable (fun n : ℕ ↦ Complex.reCLM
      (bombieriResidualCross g
        (normalizedDilation 2 (by norm_num) g) n))
    exact Complex.reCLM.summable hcross
  have hscale :
      (∑' n : ℕ, 2 * (bombieriResidualCross g
          (normalizedDilation 2 (by norm_num) g) n).re) =
        2 * ∑' n : ℕ, (bombieriResidualCross g
          (normalizedDilation 2 (by norm_num) g) n).re :=
    (hcrossRe.hasSum.mul_left 2).tsum_eq
  have hsplit :
      (∑' n : ℕ,
          (bombieriDiagonalResidual g n +
            bombieriDiagonalResidual
              (normalizedDilation 2 (by norm_num) g) n +
            2 * (bombieriResidualCross g
              (normalizedDilation 2 (by norm_num) g) n).re)) =
        (∑' n : ℕ, bombieriDiagonalResidual g n) +
          (∑' n : ℕ, bombieriDiagonalResidual
            (normalizedDilation 2 (by norm_num) g) n) +
          2 * ∑' n : ℕ, (bombieriResidualCross g
            (normalizedDilation 2 (by norm_num) g) n).re := by
    calc
      _ = (∑' n : ℕ,
            (bombieriDiagonalResidual g n +
              bombieriDiagonalResidual
                (normalizedDilation 2 (by norm_num) g) n)) +
            ∑' n : ℕ, 2 * (bombieriResidualCross g
              (normalizedDilation 2 (by norm_num) g) n).re := by
        simpa only [Pi.add_apply] using
          (hg.add hd).tsum_add (hcrossRe.mul_left 2)
      _ = _ := by
        rw [show (∑' n : ℕ,
              (bombieriDiagonalResidual g n +
                bombieriDiagonalResidual
                  (normalizedDilation 2 (by norm_num) g) n)) =
              (∑' n : ℕ, bombieriDiagonalResidual g n) +
                ∑' n : ℕ, bombieriDiagonalResidual
                  (normalizedDilation 2 (by norm_num) g) n by
            simpa only [Pi.add_apply] using hg.tsum_add hd,
          hscale]
  have hdilation :
      (∑' n : ℕ, bombieriDiagonalResidual
          (normalizedDilation 2 (by norm_num) g) n) =
        ∑' n : ℕ, bombieriDiagonalResidual g n := by
    apply tsum_congr
    intro n
    exact bombieriDiagonalResidual_normalizedDilation_two g n
  have hreal :
      (∑' n : ℕ, bombieriResidualCross g
        (normalizedDilation 2 (by norm_num) g) n).re =
        ∑' n : ℕ, (bombieriResidualCross g
          (normalizedDilation 2 (by norm_num) g) n).re := by
    change Complex.reCLM (∑' n : ℕ, bombieriResidualCross g
      (normalizedDilation 2 (by norm_num) g) n) = _
    simpa only [Function.comp_apply] using Complex.reCLM.map_tsum hcross
  calc
    (∑' n : ℕ, bombieriDiagonalResidual
        (g + normalizedDilation 2 (by norm_num) g) n) =
        ∑' n : ℕ,
          (bombieriDiagonalResidual g n +
            bombieriDiagonalResidual
              (normalizedDilation 2 (by norm_num) g) n +
            2 * (bombieriResidualCross g
              (normalizedDilation 2 (by norm_num) g) n).re) := by
      apply tsum_congr
      intro n
      exact bombieriDiagonalResidual_add g
        (normalizedDilation 2 (by norm_num) g) n
    _ = _ := by
      rw [hsplit, hdilation, ← hreal]
      ring

/-- The signed `D - R` channel is its exact core plus one half of the complete
positive residual energy of `g - normalizedDilation 2 g`. -/
theorem factorTwoDiagonalCoordinate_sub_symmetric_eq_coreResidual
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoDiagonalCoordinate g - factorTwoSymmetricCoordinate g =
      (bombieriCoreDiagonal g - (factorTwoCoreCrossSymbol g).re) +
        (1 / 2 : ℝ) * ∑' n : ℕ, bombieriDiagonalResidual
          (g - normalizedDilation 2 (by norm_num) g) n := by
  have hD : factorTwoDiagonalCoordinate g =
      bombieriCoreDiagonal g +
        ∑' n : ℕ, bombieriDiagonalResidual g n := by
    calc
      factorTwoDiagonalCoordinate g =
          (bombieriFunctional (bombieriQuadraticTest g)).re := by
        simpa only [factorTwoDiagonalCoordinate] using
          (bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
            g ha hab hsupport hratio).symm
      _ = (bombieriLocalCriticalForm g g).re := by
        rw [bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
          g ha hab hsupport hratio]
      _ = _ := bombieriLocalCriticalForm_self_re_eq_core_add_residual g
  have hR : factorTwoSymmetricCoordinate g =
      (factorTwoCoreCrossSymbol g).re +
        (∑' n : ℕ, bombieriResidualCross g
          (normalizedDilation 2 (by norm_num) g) n).re := by
    calc
      factorTwoSymmetricCoordinate g =
          (factorTwoGlobalCrossSymbol g).re := by
        simpa only [factorTwoSymmetricCoordinate] using
          (factorTwoGlobalCrossSymbol_re_eq_parity
            g ha hab hsupport hratio).symm
      _ = (factorTwoCoreCrossSymbol g +
          ∑' n : ℕ, bombieriResidualCross g
            (normalizedDilation 2 (by norm_num) g) n).re := by
        exact congrArg Complex.re
          (factorTwoGlobalCrossSymbol_eq_core_add_residual
            g ha hab hsupport hratio)
      _ = _ := by simp only [Complex.add_re]
  rw [hD, hR, tsum_bombieriDiagonalResidual_sub_dilation_two]
  ring

/-- The signed `D + R` channel is its exact core plus one half of the complete
positive residual energy of `g + normalizedDilation 2 g`. -/
theorem factorTwoDiagonalCoordinate_add_symmetric_eq_coreResidual
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoDiagonalCoordinate g + factorTwoSymmetricCoordinate g =
      (bombieriCoreDiagonal g + (factorTwoCoreCrossSymbol g).re) +
        (1 / 2 : ℝ) * ∑' n : ℕ, bombieriDiagonalResidual
          (g + normalizedDilation 2 (by norm_num) g) n := by
  have hD : factorTwoDiagonalCoordinate g =
      bombieriCoreDiagonal g +
        ∑' n : ℕ, bombieriDiagonalResidual g n := by
    calc
      factorTwoDiagonalCoordinate g =
          (bombieriFunctional (bombieriQuadraticTest g)).re := by
        simpa only [factorTwoDiagonalCoordinate] using
          (bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
            g ha hab hsupport hratio).symm
      _ = (bombieriLocalCriticalForm g g).re := by
        rw [bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
          g ha hab hsupport hratio]
      _ = _ := bombieriLocalCriticalForm_self_re_eq_core_add_residual g
  have hR : factorTwoSymmetricCoordinate g =
      (factorTwoCoreCrossSymbol g).re +
        (∑' n : ℕ, bombieriResidualCross g
          (normalizedDilation 2 (by norm_num) g) n).re := by
    calc
      factorTwoSymmetricCoordinate g =
          (factorTwoGlobalCrossSymbol g).re := by
        simpa only [factorTwoSymmetricCoordinate] using
          (factorTwoGlobalCrossSymbol_re_eq_parity
            g ha hab hsupport hratio).symm
      _ = (factorTwoCoreCrossSymbol g +
          ∑' n : ℕ, bombieriResidualCross g
            (normalizedDilation 2 (by norm_num) g) n).re := by
        exact congrArg Complex.re
          (factorTwoGlobalCrossSymbol_eq_core_add_residual
            g ha hab hsupport hratio)
      _ = _ := by simp only [Complex.add_re]
  rw [hD, hR, tsum_bombieriDiagonalResidual_add_dilation_two]
  ring

/-- Nonnegativity of the `D - R` channel is exactly the residual coercivity
bound for the minus test. -/
theorem factorTwoRealChannel_sub_nonneg_iff_coreResidual
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    0 ≤ factorTwoDiagonalCoordinate g - factorTwoSymmetricCoordinate g ↔
      -(bombieriCoreDiagonal g - (factorTwoCoreCrossSymbol g).re) ≤
        (1 / 2 : ℝ) * ∑' n : ℕ, bombieriDiagonalResidual
          (g - normalizedDilation 2 (by norm_num) g) n := by
  rw [factorTwoDiagonalCoordinate_sub_symmetric_eq_coreResidual
    g ha hab hsupport hratio]
  constructor <;> intro h <;> linarith

/-- Nonnegativity of the `D + R` channel is exactly the residual coercivity
bound for the plus test. -/
theorem factorTwoRealChannel_add_nonneg_iff_coreResidual
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    0 ≤ factorTwoDiagonalCoordinate g + factorTwoSymmetricCoordinate g ↔
      -(bombieriCoreDiagonal g + (factorTwoCoreCrossSymbol g).re) ≤
        (1 / 2 : ℝ) * ∑' n : ℕ, bombieriDiagonalResidual
          (g + normalizedDilation 2 (by norm_num) g) n := by
  rw [factorTwoDiagonalCoordinate_add_symmetric_eq_coreResidual
    g ha hab hsupport hratio]
  constructor <;> intro h <;> linarith

/-- The explicit scalar `c = -1` gives a negative production functional
exactly when the minus-channel residual coercivity is strictly reversed. -/
theorem bombieriFunctional_twoBump_neg_one_neg_iff_coreResidual
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (bombieriFunctional
      (bombieriQuadraticTest
        (g + (-1 : ℂ) • normalizedDilation 2 (by norm_num) g))).re < 0 ↔
      (1 / 2 : ℝ) * ∑' n : ℕ, bombieriDiagonalResidual
          (g - normalizedDilation 2 (by norm_num) g) n <
        -(bombieriCoreDiagonal g - (factorTwoCoreCrossSymbol g).re) := by
  have hformula := bombieriFunctional_twoBump_re
    g (-1 : ℂ) ha hab hsupport hratio
  have hD :=
    bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
      g ha hab hsupport hratio
  have hR := factorTwoGlobalCrossSymbol_re_eq_parity
    g ha hab hsupport hratio
  change (bombieriFunctional (bombieriQuadraticTest g)).re =
    factorTwoDiagonalCoordinate g at hD
  change (factorTwoGlobalCrossSymbol g).re =
    factorTwoSymmetricCoordinate g at hR
  have htwo :
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + (-1 : ℂ) • normalizedDilation 2 (by norm_num) g))).re =
        2 * (factorTwoDiagonalCoordinate g -
          factorTwoSymmetricCoordinate g) := by
    rw [hformula, hD]
    simp only [Complex.normSq_neg, Complex.normSq_one, neg_one_mul,
      Complex.neg_re]
    rw [hR]
    ring
  rw [htwo,
    factorTwoDiagonalCoordinate_sub_symmetric_eq_coreResidual
      g ha hab hsupport hratio]
  constructor <;> intro h <;> linarith

/-- The explicit scalar `c = 1` gives a negative production functional
exactly when the plus-channel residual coercivity is strictly reversed. -/
theorem bombieriFunctional_twoBump_one_neg_iff_coreResidual
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (bombieriFunctional
      (bombieriQuadraticTest
        (g + (1 : ℂ) • normalizedDilation 2 (by norm_num) g))).re < 0 ↔
      (1 / 2 : ℝ) * ∑' n : ℕ, bombieriDiagonalResidual
          (g + normalizedDilation 2 (by norm_num) g) n <
        -(bombieriCoreDiagonal g + (factorTwoCoreCrossSymbol g).re) := by
  have hformula := bombieriFunctional_twoBump_re
    g (1 : ℂ) ha hab hsupport hratio
  have hD :=
    bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
      g ha hab hsupport hratio
  have hR := factorTwoGlobalCrossSymbol_re_eq_parity
    g ha hab hsupport hratio
  change (bombieriFunctional (bombieriQuadraticTest g)).re =
    factorTwoDiagonalCoordinate g at hD
  change (factorTwoGlobalCrossSymbol g).re =
    factorTwoSymmetricCoordinate g at hR
  have htwo :
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + (1 : ℂ) • normalizedDilation 2 (by norm_num) g))).re =
        2 * (factorTwoDiagonalCoordinate g +
          factorTwoSymmetricCoordinate g) := by
    rw [hformula, hD]
    simp only [Complex.normSq_one, one_mul]
    rw [hR]
    ring
  rw [htwo,
    factorTwoDiagonalCoordinate_add_symmetric_eq_coreResidual
      g ha hab hsupport hratio]
  constructor <;> intro h <;> linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoRealChannel
