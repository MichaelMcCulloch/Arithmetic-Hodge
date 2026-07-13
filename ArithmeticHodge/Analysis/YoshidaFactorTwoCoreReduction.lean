import ArithmeticHodge.Analysis.YoshidaFactorTwoResidualDecomposition

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoCoreReduction

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaBombieriDiagonalResidual
open YoshidaBombieriResidualPairing
open YoshidaFactorTwoMomentFormula
open YoshidaFactorTwoResidualDecomposition
open MultiplicativeWeilRestrictedSupportEndpointPositive

/-!
# Reduction of the factor-two determinant to its structural core

The positive infinite digamma residual is split off simultaneously from the
diagonal and adjacent cross.  What remains keeps the growing polar channel,
the initial Cauchy channel, the mass constant, and both prime atoms in their
exact cancellation-preserving combination.
-/

def bombieriCoreDiagonalSymbol (g : BombieriTest) : ℂ :=
  star (mellin (g : ℝ → ℂ) 1) * mellin (g : ℝ → ℂ) 0 +
    star (mellin (g : ℝ → ℂ) 0) * mellin (g : ℝ → ℂ) 1 -
    bombieriCauchyCrossValue g g 0 -
    (Real.eulerMascheroniConstant : ℂ) *
      bombieriCriticalCrossCorrelation g g 0 -
    (Real.log Real.pi : ℂ) * bombieriCriticalCrossCorrelation g g 0

def bombieriCoreDiagonal (g : BombieriTest) : ℝ :=
  (bombieriCoreDiagonalSymbol g).re

def factorTwoCoreCrossSymbol (g : BombieriTest) : ℂ :=
  factorTwoGrowingMomentSymbol g - factorTwoPrimeCrossSymbol g

theorem bombieriLocalCriticalForm_self_eq_core_add_residual
    (g : BombieriTest) :
    bombieriLocalCriticalForm g g =
      bombieriCoreDiagonalSymbol g +
        ((∑' n : ℕ, bombieriDiagonalResidual g n : ℝ) : ℂ) := by
  have hcritical :
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, bombieriLocalCriticalCrossIntegrand g g v) =
        bombieriCrossDigammaCauchySeriesValue g g := by
    simpa only [bombieriLocalCriticalCrossIntegrand,
      bombieriCriticalSpectralProduct, mellinLinearMap_apply, mul_assoc] using
      normalized_localCriticalKernel_crossProduct_eq_cauchySeries g g
  rw [bombieriLocalCriticalForm_apply]
  unfold bombieriLocalCriticalPairing
  rw [hcritical]
  unfold bombieriCrossDigammaCauchySeriesValue
  rw [cauchySeries_eq_neg_ofReal_tsum_bombieriDiagonalResidual]
  unfold bombieriCoreDiagonalSymbol
  simp only [mellinLinearMap_apply]
  ring

theorem bombieriLocalCriticalForm_self_re_eq_core_add_residual
    (g : BombieriTest) :
    (bombieriLocalCriticalForm g g).re =
      bombieriCoreDiagonal g +
        ∑' n : ℕ, bombieriDiagonalResidual g n := by
  rw [bombieriLocalCriticalForm_self_eq_core_add_residual]
  simp only [add_re, ofReal_re, bombieriCoreDiagonal]

theorem factorTwoGlobalCrossSymbol_eq_core_add_residual
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoGlobalCrossSymbol g =
      factorTwoCoreCrossSymbol g +
        ∑' n : ℕ, bombieriResidualCross g
          (normalizedDilation 2 (by norm_num) g) n := by
  rw [factorTwoGlobalCrossSymbol_eq_moment_sub_prime
    g ha hab hsupport hratio]
  rw [tsum_factorTwoResidualCross_eq_neg_tailMoment
    g ha hab hsupport hratio]
  unfold factorTwoCoreCrossSymbol
  ring

theorem norm_factorTwoGlobalCrossSymbol_le_local_of_core
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcore : ‖factorTwoCoreCrossSymbol g‖ ≤ bombieriCoreDiagonal g) :
    ‖factorTwoGlobalCrossSymbol g‖ ≤
      (bombieriLocalCriticalForm g g).re := by
  rw [factorTwoGlobalCrossSymbol_eq_core_add_residual
    g ha hab hsupport hratio]
  calc
    ‖factorTwoCoreCrossSymbol g +
        ∑' n : ℕ, bombieriResidualCross g
          (normalizedDilation 2 (by norm_num) g) n‖ ≤
        ‖factorTwoCoreCrossSymbol g‖ +
          ‖∑' n : ℕ, bombieriResidualCross g
            (normalizedDilation 2 (by norm_num) g) n‖ := norm_add_le _ _
    _ ≤ bombieriCoreDiagonal g +
        ∑' n : ℕ, bombieriDiagonalResidual g n :=
      add_le_add hcore (norm_tsum_factorTwoResidualCross_le g)
    _ = (bombieriLocalCriticalForm g g).re :=
      (bombieriLocalCriticalForm_self_re_eq_core_add_residual g).symm

theorem factorTwoDeterminant_le_of_core
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcore : ‖factorTwoCoreCrossSymbol g‖ ≤ bombieriCoreDiagonal g) :
    Complex.normSq (factorTwoGlobalCrossSymbol g) ≤
      (bombieriFunctional (bombieriQuadraticTest g)).re ^ 2 := by
  have hnorm := norm_factorTwoGlobalCrossSymbol_le_local_of_core
    g ha hab hsupport hratio hcore
  have hdiag : 0 ≤ (bombieriLocalCriticalForm g g).re := by
    rw [← bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
      g ha hab hsupport hratio]
    exact bombieriFunctional_quadratic_re_nonneg_of_ratio_le_two
      g ha hab hsupport hratio
  rw [Complex.normSq_eq_norm_sq]
  rw [bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
    g ha hab hsupport hratio]
  exact (sq_le_sq₀ (norm_nonneg _) hdiag).2 hnorm

theorem bombieriFunctional_twoBump_nonneg_of_core
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcore : ‖factorTwoCoreCrossSymbol g‖ ≤ bombieriCoreDiagonal g) :
    ∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re := by
  rw [bombieriFunctional_twoBump_nonneg_iff
    g ha hab hsupport hratio]
  exact factorTwoDeterminant_le_of_core
    g ha hab hsupport hratio hcore

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoCoreReduction
