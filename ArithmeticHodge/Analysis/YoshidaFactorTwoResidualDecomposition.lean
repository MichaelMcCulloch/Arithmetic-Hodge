import ArithmeticHodge.Analysis.YoshidaFactorTwoMomentFormula
import ArithmeticHodge.Analysis.YoshidaBombieriResidualPairing

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoResidualDecomposition

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaBombieriDiagonalResidual
open YoshidaBombieriResidualPairing
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoMomentFormula

/-!
# Positive-residual decomposition of the factor-two tail

The entire decaying moment tail is the cross term of the positive diagonal
residual family.  Normalized factor-two dilation preserves each residual
diagonal, so Cauchy--Schwarz controls the full tail by the corresponding
summed diagonal energy.
-/

theorem factorTwoMellinPhase_normSq (v : ℝ) :
    Complex.normSq (factorTwoMellinPhase v) = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  simp [factorTwoMellinPhase]

theorem bombieriDiagonalResidual_normalizedDilation_two
    (g : BombieriTest) (n : ℕ) :
    bombieriDiagonalResidual (normalizedDilation 2 (by norm_num) g) n =
      bombieriDiagonalResidual g n := by
  unfold bombieriDiagonalResidual
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  unfold bombieriDiagonalResidualIntegrand
  congr 1
  rw [mellin_normalizedDilation_two_vertical g (1 / 2) v]
  rw [factorTwoMellinWeight_half, one_mul, Complex.normSq_mul,
    factorTwoMellinPhase_normSq, one_mul]

theorem factorTwoResidualCross_eq_neg_tailTerm
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) (k : ℕ) :
    bombieriResidualCross g
        (normalizedDilation 2 (by norm_num) g) k =
      -factorTwoTailMomentTerm g k := by
  have hzero : bombieriCriticalCrossCorrelation g
      (normalizedDilation 2 (by norm_num) g) 0 = 0 := by
    simpa only [factorTwoAdjacentCorrelation] using
      factorTwoAdjacentCorrelation_zero g ha hab hsupport hratio
  rw [bombieriResidualCross_eq_cauchyResidual, hzero, mul_zero, zero_sub]
  rw [bombieriCauchyCrossValue_dilation_two_eq_moment
    g ha hab hsupport hratio (k + 1)]
  rfl

theorem tsum_factorTwoResidualCross_eq_neg_tailMoment
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∑' k : ℕ, bombieriResidualCross g
        (normalizedDilation 2 (by norm_num) g) k) =
      -factorTwoTailMomentSymbol g := by
  rw [factorTwoTailMomentSymbol, ← tsum_neg]
  apply tsum_congr
  intro k
  exact factorTwoResidualCross_eq_neg_tailTerm
    g ha hab hsupport hratio k

theorem norm_bombieriResidualCross_dilation_two_le
    (g : BombieriTest) (n : ℕ) :
    ‖bombieriResidualCross g
        (normalizedDilation 2 (by norm_num) g) n‖ ≤
      bombieriDiagonalResidual g n := by
  have hcs := normSq_bombieriResidualCross_le g
    (normalizedDilation 2 (by norm_num) g) n
  rw [bombieriDiagonalResidual_normalizedDilation_two] at hcs
  rw [Complex.normSq_eq_norm_sq] at hcs
  have hnorm := norm_nonneg (bombieriResidualCross g
    (normalizedDilation 2 (by norm_num) g) n)
  have hres := bombieriDiagonalResidual_nonneg g n
  nlinarith

theorem summable_factorTwoResidualCross (g : BombieriTest) :
    Summable (fun n : ℕ ↦ bombieriResidualCross g
      (normalizedDilation 2 (by norm_num) g) n) := by
  apply (summable_bombieriDiagonalResidual g).of_norm_bounded
  exact norm_bombieriResidualCross_dilation_two_le g

theorem norm_tsum_factorTwoResidualCross_le (g : BombieriTest) :
    ‖∑' n : ℕ, bombieriResidualCross g
        (normalizedDilation 2 (by norm_num) g) n‖ ≤
      ∑' n : ℕ, bombieriDiagonalResidual g n := by
  have hcross := summable_factorTwoResidualCross g
  calc
    ‖∑' n : ℕ, bombieriResidualCross g
        (normalizedDilation 2 (by norm_num) g) n‖ ≤
        ∑' n : ℕ, ‖bombieriResidualCross g
          (normalizedDilation 2 (by norm_num) g) n‖ :=
      norm_tsum_le_tsum_norm hcross.norm
    _ ≤ ∑' n : ℕ, bombieriDiagonalResidual g n :=
      hcross.norm.tsum_le_tsum
        (norm_bombieriResidualCross_dilation_two_le g)
        (summable_bombieriDiagonalResidual g)

theorem norm_factorTwoTailMomentSymbol_le_residualSum
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    ‖factorTwoTailMomentSymbol g‖ ≤
      ∑' n : ℕ, bombieriDiagonalResidual g n := by
  calc
    ‖factorTwoTailMomentSymbol g‖ =
        ‖-factorTwoTailMomentSymbol g‖ := (norm_neg _).symm
    _ = ‖∑' n : ℕ, bombieriResidualCross g
        (normalizedDilation 2 (by norm_num) g) n‖ := by
      exact congrArg norm
        (tsum_factorTwoResidualCross_eq_neg_tailMoment
          g ha hab hsupport hratio).symm
    _ ≤ _ := norm_tsum_factorTwoResidualCross_le g

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoResidualDecomposition
