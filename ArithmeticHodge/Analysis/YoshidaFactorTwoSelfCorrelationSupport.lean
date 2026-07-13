import ArithmeticHodge.Analysis.YoshidaFactorTwoCenteredPhysical

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoSelfCorrelationSupport

noncomputable section

open MultiplicativeWeil
open YoshidaCriticalLogCorrelation
open YoshidaFactorTwoAdjacentSchwartz
open YoshidaFactorTwoCrossDistribution

/-!
# Support and regularity of the factor-two self-correlation

For a seed whose multiplicative support ratio is at most two, the critical
logarithmic pullback occupies an interval of length at most `log 2`.  Its
self-correlation is therefore smooth, supported on the symmetric interval
`[-log 2, log 2]`, and vanishes at both endpoints.
-/

theorem factorTwoSelfCorrelation_contDiff
    (g : BombieriTest) (n : ℕ∞) :
    ContDiff ℝ n (factorTwoSelfCorrelation g) := by
  have hcomp := (factorTwoAdjacentCorrelation_contDiff g n).comp
    (show ContDiff ℝ n (fun s : ℝ ↦ s + factorTwoLogLength) by fun_prop)
  convert hcomp using 1
  funext s
  change factorTwoSelfCorrelation g s =
    factorTwoAdjacentCorrelation g (s + factorTwoLogLength)
  rw [factorTwoAdjacentCorrelation_eq_shift]
  congr 2
  ring

theorem factorTwoSelfCorrelation_eq_zero_outside
    (g : BombieriTest) {a b s : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hs : s ∉ Set.Icc (-factorTwoLogLength) factorTwoLogLength) :
    factorTwoSelfCorrelation g s = 0 := by
  have hshiftOutside :
      s + factorTwoLogLength ∉
        Set.Icc 0 (2 * factorTwoLogLength) := by
    intro hmem
    apply hs
    exact ⟨(by linarith [hmem.1]), (by linarith [hmem.2])⟩
  have hzero := factorTwoAdjacentCorrelation_eq_zero_outside
    g ha hab hsupport hratio hshiftOutside
  rw [factorTwoAdjacentCorrelation_eq_shift] at hzero
  simpa only [add_sub_cancel_right] using hzero

theorem factorTwoSelfCorrelation_neg_length_eq_zero
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoSelfCorrelation g (-factorTwoLogLength) = 0 := by
  have hzero := factorTwoAdjacentCorrelation_zero
    g ha hab hsupport hratio
  rw [factorTwoAdjacentCorrelation_eq_shift] at hzero
  simpa only [zero_sub] using hzero

theorem factorTwoSelfCorrelation_length_eq_zero
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoSelfCorrelation g factorTwoLogLength = 0 := by
  have hneg := factorTwoSelfCorrelation_neg_length_eq_zero
    g ha hab hsupport hratio
  have hsym := factorTwoSelfCorrelation_neg g (-factorTwoLogLength)
  rw [neg_neg, hneg] at hsym
  simpa only [map_zero] using hsym

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoSelfCorrelationSupport
