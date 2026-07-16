import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenQuantitativeStructural

open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open TwoByTwoSchur

noncomputable section

/-!
# A retained reserve on the structural `P6/P7` phase block

The standalone two-mode theorem has more diagonal coercivity than its
alternating entry spends.  This module keeps a uniform `1 / 100` share of
both mode energies for the later low--residual Schur complement.  The proof
uses only the exact two-mode expansion and one scalar Schur inequality.
-/

/-- After paying the complete `P6/P7` alternating entry, the two-mode phase
retains one hundredth of each scaled mode energy on the whole phase disk. -/
theorem one_hundredth_energy_sum_le_P6_P7_phase
    (c d a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (1 / 100 : ℝ) *
        (factorTwoIntrinsicEnergy factorTwoCenteredP6 * c ^ 2 +
          factorTwoIntrinsicEnergy factorTwoCenteredP7 * d ^ 2) ≤
      factorTwoEndpointChannelPhase
        (fun x ↦ c * factorTwoCenteredP6 x)
        (fun x ↦ d * factorTwoCenteredP7 x) a b := by
  have ha : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
  have hb : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  have hD6 := one_twentieth_energy_le_P6_phase_diagonal a ha
  have hD7 := nine_fiftieths_energy_le_P7_phase_diagonal a ha
  have hJ := factorTwoP67Alternating_sq_le_energy_product
  let E6 := factorTwoIntrinsicEnergy factorTwoCenteredP6
  let E7 := factorTwoIntrinsicEnergy factorTwoCenteredP7
  let A := factorTwoP6PhaseDiagonal a - (1 / 100 : ℝ) * E6
  let B := factorTwoP7PhaseDiagonal a - (1 / 100 : ℝ) * E7
  have hE6 : 0 ≤ E6 := by
    dsimp only [E6]
    exact factorTwoIntrinsicEnergy_nonneg factorTwoCenteredP6
  have hE7 : 0 ≤ E7 := by
    dsimp only [E7]
    exact factorTwoIntrinsicEnergy_nonneg factorTwoCenteredP7
  have hA : (1 / 25 : ℝ) * E6 ≤ A := by
    dsimp only [A, E6]
    linarith
  have hB : (17 / 100 : ℝ) * E7 ≤ B := by
    dsimp only [B, E7]
    linarith
  have hA0 : 0 ≤ A :=
    (mul_nonneg (by norm_num) hE6).trans hA
  have hB0 : 0 ≤ B :=
    (mul_nonneg (by norm_num) hE7).trans hB
  have hbJ : (b * factorTwoP67Alternating) ^ 2 ≤
      factorTwoP67Alternating ^ 2 := by
    rw [mul_pow]
    have hmul := mul_le_mul_of_nonneg_right hb
      (sq_nonneg factorTwoP67Alternating)
    nlinarith
  have hcoefficient :
      (b * factorTwoP67Alternating) ^ 2 ≤ 4 * A * B := by
    have hAB :
        ((1 / 25 : ℝ) * E6) * ((17 / 100 : ℝ) * E7) ≤ A * B :=
      mul_le_mul hA hB (mul_nonneg (by norm_num) hE7) hA0
    have hJ' : factorTwoP67Alternating ^ 2 ≤
        (9 / 400 : ℝ) * E6 * E7 := by
      simpa only [E6, E7] using hJ
    nlinarith [mul_nonneg hE6 hE7]
  let low := A * c ^ 2
  let tail := B * d ^ 2
  let mixed := (b * factorTwoP67Alternating * c * d) / 2
  have hlow : 0 ≤ low := by
    dsimp only [low]
    positivity
  have htail : 0 ≤ tail := by
    dsimp only [tail]
    positivity
  have hscaled := mul_le_mul_of_nonneg_right hcoefficient
    (mul_nonneg (sq_nonneg c) (sq_nonneg d))
  have hschur : mixed ^ 2 ≤ low * tail := by
    dsimp only [mixed, low, tail]
    nlinarith
  have hnonneg := scalar_low_tail_nonneg
    low tail mixed hlow htail hschur
  rw [factorTwoEndpointChannelPhase_P6_P7_expansion]
  dsimp only [low, tail, mixed, A, B, E6, E7] at hnonneg ⊢
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenQuantitativeStructural
