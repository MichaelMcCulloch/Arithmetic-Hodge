import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual
import ArithmeticHodge.Analysis.YoshidaFourCellEvenCapacityStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshRegularStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshCoupledCoreStructural

noncomputable section

open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFourCellEvenCapacityStructural
open YoshidaFourCellEvenZeroCoshRegularStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellParityHalfFoldStructural

/-!
# The infinite even tail of the zero-cosh coupled core

The adverse endpoint translation and the logarithmic endpoint potential are
kept as one positive capacity block.  Once the `P₀/P₂/P₄` coordinates
have been removed, the sixth shifted-Legendre harmonic gap alone is already
strictly stronger than the `33 / 20` coupled-core target.  Thus the unresolved
part of the zero-cosh problem is a finite low block and its cross with this
infinite tail, rather than the tail itself.
-/

private theorem upperStripPotential_le_fullPotential_of_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    2 * (∫ x : ℝ in 3 / 5..1,
        yoshidaEndpointPotential x * w x ^ 2) ≤
      ∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * w x ^ 2 := by
  let g : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * w x ^ 2
  have hgFull : IntervalIntegrable g volume (-1) 1 := by
    simpa only [g] using intervalIntegrable_endpointPotential_mul_sq w hw
  have hgEven : Function.Even g := by
    intro x
    dsimp only [g, yoshidaEndpointPotential]
    rw [heven x]
    ring_nf
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    g hgFull hgEven
  have hleft : IntervalIntegrable g volume 0 (3 / 5) := by
    apply hgFull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hright : IntervalIntegrable g volume (3 / 5) 1 := by
    apply hgFull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hleftNonneg : 0 ≤ ∫ x : ℝ in 0..3 / 5, g x := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_nonneg (yoshidaEndpointPotential_nonneg_on_Icc hxIcc)
      (sq_nonneg _)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  dsimp only [g] at hfold hsplit hleftNonneg ⊢
  linarith

/-- On an even profile, the exact endpoint potential pays the exact retained
dyadic translation while leaving a strict positive strip reserve. -/
theorem endpointPotential_sub_dyadicPairing_nonnegative
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    0 ≤ (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * w x ^ 2) -
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  let S : ℝ := ∫ x : ℝ in 3 / 5..1,
    yoshidaEndpointPotential x * w x ^ 2
  let V : ℝ := ∫ x : ℝ in -1..1,
    yoshidaEndpointPotential x * w x ^ 2
  let P : ℝ := Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w
  have hprime : P ≤ (99 / 50 : ℝ) * S := by
    simpa only [P, S] using
      fourCell_dyadicPairing_le_endpointStripPotential w hw heven
  have hstrip : 2 * S ≤ V := by
    simpa only [S, V] using
      upperStripPotential_le_fullPotential_of_even w hw heven
  have hS : 0 ≤ S := by
    dsimp only [S]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_nonneg (yoshidaEndpointPotential_nonneg_on_Icc hxIcc)
      (sq_nonneg _)
  change 0 ≤ V - P
  nlinarith

/-- The complete infinite even tail above `P₄` satisfies the actual
`33 / 20` coupled-core inequality.  The proof uses the sixth harmonic gap
for all higher modes at once and retains the prime/potential pair as the
exact positive endpoint-capacity block. -/
theorem thirtyThree_div_twenty_mass_le_coupledCore_of_even_legendreTail
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hlow : centeredLegendreMomentsVanishBelow w 6) :
    (33 / 20 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore w := by
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let B : ℝ := (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hB : 0 ≤ B := by
    simpa only [B] using
      endpointPotential_sub_dyadicPairing_nonnegative w hw heven
  have hraw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    w hw hlocal 6 hlow
  norm_num [harmonic, Finset.sum_range_succ] at hraw
  have hgap : (49 / 20 : ℝ) * M ≤ centeredRawLogEnergy w / 4 := by
    simpa only [M, factorTwoIntrinsicEnergy] using hraw
  unfold fourCellEvenZeroCoshCoupledCore
  dsimp only [M, B] at hgap hB ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshCoupledCoreStructural
