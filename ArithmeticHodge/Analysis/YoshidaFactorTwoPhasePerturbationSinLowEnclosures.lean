import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationSinEnclosures
import ArithmeticHodge.Analysis.YoshidaSineCheckpointedHead
import ArithmeticHodge.Analysis.RationalIntervalWidth
import ArithmeticHodge.Analysis.CauchyKernelFiniteSumBounds
import ArithmeticHodge.Analysis.YoshidaSineCheckpointStructuralWidth
import ArithmeticHodge.Analysis.YoshidaSineStructuralWidth

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open scoped BigOperators
open Filter Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationSinLowEnclosures

noncomputable section

open ArithmeticHodge.Analysis
open CauchyKernelFiniteSumBounds
open RatInterval
open YoshidaCauchyTailBounds
open YoshidaEvenCouplingReduction
open YoshidaEvenSineHighEnclosures
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcretePerturbationMoments
open YoshidaFactorTwoPhasePerturbationConstantEnclosures
open YoshidaFactorTwoPhasePerturbationMomentSeries
open YoshidaFactorTwoPhasePerturbationSinEnclosures
open YoshidaFactorTwoPrimeTrigEnclosures
open YoshidaMomentSeries
open YoshidaOddGramPrefix
open YoshidaSineCheckpointedHead
open YoshidaSineCheckpointStructuralWidth
open YoshidaSineAcceleratedTail
open YoshidaSineMomentEnclosures
open YoshidaSineSeriesTail
open YoshidaSineStructuralWidth

/-!
# Low-mode factor-two symmetric sine enclosures

The high-mode file uses a cubic asymptotic box for the slow digamma sample.
For low modes we instead solve the established Yoshida sine identity for that
sample.  Its Cauchy series is enclosed by checkpointed finite heads and the
accelerated analytic tail, while the dyadic corrections retain their compact
geometric enclosures.
-/

/-! ## Tight reciprocal-power tails -/

/-- Euler--Maclaurin upper potential through the `B₂` term. -/
def tightInvPowUpperPotential (x : ℝ) (p : ℕ) (j : ℕ) : ℝ :=
  (((p - 1 : ℕ) : ℝ))⁻¹ * shiftedInvPow x (p - 1) j +
    (1 / 2 : ℝ) * shiftedInvPow x p j +
    ((p : ℝ) / 12) * shiftedInvPow x (p + 1) j

/-- Alternating Euler--Maclaurin lower potential through the `B₄` term. -/
def tightInvPowLowerPotential (x : ℝ) (p : ℕ) (j : ℕ) : ℝ :=
  tightInvPowUpperPotential x p j -
    (((p * (p + 1) * (p + 2) : ℕ) : ℝ) / 720) *
      shiftedInvPow x (p + 3) j

private theorem summable_shiftedInvPow_tight
    {x : ℝ} (hx : 0 < x) {p : ℕ} (hp : 1 < p) :
    Summable (shiftedInvPow x p) := by
  have hs := (Real.summable_one_div_nat_add_rpow x (p : ℝ)).2 (by
    exact_mod_cast hp)
  apply hs.congr
  intro j
  rw [shiftedInvPow, abs_of_pos (by positivity : 0 < (j : ℝ) + x),
    Real.rpow_natCast]
  congr 2
  ring

private theorem tendsto_inv_shifted_pow
    (x : ℝ) {p : ℕ} (hp : 0 < p) :
    Tendsto (fun j : ℕ ↦ 1 / (x + j) ^ p) atTop (nhds 0) := by
  have htop : Tendsto (fun j : ℕ ↦ x + (j : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv : Tendsto (fun j : ℕ ↦ (x + (j : ℝ))⁻¹)
      atTop (nhds 0) := by
    simpa only [one_div] using htop.const_div_atTop 1
  have hpow := hinv.pow p
  convert hpow using 1
  · funext j
    rw [one_div, inv_pow]
  · simp [hp.ne']

private theorem tendsto_tightInvPowUpperPotential
    (x : ℝ) {p : ℕ} (hp : 1 < p) :
    Tendsto (tightInvPowUpperPotential x p) atTop (nhds 0) := by
  have h1 := (tendsto_inv_shifted_pow x (Nat.sub_pos_of_lt hp)).const_mul
    (((p - 1 : ℕ) : ℝ))⁻¹
  have h2 := (tendsto_inv_shifted_pow x (by omega : 0 < p)).const_mul
    (1 / 2 : ℝ)
  have h3 := (tendsto_inv_shifted_pow x (by omega : 0 < p + 1)).const_mul
    ((p : ℝ) / 12)
  change Tendsto
    (fun j : ℕ ↦ (((p - 1 : ℕ) : ℝ))⁻¹ * shiftedInvPow x (p - 1) j +
      (1 / 2 : ℝ) * shiftedInvPow x p j +
      ((p : ℝ) / 12) * shiftedInvPow x (p + 1) j) atTop (nhds 0)
  simpa only [shiftedInvPow, mul_zero, add_zero] using (h1.add h2).add h3

private theorem tendsto_tightInvPowLowerPotential
    (x : ℝ) {p : ℕ} (hp : 1 < p) :
    Tendsto (tightInvPowLowerPotential x p) atTop (nhds 0) := by
  have hu := tendsto_tightInvPowUpperPotential x hp
  have hr := (tendsto_inv_shifted_pow x (by omega : 0 < p + 3)).const_mul
    (((p * (p + 1) * (p + 2) : ℕ) : ℝ) / 720)
  change Tendsto
    (fun j : ℕ ↦ tightInvPowUpperPotential x p j -
      (((p * (p + 1) * (p + 2) : ℕ) : ℝ) / 720) *
        shiftedInvPow x (p + 3) j) atTop (nhds 0)
  simpa only [shiftedInvPow, mul_zero, sub_zero] using hu.sub hr

private theorem tightInvPowLowerPotential_sub_succ_le
    {x : ℝ} (hx : 1 ≤ x) {p : ℕ}
    (hp : p = 2 ∨ p = 4 ∨ p = 6 ∨ p = 8 ∨ p = 10) (j : ℕ) :
    tightInvPowLowerPotential x p j -
        tightInvPowLowerPotential x p (j + 1) ≤
      shiftedInvPow x p j := by
  let a : ℝ := x + j
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha1 : 0 < a + 1 := by positivity
  have haOne : 1 ≤ a := by
    dsimp only [a]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  unfold tightInvPowLowerPotential tightInvPowUpperPotential shiftedInvPow
  rw [show x + (j : ℝ) = a by rfl,
    show x + ((j + 1 : ℕ) : ℝ) = a + 1 by
      dsimp only [a]
      push_cast
      ring]
  rcases hp with (rfl | rfl | rfl | rfl | rfl) <;>
    dsimp <;>
    push_cast <;>
    field_simp [ha.ne', ha1.ne'] <;>
    ring_nf
  all_goals nlinarith [sq_nonneg (a - 1), sq_nonneg a,
    sq_nonneg (a ^ 2), sq_nonneg (a ^ 3), sq_nonneg (a ^ 4)]

private theorem shiftedInvPow_le_tightUpperPotential_sub_succ
    {x : ℝ} (hx : 1 ≤ x) {p : ℕ}
    (hp : p = 2 ∨ p = 4 ∨ p = 6 ∨ p = 8 ∨ p = 10) (j : ℕ) :
    shiftedInvPow x p j ≤
      tightInvPowUpperPotential x p j -
        tightInvPowUpperPotential x p (j + 1) := by
  let a : ℝ := x + j
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha1 : 0 < a + 1 := by positivity
  have haOne : 1 ≤ a := by
    dsimp only [a]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  unfold tightInvPowUpperPotential shiftedInvPow
  rw [show x + (j : ℝ) = a by rfl,
    show x + ((j + 1 : ℕ) : ℝ) = a + 1 by
      dsimp only [a]
      push_cast
      ring]
  rcases hp with (rfl | rfl | rfl | rfl | rfl) <;>
    dsimp <;>
    push_cast <;>
    field_simp [ha.ne', ha1.ne'] <;>
    ring_nf
  all_goals nlinarith [sq_nonneg (a - 1), sq_nonneg a,
    sq_nonneg (a ^ 2), sq_nonneg (a ^ 3), sq_nonneg (a ^ 4)]

private theorem tightInvPow_tsum_bounds
    {x : ℝ} (hx : 1 ≤ x) {p : ℕ}
    (hp : p = 2 ∨ p = 4 ∨ p = 6 ∨ p = 8 ∨ p = 10) :
    tightInvPowLowerPotential x p 0 ≤
        ∑' j : ℕ, shiftedInvPow x p j ∧
      (∑' j : ℕ, shiftedInvPow x p j) ≤
        tightInvPowUpperPotential x p 0 := by
  have hp1 : 1 < p := by rcases hp with (rfl | rfl | rfl | rfl | rfl) <;> omega
  have hs := summable_shiftedInvPow_tight (lt_of_lt_of_le (by norm_num) hx) hp1
  have hpartialLower (N : ℕ) :
      tightInvPowLowerPotential x p 0 - tightInvPowLowerPotential x p N ≤
        ∑ j ∈ Finset.range N, shiftedInvPow x p j := by
    rw [← Finset.sum_range_sub' (tightInvPowLowerPotential x p)]
    exact Finset.sum_le_sum fun j _ ↦
      tightInvPowLowerPotential_sub_succ_le hx hp j
  have hpartialUpper (N : ℕ) :
      (∑ j ∈ Finset.range N, shiftedInvPow x p j) ≤
        tightInvPowUpperPotential x p 0 - tightInvPowUpperPotential x p N := by
    rw [← Finset.sum_range_sub' (tightInvPowUpperPotential x p)]
    exact Finset.sum_le_sum fun j _ ↦
      shiftedInvPow_le_tightUpperPotential_sub_succ hx hp j
  have hsum := hs.hasSum.tendsto_sum_nat
  have hlo : Tendsto
      (fun N : ℕ ↦ tightInvPowLowerPotential x p 0 -
        tightInvPowLowerPotential x p N) atTop
      (nhds (tightInvPowLowerPotential x p 0)) := by
    simpa using (tendsto_const_nhds.sub
      (tendsto_tightInvPowLowerPotential x hp1))
  have hup : Tendsto
      (fun N : ℕ ↦ tightInvPowUpperPotential x p 0 -
        tightInvPowUpperPotential x p N) atTop
      (nhds (tightInvPowUpperPotential x p 0)) := by
    simpa using (tendsto_const_nhds.sub
      (tendsto_tightInvPowUpperPotential x hp1))
  exact ⟨le_of_tendsto_of_tendsto (by simpa using hlo) hsum
      (Filter.Eventually.of_forall hpartialLower),
    le_of_tendsto_of_tendsto hsum (by simpa using hup)
      (Filter.Eventually.of_forall hpartialUpper)⟩

/-! ## Ninth-order Cauchy acceleration -/

def higherCauchyMainLower (x y : ℝ) (j : ℕ) : ℝ :=
  y * shiftedInvPow x 2 j - y ^ 3 * shiftedInvPow x 4 j +
    y ^ 5 * shiftedInvPow x 6 j - y ^ 7 * shiftedInvPow x 8 j

def higherCauchyMainUpper (x y : ℝ) (j : ℕ) : ℝ :=
  higherCauchyMainLower x y j + y ^ 9 * shiftedInvPow x 10 j

private theorem cauchyTailTerm_higher_bounds
    {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) (j : ℕ) :
    higherCauchyMainLower x y j ≤ cauchyTailTerm x y j ∧
      cauchyTailTerm x y j ≤ higherCauchyMainUpper x y j := by
  have ha : 0 < x + (j : ℝ) := by positivity
  have hden : 0 < (x + (j : ℝ)) ^ 2 + y ^ 2 := by positivity
  constructor
  · rw [← sub_nonneg]
    unfold cauchyTailTerm higherCauchyMainLower shiftedInvPow
    field_simp [ha.ne', hden.ne']
    ring_nf
    positivity
  · rw [← sub_nonneg]
    unfold cauchyTailTerm higherCauchyMainUpper higherCauchyMainLower
      shiftedInvPow
    field_simp [ha.ne', hden.ne']
    ring_nf
    positivity

private theorem summable_higherCauchyMainLower
    {x y : ℝ} (hx : 1 ≤ x) :
    Summable (higherCauchyMainLower x y) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have h2 := summable_shiftedInvPow_tight hx0 (by norm_num : 1 < 2)
  have h4 := summable_shiftedInvPow_tight hx0 (by norm_num : 1 < 4)
  have h6 := summable_shiftedInvPow_tight hx0 (by norm_num : 1 < 6)
  have h8 := summable_shiftedInvPow_tight hx0 (by norm_num : 1 < 8)
  exact (((h2.mul_left y).sub (h4.mul_left (y ^ 3))).add
    (h6.mul_left (y ^ 5))).sub (h8.mul_left (y ^ 7))

private theorem summable_higherCauchyMainUpper
    {x y : ℝ} (hx : 1 ≤ x) :
    Summable (higherCauchyMainUpper x y) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  exact (summable_higherCauchyMainLower hx).add
    ((summable_shiftedInvPow_tight hx0 (by norm_num : 1 < 10)).mul_left
      (y ^ 9))

private theorem tsum_higherCauchyMainLower
    {x y : ℝ} (hx : 1 ≤ x) :
    (∑' j : ℕ, higherCauchyMainLower x y j) =
      y * (∑' j : ℕ, shiftedInvPow x 2 j) -
        y ^ 3 * (∑' j : ℕ, shiftedInvPow x 4 j) +
        y ^ 5 * (∑' j : ℕ, shiftedInvPow x 6 j) -
        y ^ 7 * (∑' j : ℕ, shiftedInvPow x 8 j) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have h2 := summable_shiftedInvPow_tight hx0 (by norm_num : 1 < 2)
  have h4 := summable_shiftedInvPow_tight hx0 (by norm_num : 1 < 4)
  have h6 := summable_shiftedInvPow_tight hx0 (by norm_num : 1 < 6)
  have h8 := summable_shiftedInvPow_tight hx0 (by norm_num : 1 < 8)
  rw [show higherCauchyMainLower x y = fun j ↦
      (y * shiftedInvPow x 2 j - y ^ 3 * shiftedInvPow x 4 j +
        y ^ 5 * shiftedInvPow x 6 j) - y ^ 7 * shiftedInvPow x 8 j by rfl]
  rw [Summable.tsum_sub
      (((h2.mul_left y).sub (h4.mul_left (y ^ 3))).add
        (h6.mul_left (y ^ 5)))
      (h8.mul_left (y ^ 7)),
    Summable.tsum_add ((h2.mul_left y).sub (h4.mul_left (y ^ 3)))
      (h6.mul_left (y ^ 5)),
    Summable.tsum_sub (h2.mul_left y) (h4.mul_left (y ^ 3)),
    h2.tsum_mul_left, h4.tsum_mul_left, h6.tsum_mul_left,
    h8.tsum_mul_left]

private theorem tsum_higherCauchyMainUpper
    {x y : ℝ} (hx : 1 ≤ x) :
    (∑' j : ℕ, higherCauchyMainUpper x y j) =
      (∑' j : ℕ, higherCauchyMainLower x y j) +
        y ^ 9 * (∑' j : ℕ, shiftedInvPow x 10 j) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [show higherCauchyMainUpper x y = fun j ↦
      higherCauchyMainLower x y j + y ^ 9 * shiftedInvPow x 10 j by rfl]
  rw [Summable.tsum_add (summable_higherCauchyMainLower hx)
      ((summable_shiftedInvPow_tight hx0
        (by norm_num : 1 < 10)).mul_left (y ^ 9)),
    (summable_shiftedInvPow_tight hx0
      (by norm_num : 1 < 10)).tsum_mul_left]

def higherCauchyTailLower (x y : ℝ) : ℝ :=
  y * tightInvPowLowerPotential x 2 0 -
      y ^ 3 * tightInvPowUpperPotential x 4 0 +
    y ^ 5 * tightInvPowLowerPotential x 6 0 -
      y ^ 7 * tightInvPowUpperPotential x 8 0

def higherCauchyTailUpper (x y : ℝ) : ℝ :=
  y * tightInvPowUpperPotential x 2 0 -
      y ^ 3 * tightInvPowLowerPotential x 4 0 +
    y ^ 5 * tightInvPowUpperPotential x 6 0 -
      y ^ 7 * tightInvPowLowerPotential x 8 0 +
    y ^ 9 * tightInvPowUpperPotential x 10 0

theorem cauchyTail_tsum_higher_bounds
    {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) :
    higherCauchyTailLower x y ≤ ∑' j : ℕ, cauchyTailTerm x y j ∧
      (∑' j : ℕ, cauchyTailTerm x y j) ≤
        higherCauchyTailUpper x y := by
  have hmain := summable_cauchyTailTerm hx hy
  have hlo := (summable_higherCauchyMainLower hx).tsum_le_tsum
    (fun j ↦ (cauchyTailTerm_higher_bounds hx hy j).1) hmain
  have hup := hmain.tsum_le_tsum
    (fun j ↦ (cauchyTailTerm_higher_bounds hx hy j).2)
    (summable_higherCauchyMainUpper hx)
  have h2 := tightInvPow_tsum_bounds hx
    (Or.inl rfl : 2 = 2 ∨ 2 = 4 ∨ 2 = 6 ∨ 2 = 8 ∨ 2 = 10)
  have h4 := tightInvPow_tsum_bounds hx
    (Or.inr (Or.inl rfl) : 4 = 2 ∨ 4 = 4 ∨ 4 = 6 ∨ 4 = 8 ∨ 4 = 10)
  have h6 := tightInvPow_tsum_bounds hx
    (Or.inr (Or.inr (Or.inl rfl)) :
      6 = 2 ∨ 6 = 4 ∨ 6 = 6 ∨ 6 = 8 ∨ 6 = 10)
  have h8 := tightInvPow_tsum_bounds hx
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))) :
      8 = 2 ∨ 8 = 4 ∨ 8 = 6 ∨ 8 = 8 ∨ 8 = 10)
  have h10 := tightInvPow_tsum_bounds hx
    (Or.inr (Or.inr (Or.inr (Or.inr rfl))) :
      10 = 2 ∨ 10 = 4 ∨ 10 = 6 ∨ 10 = 8 ∨ 10 = 10)
  rw [tsum_higherCauchyMainLower hx] at hlo
  rw [tsum_higherCauchyMainUpper hx, tsum_higherCauchyMainLower hx] at hup
  constructor
  · unfold higherCauchyTailLower
    calc
      y * tightInvPowLowerPotential x 2 0 -
            y ^ 3 * tightInvPowUpperPotential x 4 0 +
          y ^ 5 * tightInvPowLowerPotential x 6 0 -
            y ^ 7 * tightInvPowUpperPotential x 8 0 ≤
          y * (∑' j : ℕ, shiftedInvPow x 2 j) -
            y ^ 3 * (∑' j : ℕ, shiftedInvPow x 4 j) +
            y ^ 5 * (∑' j : ℕ, shiftedInvPow x 6 j) -
            y ^ 7 * (∑' j : ℕ, shiftedInvPow x 8 j) := by
          gcongr
          · exact h2.1
          · exact h4.2
          · exact h6.1
          · exact h8.2
      _ ≤ _ := hlo
  · unfold higherCauchyTailUpper
    apply hup.trans
    gcongr
    · exact h2.2
    · exact h4.1
    · exact h6.2
    · exact h8.1
    · exact h10.2

theorem sineCauchyTerm_tail_higher_bounds
    {n N : ℕ} (hn : n ≠ 0) (hN : 0 < N) :
    let x : ℝ := N + 1 / 4
    let y : ℝ := yoshidaScaledFrequency n
    higherCauchyTailLower x y - 2 * y / (4 : ℝ) ^ N ≤
        ∑' j : ℕ, sineCauchyTerm n (N + j) ∧
      (∑' j : ℕ, sineCauchyTerm n (N + j)) ≤
        higherCauchyTailUpper x y := by
  dsimp only
  let x : ℝ := N + 1 / 4
  let y : ℝ := yoshidaScaledFrequency n
  have hx : 1 ≤ x := by
    dsimp only [x]
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hy : 0 ≤ y := (yoshidaScaledFrequency_pos hn).le
  have hmain := cauchyTail_tsum_higher_bounds hx hy
  have hmainEq : (fun j : ℕ ↦ sineMainTerm n (N + j)) =
      cauchyTailTerm x y := by
    funext j
    simpa only [x, y] using sineMainTerm_shift n N j
  rw [← hmainEq] at hmain
  have hcorr := sineDyadicCorrection_tail_le hn hN
  have hmainSummable : Summable (fun j : ℕ ↦ sineMainTerm n (N + j)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff N).2 (summable_sineMainTerm hn)
  have hcorrSummable : Summable
      (fun j : ℕ ↦ sineDyadicCorrection n (N + j)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff N).2 (summable_sineDyadicCorrection hn)
  have htailEq :
      (∑' j : ℕ, sineCauchyTerm n (N + j)) =
        (∑' j : ℕ, sineMainTerm n (N + j)) -
          ∑' j : ℕ, sineDyadicCorrection n (N + j) := by
    rw [← hmainSummable.tsum_sub hcorrSummable]
    apply tsum_congr
    intro j
    exact sineCauchyTerm_eq_main_sub_correction n (N + j)
  have hcorr0 : 0 ≤ ∑' j : ℕ, sineDyadicCorrection n (N + j) :=
    tsum_nonneg fun j ↦ sineDyadicCorrection_nonneg hn (N + j)
  rw [htailEq]
  constructor <;> linarith

/-! ## Exact rational higher-tail intervals -/

def lowTailShiftQ (K : ℕ) : ℚ := K + 1 / 4

def tightInvPowUpperQ (K p : ℕ) : ℚ :=
  (((p - 1 : ℕ) : ℚ))⁻¹ * (1 / lowTailShiftQ K ^ (p - 1)) +
    (1 / 2) * (1 / lowTailShiftQ K ^ p) +
    (p / 12) * (1 / lowTailShiftQ K ^ (p + 1))

def tightInvPowLowerQ (K p : ℕ) : ℚ :=
  tightInvPowUpperQ K p -
    ((p * (p + 1) * (p + 2) : ℕ) / 720) *
      (1 / lowTailShiftQ K ^ (p + 3))

def tightInvPowUpperInterval (K p : ℕ) : RatInterval :=
  pure (tightInvPowUpperQ K p)

def tightInvPowLowerInterval (K p : ℕ) : RatInterval :=
  pure (tightInvPowLowerQ K p)

theorem tightInvPowUpperInterval_contains (K p : ℕ) :
    (tightInvPowUpperInterval K p).Contains
      (tightInvPowUpperPotential ((K : ℝ) + 1 / 4) p 0) := by
  convert contains_pure (tightInvPowUpperQ K p) using 1
  unfold tightInvPowUpperQ tightInvPowUpperPotential shiftedInvPow lowTailShiftQ
  push_cast
  ring

theorem tightInvPowLowerInterval_contains (K p : ℕ) :
    (tightInvPowLowerInterval K p).Contains
      (tightInvPowLowerPotential ((K : ℝ) + 1 / 4) p 0) := by
  convert contains_pure (tightInvPowLowerQ K p) using 1
  unfold tightInvPowLowerQ tightInvPowUpperQ tightInvPowLowerPotential
    tightInvPowUpperPotential shiftedInvPow lowTailShiftQ
  push_cast
  ring

def nonnegPowInterval (I : RatInterval) (p : ℕ) : RatInterval :=
  ⟨I.lower ^ p, I.upper ^ p⟩

theorem nonnegPowInterval_contains
    {I : RatInterval} {x : ℝ} (hI0 : 0 ≤ I.lower)
    (hx : I.Contains x) (p : ℕ) :
    (nonnegPowInterval I p).Contains (x ^ p) := by
  have hl0 : (0 : ℝ) ≤ I.lower := by exact_mod_cast hI0
  have hx0 : 0 ≤ x := hl0.trans hx.1
  constructor
  · norm_num [nonnegPowInterval, Contains]
    exact pow_le_pow_left₀ hl0 hx.1 p
  · norm_num [nonnegPowInterval, Contains]
    exact pow_le_pow_left₀ hx0 hx.2 p

private theorem yoshidaYInterval_lower_nonneg (n : ℕ) :
    0 ≤ (yoshidaYInterval n).lower := by
  change 0 ≤ piFineInterval.lower * n / logTwoFineInterval.upper
  unfold piFineInterval logTwoFineInterval
  positivity

def higherSineTailLowerFormulaInterval (n K : ℕ) : RatInterval :=
  let y := yoshidaYInterval n
  y * tightInvPowLowerInterval K 2 -
      nonnegPowInterval y 3 * tightInvPowUpperInterval K 4 +
    nonnegPowInterval y 5 * tightInvPowLowerInterval K 6 -
      nonnegPowInterval y 7 * tightInvPowUpperInterval K 8 -
    pure 2 * y / pure ((4 : ℚ) ^ K)

def higherSineTailUpperFormulaInterval (n K : ℕ) : RatInterval :=
  let y := yoshidaYInterval n
  y * tightInvPowUpperInterval K 2 -
      nonnegPowInterval y 3 * tightInvPowLowerInterval K 4 +
    nonnegPowInterval y 5 * tightInvPowUpperInterval K 6 -
      nonnegPowInterval y 7 * tightInvPowLowerInterval K 8 +
    nonnegPowInterval y 9 * tightInvPowUpperInterval K 10

def higherSineCauchyTailInterval (n K : ℕ) : RatInterval :=
  ⟨(higherSineTailLowerFormulaInterval n K).lower,
    (higherSineTailUpperFormulaInterval n K).upper⟩

private theorem higherSineTailLowerFormulaInterval_contains (n K : ℕ) :
    (higherSineTailLowerFormulaInterval n K).Contains
      (higherCauchyTailLower ((K : ℝ) + 1 / 4)
          (yoshidaScaledFrequency n) -
        2 * yoshidaScaledFrequency n / (4 : ℝ) ^ K) := by
  have hy : (yoshidaYInterval n).Contains (yoshidaScaledFrequency n) := by
    rw [yoshidaScaledFrequency_eq_y]
    exact yoshidaYInterval_contains n
  have h2 := tightInvPowLowerInterval_contains K 2
  have h4 := tightInvPowUpperInterval_contains K 4
  have h6 := tightInvPowLowerInterval_contains K 6
  have h8 := tightInvPowUpperInterval_contains K 8
  have hy0 := yoshidaYInterval_lower_nonneg n
  have hfour : (pure ((4 : ℚ) ^ K)).Contains ((4 : ℝ) ^ K) := by
    simpa using contains_pure ((4 : ℚ) ^ K)
  unfold higherSineTailLowerFormulaInterval higherCauchyTailLower
  exact contains_sub
    (contains_sub
      (contains_add
        (contains_sub (contains_mul hy h2)
          (contains_mul (nonnegPowInterval_contains hy0 hy 3) h4))
        (contains_mul (nonnegPowInterval_contains hy0 hy 5) h6))
      (contains_mul (nonnegPowInterval_contains hy0 hy 7) h8))
    (contains_div_of_pos (by
      change 0 < (4 : ℚ) ^ K
      positivity)
      (contains_mul (contains_pure 2) hy) hfour)

private theorem higherSineTailUpperFormulaInterval_contains (n K : ℕ) :
    (higherSineTailUpperFormulaInterval n K).Contains
      (higherCauchyTailUpper ((K : ℝ) + 1 / 4)
        (yoshidaScaledFrequency n)) := by
  have hy : (yoshidaYInterval n).Contains (yoshidaScaledFrequency n) := by
    rw [yoshidaScaledFrequency_eq_y]
    exact yoshidaYInterval_contains n
  have h2 := tightInvPowUpperInterval_contains K 2
  have h4 := tightInvPowLowerInterval_contains K 4
  have h6 := tightInvPowUpperInterval_contains K 6
  have h8 := tightInvPowLowerInterval_contains K 8
  have h10 := tightInvPowUpperInterval_contains K 10
  have hy0 := yoshidaYInterval_lower_nonneg n
  unfold higherSineTailUpperFormulaInterval higherCauchyTailUpper
  exact contains_add
    (contains_sub
      (contains_add
        (contains_sub (contains_mul hy h2)
          (contains_mul (nonnegPowInterval_contains hy0 hy 3) h4))
        (contains_mul (nonnegPowInterval_contains hy0 hy 5) h6))
      (contains_mul (nonnegPowInterval_contains hy0 hy 7) h8))
    (contains_mul (nonnegPowInterval_contains hy0 hy 9) h10)

theorem higherSineCauchyTailInterval_contains
    {n K : ℕ} (hn : n ≠ 0) (hK : 0 < K) :
    (higherSineCauchyTailInterval n K).Contains
      (∑' j : ℕ, sineCauchyTerm n (K + j)) := by
  change
    ((higherSineTailLowerFormulaInterval n K).lower : ℝ) ≤
        (∑' j : ℕ, sineCauchyTerm n (K + j)) ∧
      (∑' j : ℕ, sineCauchyTerm n (K + j)) ≤
        ((higherSineTailUpperFormulaInterval n K).upper : ℝ)
  have ht := sineCauchyTerm_tail_higher_bounds hn hK
  have hlo := higherSineTailLowerFormulaInterval_contains n K
  have hup := higherSineTailUpperFormulaInterval_contains n K
  exact ⟨hlo.1.trans ht.1, ht.2.trans hup.2⟩

private def higherSineTailLowerAtQ (y : ℚ) (K : ℕ) : ℚ :=
  y * tightInvPowLowerQ K 2 - y ^ 3 * tightInvPowUpperQ K 4 +
    y ^ 5 * tightInvPowLowerQ K 6 - y ^ 7 * tightInvPowUpperQ K 8 -
    2 * y / (4 : ℚ) ^ K

private def higherSineTailUpperAtQ (y : ℚ) (K : ℕ) : ℚ :=
  y * tightInvPowUpperQ K 2 - y ^ 3 * tightInvPowLowerQ K 4 +
    y ^ 5 * tightInvPowUpperQ K 6 - y ^ 7 * tightInvPowLowerQ K 8 +
    y ^ 9 * tightInvPowUpperQ K 10
private theorem pow_sub_pow_le_mul
    {a b B : ℚ} (hb0 : 0 ≤ b) (hba : b ≤ a) (haB : a ≤ B)
    (p : ℕ) :
    a ^ p - b ^ p ≤ (p : ℚ) * B ^ (p - 1) * (a - b) := by
  have ha0 : 0 ≤ a := hb0.trans hba
  have hB0 : 0 ≤ B := ha0.trans haB
  induction p with
  | zero => simp
  | succ p ih =>
      have hpow : b ^ p ≤ a ^ p := pow_le_pow_left₀ hb0 hba p
      have hpowB : a ^ p ≤ B ^ p := pow_le_pow_left₀ ha0 haB p
      have hdiff : 0 ≤ a - b := sub_nonneg.mpr hba
      have hpowdiff : 0 ≤ a ^ p - b ^ p := sub_nonneg.mpr hpow
      have hihrhs : 0 ≤ (p : ℚ) * B ^ (p - 1) * (a - b) := by positivity
      calc
        a ^ (p + 1) - b ^ (p + 1) =
            a ^ p * (a - b) + b * (a ^ p - b ^ p) := by ring
        _ ≤ B ^ p * (a - b) +
            B * ((p : ℚ) * B ^ (p - 1) * (a - b)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hpowB hdiff)
            (mul_le_mul (hba.trans haB) ih hpowdiff hB0)
        _ = ((p + 1 : ℕ) : ℚ) * B ^ ((p + 1 : ℕ) - 1) *
            (a - b) := by
          push_cast
          cases p
          · simp
          · simp
            ring

private theorem nonnegPowInterval_valid
    {I : RatInterval} (hI0 : 0 ≤ I.lower) (hI : I.Valid) (p : ℕ) :
    (nonnegPowInterval I p).Valid := by
  exact pow_le_pow_left₀ hI0 hI p

private theorem nonnegPowInterval_width_le
    {I : RatInterval} {B W : ℚ} (hI0 : 0 ≤ I.lower) (hI : I.Valid)
    (hupper : I.upper ≤ B) (hwidth : width I ≤ W) (p : ℕ) :
    width (nonnegPowInterval I p) ≤
      (p : ℚ) * B ^ (p - 1) * W := by
  change I.upper ^ p - I.lower ^ p ≤ _
  calc
    I.upper ^ p - I.lower ^ p ≤
        (p : ℚ) * B ^ (p - 1) * (I.upper - I.lower) :=
      pow_sub_pow_le_mul hI0 hI hupper p
    _ ≤ (p : ℚ) * B ^ (p - 1) * W := by
      exact mul_le_mul_of_nonneg_left hwidth
        (mul_nonneg (Nat.cast_nonneg p) (pow_nonneg (by
          exact (hI0.trans hI).trans hupper) _))

private theorem inv_lowTailShift_pow_le_inv_nat_pow
    {K : ℕ} (hK : 1 ≤ K) (p : ℕ) :
    1 / lowTailShiftQ K ^ p ≤ 1 / (K : ℚ) ^ p := by
  have hKpos : (0 : ℚ) < K := by exact_mod_cast (show 0 < K by omega)
  have hx : (K : ℚ) ≤ lowTailShiftQ K := by
    unfold lowTailShiftQ
    norm_num
  exact one_div_le_one_div_of_le (pow_pos hKpos p)
    (pow_le_pow_left₀ hKpos.le hx p)

private theorem inv_nat_pow_succ_le
    {K : ℕ} (hK : 40 ≤ K) (p : ℕ) :
    1 / (K : ℚ) ^ (p + 1) ≤
      (1 / 40 : ℚ) * (1 / (K : ℚ) ^ p) := by
  have hKpos : (0 : ℚ) < K := by exact_mod_cast (show 0 < K by omega)
  have hK40 : (40 : ℚ) ≤ K := by exact_mod_cast hK
  have hinv : (K : ℚ)⁻¹ ≤ (1 / 40 : ℚ) := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 40) hK40)
  calc
    1 / (K : ℚ) ^ (p + 1) =
        (1 / (K : ℚ) ^ p) * (K : ℚ)⁻¹ := by
      rw [pow_succ]
      field_simp
    _ ≤ (1 / (K : ℚ) ^ p) * (1 / 40 : ℚ) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (1 / 40 : ℚ) * (1 / (K : ℚ) ^ p) := by ring

private theorem inv_nat_pow_antitone
    {K r s : ℕ} (hK : 1 ≤ K) (hrs : r ≤ s) :
    1 / (K : ℚ) ^ s ≤ 1 / (K : ℚ) ^ r := by
  have hKpos : (0 : ℚ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKone : (1 : ℚ) ≤ K := by exact_mod_cast hK
  exact one_div_le_one_div_of_le (pow_pos hKpos r)
    (pow_le_pow_right₀ hKone hrs)

private theorem tightInvPowUpperQ_le_two
    {K p : ℕ} (hK : 40 ≤ K)
    (hp : p = 2 ∨ p = 4 ∨ p = 6 ∨ p = 8) :
    tightInvPowUpperQ K p ≤ 2 * (1 / (K : ℚ) ^ (p - 1)) := by
  have hK1 : 1 ≤ K := by omega
  have hshift (r : ℕ) := inv_lowTailShift_pow_le_inv_nat_pow hK1 r
  have hdecay (r s : ℕ) (hrs : r ≤ s) :=
    inv_nat_pow_antitone hK1 hrs
  have hterm (r s : ℕ) (hrs : r ≤ s) :
      1 / lowTailShiftQ K ^ s ≤ 1 / (K : ℚ) ^ r :=
    (hshift s).trans (hdecay r s hrs)
  rcases hp with (rfl | rfl | rfl | rfl)
  · norm_num [tightInvPowUpperQ]
    have a := hterm 1 1 (by omega)
    have b := hterm 1 2 (by omega)
    have c := hterm 1 3 (by omega)
    simp only [one_div] at a b c ⊢
    norm_num at a b c ⊢
    nlinarith [show 0 ≤ (K : ℚ)⁻¹ by positivity]
  · norm_num [tightInvPowUpperQ]
    have a := hterm 3 3 (by omega)
    have b := hterm 3 4 (by omega)
    have c := hterm 3 5 (by omega)
    simp only [one_div] at a b c ⊢
    nlinarith [show 0 ≤ ((K : ℚ) ^ 3)⁻¹ by positivity]
  · norm_num [tightInvPowUpperQ]
    have a := hterm 5 5 (by omega)
    have b := hterm 5 6 (by omega)
    have c := hterm 5 7 (by omega)
    simp only [one_div] at a b c ⊢
    nlinarith [show 0 ≤ ((K : ℚ) ^ 5)⁻¹ by positivity]
  · norm_num [tightInvPowUpperQ]
    have a := hterm 7 7 (by omega)
    have b := hterm 7 8 (by omega)
    have c := hterm 7 9 (by omega)
    simp only [one_div] at a b c ⊢
    nlinarith [show 0 ≤ ((K : ℚ) ^ 7)⁻¹ by positivity]

private theorem tightInvPowUpperQ_ten_le
    {K : ℕ} (hK : 40 ≤ K) :
    tightInvPowUpperQ K 10 ≤
      (1 / 8 : ℚ) * (1 / (K : ℚ) ^ 9) := by
  have hK1 : 1 ≤ K := by omega
  have h9 := inv_lowTailShift_pow_le_inv_nat_pow hK1 9
  have h10 := inv_lowTailShift_pow_le_inv_nat_pow hK1 10
  have h11 := inv_lowTailShift_pow_le_inv_nat_pow hK1 11
  have s9 := inv_nat_pow_succ_le hK 9
  have s10 := inv_nat_pow_succ_le hK 10
  unfold tightInvPowUpperQ
  norm_num
  simp only [one_div] at h9 h10 h11 s9 s10 ⊢
  norm_num at h9 h10 h11 s9 s10 ⊢
  have hnonneg : 0 ≤ 1 / (K : ℚ) ^ 9 := by positivity
  simp only [one_div] at hnonneg
  linarith

private theorem tightInvPowUpperQ_nonneg (K p : ℕ) :
    0 ≤ tightInvPowUpperQ K p := by
  unfold tightInvPowUpperQ lowTailShiftQ
  positivity

private theorem tightInvPowLowerQ_abs_le_three
    {K p : ℕ} (hK : 40 ≤ K)
    (hp : p = 2 ∨ p = 4 ∨ p = 6 ∨ p = 8) :
    |tightInvPowLowerQ K p| ≤
      3 * (1 / (K : ℚ) ^ (p - 1)) := by
  have hK1 : 1 ≤ K := by omega
  have hU := tightInvPowUpperQ_le_two hK hp
  have hU0 := tightInvPowUpperQ_nonneg K p
  have hbase0 : 0 ≤ 1 / (K : ℚ) ^ (p - 1) := by positivity
  have hshift (r s : ℕ) (hrs : r ≤ s) :
      1 / lowTailShiftQ K ^ s ≤ 1 / (K : ℚ) ^ r :=
    (inv_lowTailShift_pow_le_inv_nat_pow hK1 s).trans
      (inv_nat_pow_antitone hK1 hrs)
  have hx0 : 0 ≤ lowTailShiftQ K := by
    unfold lowTailShiftQ
    positivity
  let R : ℚ := ((p * (p + 1) * (p + 2) : ℕ) / 720) *
    (1 / lowTailShiftQ K ^ (p + 3))
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    exact mul_nonneg (by positivity)
      (div_nonneg (by norm_num) (pow_nonneg hx0 _))
  have hR : R ≤ 1 / (K : ℚ) ^ (p - 1) := by
    rcases hp with (rfl | rfl | rfl | rfl) <;> dsimp only [R] <;> norm_num
    · have hs := hshift 1 5 (by omega)
      simp only [one_div] at hs ⊢
      norm_num at hs ⊢
      nlinarith [show 0 ≤ (lowTailShiftQ K ^ 5)⁻¹ by
        exact inv_nonneg.mpr (pow_nonneg hx0 _)]
    · have hs := hshift 3 7 (by omega)
      simp only [one_div] at hs ⊢
      nlinarith [show 0 ≤ (lowTailShiftQ K ^ 7)⁻¹ by
        exact inv_nonneg.mpr (pow_nonneg hx0 _)]
    · have hs := hshift 5 9 (by omega)
      simp only [one_div] at hs ⊢
      nlinarith [show 0 ≤ (lowTailShiftQ K ^ 9)⁻¹ by
        exact inv_nonneg.mpr (pow_nonneg hx0 _)]
    · simpa only [one_div] using hshift 7 11 (by omega)
  change |tightInvPowUpperQ K p - R| ≤ _
  rw [abs_le]
  constructor <;> linarith

private theorem scaled_nat_pow_ratio_le
    {n K : ℕ} (hn : 1 ≤ n) (hK : 300 * n ≤ 7 * K) (p : ℕ) :
    (((91 / 20 : ℚ) * n) ^ p) / ((K : ℚ) ^ p) ≤
      (637 / 6000 : ℚ) ^ p := by
  have hn0 : (0 : ℚ) ≤ n := by positivity
  have hKpos : (0 : ℚ) < K := by
    exact_mod_cast (show 0 < K by omega)
  have hKq : (300 : ℚ) * n ≤ 7 * K := by exact_mod_cast hK
  have hbase : (91 / 20 : ℚ) * n ≤ (637 / 6000 : ℚ) * K := by
    nlinarith
  rw [div_le_iff₀ (pow_pos hKpos p)]
  calc
    ((91 / 20 : ℚ) * n) ^ p ≤
        ((637 / 6000 : ℚ) * K) ^ p :=
      pow_le_pow_left₀ (by positivity) hbase p
    _ = (637 / 6000 : ℚ) ^ p * (K : ℚ) ^ p := by ring

private theorem tailPowerProduct_width_le
    {n K r : ℕ} {q C : ℚ}
    (hn : 1 ≤ n) (hK : 300 * n ≤ 7 * K)
    (hq : |q| ≤ C * (1 / (K : ℚ) ^ r)) (hC : 0 ≤ C) :
    width (nonnegPowInterval (yoshidaYInterval n) r * pure q) ≤
      (C * (r : ℚ) / ((91 / 20 : ℚ) * 7000000000)) *
        (637 / 6000 : ℚ) ^ r := by
  let B : ℚ := (91 / 20 : ℚ) * n
  let W : ℚ := (n : ℚ) / 7000000000
  have hy0 := yoshidaYInterval_lower_nonneg n
  have hyv := yoshidaYInterval_valid n
  have hyu : (yoshidaYInterval n).upper ≤ B := by
    simpa only [B] using
      yoshidaYInterval_upper_le_ninety_one_twentieths_mul_nat n
  have hyw : width (yoshidaYInterval n) ≤ W := by
    simpa only [W] using yoshidaYInterval_width_le n
  have hpv := nonnegPowInterval_valid hy0 hyv r
  have hpw := nonnegPowInterval_width_le hy0 hyv hyu hyw r
  have hqbound0 : 0 ≤ C * (1 / (K : ℚ) ^ r) := by positivity
  rw [width_mul_pure q hpv]
  calc
    |q| * width (nonnegPowInterval (yoshidaYInterval n) r) ≤
        (C * (1 / (K : ℚ) ^ r)) *
          ((r : ℚ) * B ^ (r - 1) * W) :=
      mul_le_mul hq hpw (width_nonneg hpv) hqbound0
    _ = (C * (r : ℚ) / ((91 / 20 : ℚ) * 7000000000)) *
          (B ^ r / (K : ℚ) ^ r) := by
      dsimp only [B, W]
      cases r with
      | zero => norm_num
      | succ r =>
          simp only [Nat.add_sub_cancel]
          field_simp
          ring
    _ ≤ (C * (r : ℚ) / ((91 / 20 : ℚ) * 7000000000)) *
          (637 / 6000 : ℚ) ^ r := by
      apply mul_le_mul_of_nonneg_left (scaled_nat_pow_ratio_le hn hK r)
      positivity

private theorem nat_sq_le_four_pow (K : ℕ) : K ^ 2 ≤ 4 ^ K := by
  induction K using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more K ih0 ih1 =>
      calc
        (K + 2) ^ 2 ≤ 4 * (K + 1) ^ 2 := by
          simp only [pow_two]
          nlinarith
        _ ≤ 4 * 4 ^ (K + 1) := Nat.mul_le_mul_left 4 ih1
        _ = 4 ^ (K + 2) := by ring

private theorem dyadicTailCorrection_width_le
    {n K : ℕ} (hn : 1 ≤ n) (hK : 300 * n ≤ 7 * K) :
    width (pure 2 * yoshidaYInterval n / pure ((4 : ℚ) ^ K)) ≤
      (1 / 100000000000 : ℚ) := by
  have hKn : n ≤ K := by omega
  have hK40 : 40 ≤ K := by omega
  have hKpos : (0 : ℚ) < K := by exact_mod_cast (show 0 < K by omega)
  have hsquareNat := nat_sq_le_four_pow K
  have hsquare : (K : ℚ) ^ 2 ≤ (4 : ℚ) ^ K := by exact_mod_cast hsquareNat
  have hinv : ((4 : ℚ) ^ K)⁻¹ ≤ ((K : ℚ) ^ 2)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (pow_pos hKpos 2) hsquare
  have hyn := yoshidaYInterval_valid n
  have hyw := yoshidaYInterval_width_le n
  change width ((RatInterval.pure 2 * yoshidaYInterval n) *
    RatInterval.pure (((4 : ℚ) ^ K)⁻¹)) ≤ _
  rw [width_mul_pure _ (valid_mul (valid_pure 2) hyn),
    abs_of_nonneg (by positivity), width_pure_mul 2 hyn,
    abs_of_nonneg (by norm_num)]
  have hnq : (n : ℚ) ≤ K := by exact_mod_cast hKn
  calc
    ((4 : ℚ) ^ K)⁻¹ * (2 * width (yoshidaYInterval n)) ≤
        ((K : ℚ) ^ 2)⁻¹ * (2 * ((n : ℚ) / 7000000000)) := by
      exact mul_le_mul hinv (mul_le_mul_of_nonneg_left hyw (by norm_num))
        (mul_nonneg (by norm_num) (width_nonneg hyn)) (by positivity)
    _ ≤ ((K : ℚ) ^ 2)⁻¹ * (2 * ((K : ℚ) / 7000000000)) := by
      gcongr
    _ = 2 / (7000000000 * (K : ℚ)) := by
      field_simp
    _ ≤ 1 / 100000000000 := by
      rw [div_le_iff₀ (by positivity : (0 : ℚ) < 7000000000 * K)]
      have hKq : (40 : ℚ) ≤ K := by exact_mod_cast hK40
      nlinarith

private theorem higherSineTailLowerFormulaInterval_width_le
    {n K : ℕ} (hn : 1 ≤ n) (hK : 300 * n ≤ 7 * K) :
    width (higherSineTailLowerFormulaInterval n K) ≤
      (21 / 1000000000000 : ℚ) := by
  have hK40 : 40 ≤ K := by omega
  have hL2 := tightInvPowLowerQ_abs_le_three hK40
    (Or.inl rfl : 2 = 2 ∨ 2 = 4 ∨ 2 = 6 ∨ 2 = 8)
  have hU4 : |tightInvPowUpperQ K 4| ≤
      2 * (1 / (K : ℚ) ^ 3) := by
    rw [abs_of_nonneg (tightInvPowUpperQ_nonneg K 4)]
    exact tightInvPowUpperQ_le_two hK40 (Or.inr (Or.inl rfl))
  have hL6 := tightInvPowLowerQ_abs_le_three hK40
    (Or.inr (Or.inr (Or.inl rfl)) :
      6 = 2 ∨ 6 = 4 ∨ 6 = 6 ∨ 6 = 8)
  have hU8 : |tightInvPowUpperQ K 8| ≤
      2 * (1 / (K : ℚ) ^ 7) := by
    rw [abs_of_nonneg (tightInvPowUpperQ_nonneg K 8)]
    exact tightInvPowUpperQ_le_two hK40
      (Or.inr (Or.inr (Or.inr rfl)))
  have w2 := tailPowerProduct_width_le hn hK hL2 (by norm_num)
  have hpowOne : nonnegPowInterval (yoshidaYInterval n) 1 =
      yoshidaYInterval n := by
    cases h : yoshidaYInterval n
    simp [nonnegPowInterval]
  have w2' : width (yoshidaYInterval n *
      RatInterval.pure (tightInvPowLowerQ K 2)) ≤
      (1 / 100000000000 : ℚ) := by
    rw [← hpowOne]
    apply w2.trans
    norm_num
  have w4 := tailPowerProduct_width_le hn hK hU4 (by norm_num)
  have w6 := tailPowerProduct_width_le hn hK hL6 (by norm_num)
  have w8 := tailPowerProduct_width_le hn hK hU8 (by norm_num)
  have wd := dyadicTailCorrection_width_le hn hK
  unfold higherSineTailLowerFormulaInterval tightInvPowLowerInterval
    tightInvPowUpperInterval
  simp only [width_sub, width_add]
  norm_num at w4 w6 w8 ⊢
  linarith

private theorem higherSineTailUpperFormulaInterval_width_le
    {n K : ℕ} (hn : 1 ≤ n) (hK : 300 * n ≤ 7 * K) :
    width (higherSineTailUpperFormulaInterval n K) ≤
      (8 / 1000000000000 : ℚ) := by
  have hK40 : 40 ≤ K := by omega
  have hU2 : |tightInvPowUpperQ K 2| ≤
      2 * (1 / (K : ℚ) ^ 1) := by
    rw [abs_of_nonneg (tightInvPowUpperQ_nonneg K 2)]
    simpa using tightInvPowUpperQ_le_two hK40 (Or.inl rfl)
  have hL4 := tightInvPowLowerQ_abs_le_three hK40
    (Or.inr (Or.inl rfl) : 4 = 2 ∨ 4 = 4 ∨ 4 = 6 ∨ 4 = 8)
  have hU6 : |tightInvPowUpperQ K 6| ≤
      2 * (1 / (K : ℚ) ^ 5) := by
    rw [abs_of_nonneg (tightInvPowUpperQ_nonneg K 6)]
    exact tightInvPowUpperQ_le_two hK40
      (Or.inr (Or.inr (Or.inl rfl)))
  have hL8 := tightInvPowLowerQ_abs_le_three hK40
    (Or.inr (Or.inr (Or.inr rfl)) :
      8 = 2 ∨ 8 = 4 ∨ 8 = 6 ∨ 8 = 8)
  have hU10 : |tightInvPowUpperQ K 10| ≤
      (1 / 8 : ℚ) * (1 / (K : ℚ) ^ 9) := by
    rw [abs_of_nonneg (tightInvPowUpperQ_nonneg K 10)]
    exact tightInvPowUpperQ_ten_le hK40
  have w2 := tailPowerProduct_width_le hn hK hU2 (by norm_num)
  have hpowOne : nonnegPowInterval (yoshidaYInterval n) 1 =
      yoshidaYInterval n := by
    cases h : yoshidaYInterval n
    simp [nonnegPowInterval]
  have w2' : width (yoshidaYInterval n *
      RatInterval.pure (tightInvPowUpperQ K 2)) ≤
      (1 / 150000000000 : ℚ) := by
    rw [← hpowOne]
    apply w2.trans
    norm_num
  have w4 := tailPowerProduct_width_le hn hK hL4 (by norm_num)
  have w6 := tailPowerProduct_width_le hn hK hU6 (by norm_num)
  have w8 := tailPowerProduct_width_le hn hK hL8 (by norm_num)
  have w10 := tailPowerProduct_width_le hn hK hU10 (by norm_num)
  unfold higherSineTailUpperFormulaInterval tightInvPowLowerInterval
    tightInvPowUpperInterval
  simp only [width_sub, width_add]
  norm_num at w4 w6 w8 w10 ⊢
  linarith

private theorem higherSineTailLowerFormulaInterval_contains_at_lower
    (n K : ℕ) :
    (higherSineTailLowerFormulaInterval n K).lower ≤
        higherSineTailLowerAtQ (yoshidaYInterval n).lower K ∧
      higherSineTailLowerAtQ (yoshidaYInterval n).lower K ≤
        (higherSineTailLowerFormulaInterval n K).upper := by
  have hyv := yoshidaYInterval_valid n
  have hy0 := yoshidaYInterval_lower_nonneg n
  have hy : (yoshidaYInterval n).Contains
      (((yoshidaYInterval n).lower : ℚ) : ℝ) := by
    constructor
    · norm_num
    · exact_mod_cast hyv
  have h := contains_sub
    (contains_sub
      (contains_add
        (contains_sub
          (contains_mul hy (contains_pure (tightInvPowLowerQ K 2)))
          (contains_mul (nonnegPowInterval_contains hy0 hy 3)
            (contains_pure (tightInvPowUpperQ K 4))))
        (contains_mul (nonnegPowInterval_contains hy0 hy 5)
          (contains_pure (tightInvPowLowerQ K 6))))
      (contains_mul (nonnegPowInterval_contains hy0 hy 7)
        (contains_pure (tightInvPowUpperQ K 8))))
    (contains_div_of_pos (by
      change 0 < (4 : ℚ) ^ K
      positivity)
      (contains_mul (contains_pure 2) hy)
      (contains_pure ((4 : ℚ) ^ K)))
  have h' : (higherSineTailLowerFormulaInterval n K).Contains
      ((higherSineTailLowerAtQ (yoshidaYInterval n).lower K : ℚ) : ℝ) := by
    convert h using 1
    all_goals norm_num [higherSineTailLowerFormulaInterval,
      higherSineTailLowerAtQ]
  constructor
  · exact_mod_cast h'.1
  · exact_mod_cast h'.2

private theorem higherSineTailUpperFormulaInterval_contains_at_lower
    (n K : ℕ) :
    (higherSineTailUpperFormulaInterval n K).lower ≤
        higherSineTailUpperAtQ (yoshidaYInterval n).lower K ∧
      higherSineTailUpperAtQ (yoshidaYInterval n).lower K ≤
        (higherSineTailUpperFormulaInterval n K).upper := by
  have hyv := yoshidaYInterval_valid n
  have hy0 := yoshidaYInterval_lower_nonneg n
  have hy : (yoshidaYInterval n).Contains
      (((yoshidaYInterval n).lower : ℚ) : ℝ) := by
    constructor
    · norm_num
    · exact_mod_cast hyv
  have h := contains_add
    (contains_sub
      (contains_add
        (contains_sub
          (contains_mul hy (contains_pure (tightInvPowUpperQ K 2)))
          (contains_mul (nonnegPowInterval_contains hy0 hy 3)
            (contains_pure (tightInvPowLowerQ K 4))))
        (contains_mul (nonnegPowInterval_contains hy0 hy 5)
          (contains_pure (tightInvPowUpperQ K 6))))
      (contains_mul (nonnegPowInterval_contains hy0 hy 7)
        (contains_pure (tightInvPowLowerQ K 8))))
    (contains_mul (nonnegPowInterval_contains hy0 hy 9)
      (contains_pure (tightInvPowUpperQ K 10)))
  have h' : (higherSineTailUpperFormulaInterval n K).Contains
      ((higherSineTailUpperAtQ (yoshidaYInterval n).lower K : ℚ) : ℝ) := by
    convert h using 1
    all_goals norm_num [higherSineTailUpperFormulaInterval,
      higherSineTailUpperAtQ]
  constructor
  · exact_mod_cast h'.1
  · exact_mod_cast h'.2

private theorem ypow_mul_tightInvPow_gap_le
    {n K p : ℕ} (hn : 1 ≤ n) (hKmin : 256 ≤ K)
    (hK : 300 * n ≤ 7 * K)
    (hp : p = 2 ∨ p = 4 ∨ p = 6 ∨ p = 8) :
    (yoshidaYInterval n).lower ^ (p - 1) *
        (tightInvPowUpperQ K p - tightInvPowLowerQ K p) ≤
      (((p * (p + 1) * (p + 2) : ℕ) : ℚ) / 720) *
        (637 / 6000 : ℚ) ^ (p - 1) / (256 : ℚ) ^ 4 := by
  have hp2 : 2 ≤ p := by
    rcases hp with (rfl | rfl | rfl | rfl) <;> omega
  have hK40 : 40 ≤ K := by omega
  have hK1 : 1 ≤ K := by omega
  have hKpos : (0 : ℚ) < K := by exact_mod_cast (show 0 < K by omega)
  let y : ℚ := (yoshidaYInterval n).lower
  let B : ℚ := (91 / 20 : ℚ) * n
  let C : ℚ := (((p * (p + 1) * (p + 2) : ℕ) : ℚ) / 720)
  have hy0 : 0 ≤ y := by
    simpa only [y] using yoshidaYInterval_lower_nonneg n
  have hyB : y ≤ B := by
    dsimp only [y, B]
    exact (yoshidaYInterval_valid n).trans
      (yoshidaYInterval_upper_le_ninety_one_twentieths_mul_nat n)
  have hpow : y ^ (p - 1) ≤ B ^ (p - 1) :=
    pow_le_pow_left₀ hy0 hyB (p - 1)
  have hratio : y ^ (p - 1) / (K : ℚ) ^ (p - 1) ≤
      (637 / 6000 : ℚ) ^ (p - 1) := by
    exact (div_le_div_of_nonneg_right hpow (pow_nonneg hKpos.le _)).trans
      (scaled_nat_pow_ratio_le hn hK (p - 1))
  have hKq : (256 : ℚ) ≤ K := by exact_mod_cast hKmin
  have hinv4 : 1 / (K : ℚ) ^ 4 ≤ 1 / (256 : ℚ) ^ 4 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < (256 : ℚ) ^ 4)
      (pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 256) hKq 4)
  have hshift := inv_lowTailShift_pow_le_inv_nat_pow hK1 (p + 3)
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hx0 : 0 ≤ lowTailShiftQ K := by
    unfold lowTailShiftQ
    positivity
  have hgap : tightInvPowUpperQ K p - tightInvPowLowerQ K p ≤
      C * (1 / (K : ℚ) ^ (p + 3)) := by
    rw [show tightInvPowUpperQ K p - tightInvPowLowerQ K p =
        C * (1 / lowTailShiftQ K ^ (p + 3)) by
      unfold tightInvPowLowerQ C
      ring]
    exact mul_le_mul_of_nonneg_left hshift hC0
  have hgap0 : 0 ≤ tightInvPowUpperQ K p - tightInvPowLowerQ K p := by
    rw [show tightInvPowUpperQ K p - tightInvPowLowerQ K p =
        C * (1 / lowTailShiftQ K ^ (p + 3)) by
      unfold tightInvPowLowerQ C
      ring]
    exact mul_nonneg hC0
      (div_nonneg (by norm_num) (pow_nonneg hx0 _))
  calc
    y ^ (p - 1) *
          (tightInvPowUpperQ K p - tightInvPowLowerQ K p) ≤
        y ^ (p - 1) * (C * (1 / (K : ℚ) ^ (p + 3))) :=
      mul_le_mul_of_nonneg_left hgap (pow_nonneg hy0 _)
    _ = C * (y ^ (p - 1) / (K : ℚ) ^ (p - 1)) *
          (1 / (K : ℚ) ^ 4) := by
      rw [show p + 3 = (p - 1) + 4 by omega, pow_add]
      field_simp
    _ ≤ C * (637 / 6000 : ℚ) ^ (p - 1) *
          (1 / (256 : ℚ) ^ 4) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hratio hC0) hinv4
        (by positivity) (by positivity)
    _ = C * (637 / 6000 : ℚ) ^ (p - 1) / (256 : ℚ) ^ 4 := by
      ring

private theorem ninth_upper_term_le
    {n K : ℕ} (hn : 1 ≤ n) (hK : 300 * n ≤ 7 * K) :
    (yoshidaYInterval n).lower ^ 9 * tightInvPowUpperQ K 10 ≤
      (1 / 8 : ℚ) * (637 / 6000 : ℚ) ^ 9 := by
  have hK40 : 40 ≤ K := by omega
  have hKpos : (0 : ℚ) < K := by exact_mod_cast (show 0 < K by omega)
  let y : ℚ := (yoshidaYInterval n).lower
  let B : ℚ := (91 / 20 : ℚ) * n
  have hy0 : 0 ≤ y := by
    simpa only [y] using yoshidaYInterval_lower_nonneg n
  have hyB : y ≤ B := by
    dsimp only [y, B]
    exact (yoshidaYInterval_valid n).trans
      (yoshidaYInterval_upper_le_ninety_one_twentieths_mul_nat n)
  have hpow : y ^ 9 ≤ B ^ 9 := pow_le_pow_left₀ hy0 hyB 9
  have hratio : y ^ 9 / (K : ℚ) ^ 9 ≤
      (637 / 6000 : ℚ) ^ 9 := by
    exact (div_le_div_of_nonneg_right hpow (pow_nonneg hKpos.le _)).trans
      (scaled_nat_pow_ratio_le hn hK 9)
  have hU := tightInvPowUpperQ_ten_le hK40
  calc
    y ^ 9 * tightInvPowUpperQ K 10 ≤
        y ^ 9 * ((1 / 8 : ℚ) * (1 / (K : ℚ) ^ 9)) :=
      mul_le_mul_of_nonneg_left hU (pow_nonneg hy0 9)
    _ = (1 / 8 : ℚ) * (y ^ 9 / (K : ℚ) ^ 9) := by ring
    _ ≤ (1 / 8 : ℚ) * (637 / 6000 : ℚ) ^ 9 :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)

private theorem nat_mul_four_pow_le
    {K : ℕ} (hK : 40 ≤ K) : K * 4 ^ 40 ≤ 40 * 4 ^ K := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ K hK ih =>
      calc
        (K + 1) * 4 ^ 40 ≤ 4 * (K * 4 ^ 40) := by
          have : 1 ≤ 3 * K := by omega
          nlinarith
        _ ≤ 4 * (40 * 4 ^ K) := Nat.mul_le_mul_left 4 ih
        _ = 40 * 4 ^ (K + 1) := by ring

private theorem dyadicTailCorrection_value_le
    {n K : ℕ} (hn : 1 ≤ n) (hK : 300 * n ≤ 7 * K) :
    2 * (yoshidaYInterval n).lower / (4 : ℚ) ^ K ≤
      (1 / 100000000000000000000 : ℚ) := by
  have hK40 : 40 ≤ K := by omega
  have hKn : n ≤ K := by omega
  have hpowNat := nat_mul_four_pow_le hK40
  have hpow : (K : ℚ) * (4 : ℚ) ^ 40 ≤
      40 * (4 : ℚ) ^ K := by exact_mod_cast hpowNat
  have hy : (yoshidaYInterval n).lower ≤ (91 / 20 : ℚ) * K := by
    exact (yoshidaYInterval_valid n).trans
      ((yoshidaYInterval_upper_le_ninety_one_twentieths_mul_nat n).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hKn)
          (by norm_num : (0 : ℚ) ≤ 91 / 20)))
  have hden : (0 : ℚ) < (4 : ℚ) ^ K := by positivity
  rw [div_le_iff₀ hden]
  have hpow40 : (0 : ℚ) < (4 : ℚ) ^ 40 := by positivity
  have hscaled : (91 / 10 : ℚ) * K ≤
      (1 / 100000000000000000000 : ℚ) * (4 : ℚ) ^ K := by
    nlinarith [hpow]
  linarith

private theorem higherSineTailAtQ_gap_le
    {n K : ℕ} (hn : 1 ≤ n) (hKmin : 256 ≤ K)
    (hK : 300 * n ≤ 7 * K) :
    higherSineTailUpperAtQ (yoshidaYInterval n).lower K -
      higherSineTailLowerAtQ (yoshidaYInterval n).lower K ≤
      (216 / 1000000000000 : ℚ) := by
  have g2 := ypow_mul_tightInvPow_gap_le hn hKmin hK
    (Or.inl rfl : 2 = 2 ∨ 2 = 4 ∨ 2 = 6 ∨ 2 = 8)
  have g4 := ypow_mul_tightInvPow_gap_le hn hKmin hK
    (Or.inr (Or.inl rfl) : 4 = 2 ∨ 4 = 4 ∨ 4 = 6 ∨ 4 = 8)
  have g6 := ypow_mul_tightInvPow_gap_le hn hKmin hK
    (Or.inr (Or.inr (Or.inl rfl)) :
      6 = 2 ∨ 6 = 4 ∨ 6 = 6 ∨ 6 = 8)
  have g8 := ypow_mul_tightInvPow_gap_le hn hKmin hK
    (Or.inr (Or.inr (Or.inr rfl)) :
      8 = 2 ∨ 8 = 4 ∨ 8 = 6 ∨ 8 = 8)
  have g10 := ninth_upper_term_le hn hK
  have gd := dyadicTailCorrection_value_le hn hK
  rw [show higherSineTailUpperAtQ (yoshidaYInterval n).lower K -
      higherSineTailLowerAtQ (yoshidaYInterval n).lower K =
      (yoshidaYInterval n).lower *
          (tightInvPowUpperQ K 2 - tightInvPowLowerQ K 2) +
        (yoshidaYInterval n).lower ^ 3 *
          (tightInvPowUpperQ K 4 - tightInvPowLowerQ K 4) +
        (yoshidaYInterval n).lower ^ 5 *
          (tightInvPowUpperQ K 6 - tightInvPowLowerQ K 6) +
        (yoshidaYInterval n).lower ^ 7 *
          (tightInvPowUpperQ K 8 - tightInvPowLowerQ K 8) +
        (yoshidaYInterval n).lower ^ 9 * tightInvPowUpperQ K 10 +
        2 * (yoshidaYInterval n).lower / (4 : ℚ) ^ K by
    unfold higherSineTailUpperAtQ higherSineTailLowerAtQ
    ring]
  norm_num at g2 g4 g6 g8 g10 gd ⊢
  linarith

theorem higherSineCauchyTailInterval_width_le
    {n K : ℕ} (hn : 1 ≤ n) (hKmin : 256 ≤ K)
    (hK : 300 * n ≤ 7 * K) :
    width (higherSineCauchyTailInterval n K) ≤
      (1 / 4000000000 : ℚ) := by
  have hloWidth := higherSineTailLowerFormulaInterval_width_le hn hK
  have hupWidth := higherSineTailUpperFormulaInterval_width_le hn hK
  have hlo := higherSineTailLowerFormulaInterval_contains_at_lower n K
  have hup := higherSineTailUpperFormulaInterval_contains_at_lower n K
  have hgap := higherSineTailAtQ_gap_le hn hKmin hK
  unfold higherSineCauchyTailInterval width
  unfold width at hloWidth hupWidth
  norm_num at hloWidth hupWidth hgap ⊢
  linarith

def higherRoundedSineCauchySeriesInterval
    (n blocks : ℕ) (scale : ℚ) : RatInterval :=
  coarseSineCheckpointHead (roundedSineCauchyChunkBox n scale) blocks +
    higherSineCauchyTailInterval n (256 * blocks)

theorem higherRoundedSineCauchySeriesInterval_contains
    {n blocks : ℕ} (hn : n ≠ 0) (hblocks : 0 < blocks)
    {scale : ℚ} (hscale : 0 < scale) :
    (higherRoundedSineCauchySeriesInterval n blocks scale).Contains
      (sinePolarValue n - yoshidaSineMoment n) := by
  have hseries := contains_add
    (coarseSineCheckpointHead_contains_production (blocks := blocks) hn _
      (fun i _ ↦ scheduledSineCauchyChunkInterval_sub_rounded n i hscale))
    (higherSineCauchyTailInterval_contains (K := 256 * blocks) hn (by omega))
  rw [yoshidaSineMoment_eq_finiteHead_sub_tail hn (256 * blocks)]
  convert hseries using 1
  all_goals ring

def higherRoundedSineSeriesInterval
    (n blocks : ℕ) (scale : ℚ) : RatInterval :=
  sinePolarInterval n -
    higherRoundedSineCauchySeriesInterval n blocks scale

theorem higherRoundedSineSeriesInterval_contains
    {n blocks : ℕ} (hn : n ≠ 0) (hblocks : 0 < blocks)
    {scale : ℚ} (hscale : 0 < scale) :
    (higherRoundedSineSeriesInterval n blocks scale).Contains
      (yoshidaSineMoment n) := by
  have h := contains_sub (sinePolarInterval_contains n)
    (higherRoundedSineCauchySeriesInterval_contains hn hblocks hscale)
  convert h using 1
  all_goals ring

/-- Rewrite the perturbation moment through the directly checkpointable
Yoshida sine moment. -/
theorem factorTwoSymmetricSinMoment_eq_checkpointedSine
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoSymmetricSinMoment n.1 =
      -(factorTwoHeadDefect / 2) * sineMainTerm n.1 0 +
        (1 / 2 : ℝ) *
          (((sinePolarValue n.1 - yoshidaSineMoment n.1) -
              (∑' k : ℕ, sineDyadicCorrection n.1 k) -
              sineMainTerm n.1 0 +
              2 * sineDyadicCorrection n.1 0) +
            ((∑' k : ℕ, factorTwoSecondDyadicCorrection n.1 k) -
              factorTwoSecondDyadicCorrection n.1 0)) -
        (Real.log 3 / Real.sqrt 3) *
          Real.sin (2 * factorTwoMomentY n.1 * factorTwoPrimeShift) := by
  rw [factorTwoSymmetricSinMoment_eq_digammaCorrections n hn]
  have hs := yoshidaSineMoment_eq_polar_sub_digamma_add_dyadic hn
  have hd : yoshidaEvenDigammaImag n.1 =
      sinePolarValue n.1 +
        (∑' k : ℕ, sineDyadicCorrection n.1 k) -
        yoshidaSineMoment n.1 := by
    linarith
  rw [hd]
  ring

/-- Parameterized exact interval using `blocks` checkpoint chunks of 256
terms, rounded outward on the rational grid `scale⁻¹`. -/
def factorTwoSymmetricSinCheckpointedInterval
    (n : FactorTwoCanonicalEvenIndex) (blocks : ℕ) (scale : ℚ) :
    RatInterval :=
  factorTwoSymmetricSinHeadInterval n.1 +
    pure (1 / 2) *
      ((higherRoundedSineCauchySeriesInterval n.1 blocks scale -
          sineDyadicCorrectionFullInterval n.1 20 -
          factorTwoSineMainInterval n.1 0 +
          pure 2 * sineDyadicCorrectionInterval n.1 0) +
        (factorTwoSecondDyadicCorrectionFullInterval n.1 12 -
          factorTwoSecondDyadicCorrectionInterval n.1 0)) -
    factorTwoSymmetricSinPrimeInterval n

theorem factorTwoSymmetricSinCheckpointedInterval_contains
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {scale : ℚ} (hscale : 0 < scale) :
    (factorTwoSymmetricSinCheckpointedInterval n blocks scale).Contains
      (factorTwoSymmetricSinMoment n.1) := by
  rw [factorTwoSymmetricSinMoment_eq_checkpointedSine n hn]
  have hsine := higherRoundedSineCauchySeriesInterval_contains
    hn hblocks hscale
  have hfirstFull := sineDyadicCorrectionFullInterval_contains hn 20
  have hfirstZero := sineDyadicCorrectionInterval_contains hn 0
  have hsecondFull :=
    factorTwoSecondDyadicCorrectionFullInterval_contains hn 12
  have hsecondZero :=
    factorTwoSecondDyadicCorrectionInterval_contains hn 0
  have hhalf : (pure (1 / 2 : ℚ)).Contains (1 / 2 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hslow := contains_add
    (contains_sub
      (contains_sub hsine hfirstFull)
      (factorTwoSineMainInterval_contains n.1 0))
    (contains_mul (contains_pure 2) hfirstZero)
  have hcore := contains_add hslow
    (contains_sub hsecondFull hsecondZero)
  exact contains_sub
    (contains_add (factorTwoSymmetricSinHeadInterval_contains n.1)
      (contains_mul hhalf hcore))
    (factorTwoSymmetricSinPrimeInterval_contains n)

def factorTwoSymmetricSinLowBlocks
    (n : FactorTwoCanonicalEvenIndex) : ℕ :=
  n.1 / 6 + 1

def factorTwoSymmetricSinLowInterval
    (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  factorTwoSymmetricSinCheckpointedInterval n
    (factorTwoSymmetricSinLowBlocks n) 1000000000000000000

theorem factorTwoSymmetricSinLowInterval_contains
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    (factorTwoSymmetricSinLowInterval n).Contains
      (factorTwoSymmetricSinMoment n.1) := by
  apply factorTwoSymmetricSinCheckpointedInterval_contains n hn
  · unfold factorTwoSymmetricSinLowBlocks
    omega
  · norm_num

/-! ## Complementary low-mode width certificate -/

theorem higherRoundedSineCauchySeriesInterval_width_le
    (n blocks : ℕ) {scale headBound tailBound : ℚ}
    (hscale : 0 < scale)
    (hhead : width (exactSineCheckpointHead n blocks) ≤ headBound)
    (htail : width (higherSineCauchyTailInterval n (256 * blocks)) ≤
      tailBound) :
    width (higherRoundedSineCauchySeriesInterval n blocks scale) ≤
      headBound + (blocks : ℚ) * (2 / scale) + tailBound := by
  rw [higherRoundedSineCauchySeriesInterval, width_add]
  linarith [coarseRoundedSineCheckpointHead_width_le n blocks hscale]

/-- Uniform finite-head contribution to the direct checkpointed Cauchy
series; only the analytic tail budget and rounding grid remain explicit. -/
theorem higherRoundedSineCauchySeriesInterval_width_le_uniform
    {n : ℕ} (hn : 1 ≤ n) (blocks : ℕ)
    {scale tailBound : ℚ} (hscale : 0 < scale)
    (htail : width (higherSineCauchyTailInterval n (256 * blocks)) ≤
      tailBound) :
    width (higherRoundedSineCauchySeriesInterval n blocks scale) ≤
      (1 : ℚ) / 4500000000 +
        (blocks : ℚ) * (2 / scale) + tailBound := by
  exact higherRoundedSineCauchySeriesInterval_width_le n blocks hscale
    (exactSineCheckpointHead_width_le hn blocks) htail

/-- Structural width bound for the legacy sine-moment interval.  This is
kept public for consumers that need `yoshidaSineMoment` itself rather than
the directly checkpointed Cauchy difference used below. -/
theorem higherRoundedSineSeriesInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) (blocks : ℕ)
    {scale tailBound : ℚ} (hscale : 0 < scale)
    (htail : width (higherSineCauchyTailInterval n (256 * blocks)) ≤
      tailBound) :
    width (higherRoundedSineSeriesInterval n blocks scale) ≤
      (1 : ℚ) / 100000000000 +
        ((1 : ℚ) / 4500000000 +
          (blocks : ℚ) * (2 / scale) + tailBound) := by
  rw [higherRoundedSineSeriesInterval, width_sub]
  exact add_le_add (sinePolarInterval_width_le hn)
    (higherRoundedSineCauchySeriesInterval_width_le_uniform hn blocks
      hscale htail)

private theorem absBound_mono {I : RatInterval} {A B : ℚ}
    (hI : I.AbsBound A) (hAB : A ≤ B) : I.AbsBound B := by
  exact ⟨(neg_le_neg hAB).trans hI.1, hI.2.trans hAB⟩

theorem factorTwoSineMainInterval_valid (n k : ℕ) :
    (factorTwoSineMainInterval n k).Valid := by
  exact valid_div_of_pos (yoshidaYInterval_valid n)
    (cauchyDenomInterval_valid n k) (cauchyDenomInterval_lower_pos n k)

theorem factorTwoSineMainInterval_absBound_quarter
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (factorTwoSineMainInterval n k).AbsBound (1 / 4 : ℚ) := by
  let m := sineCauchyDenominatorFloor n k
  have hm : 0 < m := sineCauchyDenominatorFloor_pos hn k
  have hraw := absBound_div_of_lower
    (yoshidaYInterval_valid n) (cauchyDenomInterval_valid n k)
    (yoshidaYInterval_absBound n) (by positivity) hm
    (sineCauchyDenominatorFloor_le_lower n k)
  apply absBound_mono hraw
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hmBase : ((9 / 2 : ℚ) * n) ^ 2 ≤ m := by
    dsimp only [m, sineCauchyDenominatorFloor]
    exact le_add_of_nonneg_left (sq_nonneg ((k : ℚ) + 1 / 4))
  rw [mul_inv_le_iff₀ hm]
  nlinarith [sq_nonneg (n : ℚ)]

private theorem factorTwoSineMain_width_budget
    {n : ℕ} (hn : 1 ≤ n) {m : ℚ}
    (hm : 0 < m) (hmn : ((9 / 2 : ℚ) * n) ^ 2 ≤ m) :
    m⁻¹ * ((n : ℚ) / 7000000000) +
        ((91 / 20 : ℚ) * n) *
          ((13 * (n : ℚ) ^ 2 / 10000000000) / (m * m)) ≤
      (1 : ℚ) / 40000000000 := by
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  field_simp [hm.ne']
  nlinarith [sq_nonneg (n : ℚ),
    sq_nonneg (m - ((9 / 2 : ℚ) * n) ^ 2)]

theorem factorTwoSineMainInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    width (factorTwoSineMainInterval n k) ≤
      (1 : ℚ) / 40000000000 := by
  let m := sineCauchyDenominatorFloor n k
  have hm : 0 < m := sineCauchyDenominatorFloor_pos hn k
  have hdiv := width_div_le_of_lower
    (yoshidaYInterval_valid n) (cauchyDenomInterval_valid n k)
    (yoshidaYInterval_absBound n) (by positivity) hm
    (sineCauchyDenominatorFloor_le_lower n k)
  have hfirst := mul_le_mul_of_nonneg_left (yoshidaYInterval_width_le n)
    (inv_nonneg.mpr hm.le)
  have hsecond :
      ((91 / 20 : ℚ) * n) *
          (width (cauchyDenomInterval n k) / (m * m)) ≤
        ((91 / 20 : ℚ) * n) *
          ((13 * (n : ℚ) ^ 2 / 10000000000) / (m * m)) := by
    apply mul_le_mul_of_nonneg_left
    · exact div_le_div_of_nonneg_right (cauchyDenomInterval_width_le n k)
        (mul_nonneg hm.le hm.le)
    · positivity
  have hmBase : ((9 / 2 : ℚ) * n) ^ 2 ≤ m := by
    dsimp only [m, sineCauchyDenominatorFloor]
    exact le_add_of_nonneg_left (sq_nonneg ((k : ℚ) + 1 / 4))
  calc
    width (factorTwoSineMainInterval n k) ≤
        m⁻¹ * width (yoshidaYInterval n) +
          ((91 / 20 : ℚ) * n) *
            (width (cauchyDenomInterval n k) / (m * m)) := hdiv
    _ ≤ m⁻¹ * ((n : ℚ) / 7000000000) +
        ((91 / 20 : ℚ) * n) *
          ((13 * (n : ℚ) ^ 2 / 10000000000) / (m * m)) :=
      add_le_add hfirst hsecond
    _ ≤ (1 : ℚ) / 40000000000 :=
      factorTwoSineMain_width_budget hn hm hmBase

theorem sineDyadicCorrectionInterval_valid (n k : ℕ) :
    (sineDyadicCorrectionInterval n k).Valid := by
  apply valid_div_of_pos
  · exact valid_mul (factorTwoSineMainInterval_valid n k)
      (valid_inv_of_pos sqrtTwoInterval_valid
        (lt_of_lt_of_le (by norm_num) one_le_sqrtTwoInterval_lower))
  · exact valid_pure _
  · change 0 < (4 : ℚ) ^ k
    positivity

theorem sineDyadicCorrectionInterval_absBound_quarter
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (sineDyadicCorrectionInterval n k).AbsBound (1 / 4 : ℚ) := by
  have hsValid := valid_inv_of_pos sqrtTwoInterval_valid
    (lt_of_lt_of_le (by norm_num) one_le_sqrtTwoInterval_lower)
  have hsAbs : sqrtTwoInterval⁻¹.AbsBound 1 := by
    simpa only [inv_one] using absBound_inv_of_lower
      sqrtTwoInterval_valid (by norm_num) one_le_sqrtTwoInterval_lower
  have hprodValid := valid_mul (factorTwoSineMainInterval_valid n k) hsValid
  have hprodAbs :
      (factorTwoSineMainInterval n k * sqrtTwoInterval⁻¹).AbsBound
        (1 / 4 : ℚ) := by
    simpa only [mul_one] using absBound_mul
      (factorTwoSineMainInterval_valid n k) hsValid
      (factorTwoSineMainInterval_absBound_quarter hn k) hsAbs
      (by norm_num) (by norm_num)
  have hpow : (0 : ℚ) < (4 : ℚ) ^ k := by positivity
  have hraw := absBound_div_of_lower hprodValid (valid_pure _)
    hprodAbs (by norm_num) hpow (by rfl)
  apply absBound_mono hraw
  have hpowOne : (1 : ℚ) ≤ (4 : ℚ) ^ k := one_le_pow₀ (by norm_num)
  have hinv : ((4 : ℚ) ^ k)⁻¹ ≤ 1 :=
    (inv_le_one₀ hpow).2 hpowOne
  nlinarith

theorem sineDyadicCorrectionInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    width (sineDyadicCorrectionInterval n k) ≤
      (1 : ℚ) / 39000000000 := by
  have hmainValid := factorTwoSineMainInterval_valid n k
  have hsqrtValid := valid_inv_of_pos sqrtTwoInterval_valid
    (lt_of_lt_of_le (by norm_num) one_le_sqrtTwoInterval_lower)
  have hsqrtAbs : sqrtTwoInterval⁻¹.AbsBound 1 := by
    simpa only [inv_one] using absBound_inv_of_lower
      sqrtTwoInterval_valid (by norm_num) one_le_sqrtTwoInterval_lower
  have hmul := width_mul_le hmainValid hsqrtValid
    (factorTwoSineMainInterval_absBound_quarter hn k) hsqrtAbs
    (by norm_num) (by norm_num)
  have hprodValid := valid_mul hmainValid hsqrtValid
  have hpow : (0 : ℚ) < (4 : ℚ) ^ k := by positivity
  have hpowInvLeOne : ((4 : ℚ) ^ k)⁻¹ ≤ 1 :=
    (inv_le_one₀ hpow).2 (one_le_pow₀ (by norm_num))
  change width ((factorTwoSineMainInterval n k * sqrtTwoInterval⁻¹) *
      (pure ((4 : ℚ) ^ k))⁻¹) ≤ _
  rw [show (pure ((4 : ℚ) ^ k))⁻¹ =
      pure (((4 : ℚ) ^ k)⁻¹) by rfl,
    width_mul_pure _ hprodValid,
    abs_of_nonneg (inv_nonneg.mpr hpow.le)]
  calc
    ((4 : ℚ) ^ k)⁻¹ *
        width (factorTwoSineMainInterval n k * sqrtTwoInterval⁻¹) ≤
        1 * ((1 : ℚ) / 40000000000 +
          (1 / 4 : ℚ) * (1 / 1000000000000000)) := by
      apply mul_le_mul hpowInvLeOne
      · exact hmul.trans (add_le_add
          (by simpa using factorTwoSineMainInterval_width_le hn k)
          (mul_le_mul_of_nonneg_left sqrtTwoInterval_inv_width_le
            (by norm_num)))
      · exact width_nonneg hprodValid
      · positivity
    _ ≤ (1 : ℚ) / 39000000000 := by norm_num

theorem factorTwoDyadicQInterval_valid (k : ℕ) :
    (factorTwoDyadicQInterval k).Valid := by
  exact valid_div_of_pos
    (valid_inv_of_pos sqrtTwoInterval_valid
      (lt_of_lt_of_le (by norm_num) one_le_sqrtTwoInterval_lower))
    (valid_pure _) (by change 0 < (4 : ℚ) ^ k; positivity)

theorem factorTwoDyadicQInterval_absBound_one (k : ℕ) :
    (factorTwoDyadicQInterval k).AbsBound 1 := by
  have hInvValid := valid_inv_of_pos sqrtTwoInterval_valid
    (lt_of_lt_of_le (by norm_num) one_le_sqrtTwoInterval_lower)
  have hInvAbs : sqrtTwoInterval⁻¹.AbsBound 1 := by
    simpa only [inv_one] using absBound_inv_of_lower
      sqrtTwoInterval_valid (by norm_num) one_le_sqrtTwoInterval_lower
  have hpow : (0 : ℚ) < (4 : ℚ) ^ k := by positivity
  have hraw := absBound_div_of_lower hInvValid (valid_pure _) hInvAbs
    (by norm_num) hpow (by rfl)
  apply absBound_mono hraw
  simpa only [one_mul] using
    (inv_le_one₀ hpow).2 (one_le_pow₀ (by norm_num))

theorem factorTwoDyadicQInterval_width_le (k : ℕ) :
    width (factorTwoDyadicQInterval k) ≤
      (1 : ℚ) / 1000000000000000 := by
  change width (sqrtTwoInterval⁻¹ *
    (pure ((4 : ℚ) ^ k))⁻¹) ≤ _
  rw [show (pure ((4 : ℚ) ^ k))⁻¹ =
      pure (((4 : ℚ) ^ k)⁻¹) by rfl,
    width_mul_pure _ (valid_inv_of_pos sqrtTwoInterval_valid
      (lt_of_lt_of_le (by norm_num) one_le_sqrtTwoInterval_lower))]
  rw [abs_of_nonneg (by positivity)]
  calc
    ((4 : ℚ) ^ k)⁻¹ * width sqrtTwoInterval⁻¹ ≤
        1 * width sqrtTwoInterval⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      · exact (inv_le_one₀ (by positivity :
          (0 : ℚ) < (4 : ℚ) ^ k)).2 (one_le_pow₀ (by norm_num))
      · exact width_nonneg (valid_inv_of_pos sqrtTwoInterval_valid
          (lt_of_lt_of_le (by norm_num) one_le_sqrtTwoInterval_lower))
    _ ≤ (1 : ℚ) / 1000000000000000 := by
      simpa using sqrtTwoInterval_inv_width_le

theorem factorTwoSecondDyadicCorrectionInterval_valid (n k : ℕ) :
    (factorTwoSecondDyadicCorrectionInterval n k).Valid :=
  valid_mul (sineDyadicCorrectionInterval_valid n k)
    (factorTwoDyadicQInterval_valid k)

theorem factorTwoSecondDyadicCorrectionInterval_absBound_quarter
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (factorTwoSecondDyadicCorrectionInterval n k).AbsBound (1 / 4 : ℚ) := by
  simpa only [factorTwoSecondDyadicCorrectionInterval, mul_one] using
    absBound_mul (sineDyadicCorrectionInterval_valid n k)
      (factorTwoDyadicQInterval_valid k)
      (sineDyadicCorrectionInterval_absBound_quarter hn k)
      (factorTwoDyadicQInterval_absBound_one k)
      (by norm_num) (by norm_num)

theorem factorTwoSecondDyadicCorrectionInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    width (factorTwoSecondDyadicCorrectionInterval n k) ≤
      (1 : ℚ) / 38000000000 := by
  calc
    width (factorTwoSecondDyadicCorrectionInterval n k) ≤
        1 * width (sineDyadicCorrectionInterval n k) +
          (1 / 4 : ℚ) * width (factorTwoDyadicQInterval k) := by
      exact width_mul_le (sineDyadicCorrectionInterval_valid n k)
        (factorTwoDyadicQInterval_valid k)
        (sineDyadicCorrectionInterval_absBound_quarter hn k)
        (factorTwoDyadicQInterval_absBound_one k)
        (by norm_num) (by norm_num)
    _ ≤ 1 * ((1 : ℚ) / 39000000000) +
        (1 / 4 : ℚ) * (1 / 1000000000000000) := by
      gcongr
      · exact sineDyadicCorrectionInterval_width_le hn k
      · exact factorTwoDyadicQInterval_width_le k
    _ ≤ (1 : ℚ) / 38000000000 := by norm_num

theorem sineDyadicCorrectionHeadInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) (K : ℕ) :
    width (sineDyadicCorrectionHeadInterval n K) ≤
      (K : ℚ) * ((1 : ℚ) / 39000000000) := by
  exact width_recursive_add_le_const_mul
    (sineDyadicCorrectionHeadInterval n)
    (sineDyadicCorrectionInterval n) (by rfl)
    (fun used ↦ by rw [sineDyadicCorrectionHeadInterval]) K
    (fun k _hk ↦ sineDyadicCorrectionInterval_width_le hn k)

theorem factorTwoSecondDyadicCorrectionHeadInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) (K : ℕ) :
    width (factorTwoSecondDyadicCorrectionHeadInterval n K) ≤
      (K : ℚ) * ((1 : ℚ) / 38000000000) := by
  exact width_recursive_add_le_const_mul
    (factorTwoSecondDyadicCorrectionHeadInterval n)
    (factorTwoSecondDyadicCorrectionInterval n) (by rfl)
    (fun used ↦ by rw [factorTwoSecondDyadicCorrectionHeadInterval]) K
    (fun k _hk ↦ factorTwoSecondDyadicCorrectionInterval_width_le hn k)

theorem sineDyadicCorrectionTailInterval_width_le_20
    {n : ℕ} (hn : 1 ≤ n) :
    width (sineDyadicCorrectionTailInterval n 20) ≤
      (1 : ℚ) / 2000000000000 := by
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hy : (4 : ℚ) ≤ (yoshidaYInterval n).lower := by
    calc
      (4 : ℚ) = 4 * 1 := by ring
      _ ≤ 4 * (n : ℚ) := by gcongr
      _ ≤ (yoshidaYInterval n).lower :=
        four_mul_nat_le_yoshidaYInterval_lower n
  change 2 / ((yoshidaYInterval n).lower * (4 : ℚ) ^ 20) - 0 ≤ _
  rw [sub_zero]
  calc
    2 / ((yoshidaYInterval n).lower * (4 : ℚ) ^ 20) ≤
        2 / ((4 : ℚ) * 4 ^ 20) := by
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_right hy (by positivity))
    _ ≤ (1 : ℚ) / 2000000000000 := by norm_num

theorem factorTwoSecondDyadicCorrectionTailInterval_width_le_12
    {n : ℕ} (hn : 1 ≤ n) :
    width (factorTwoSecondDyadicCorrectionTailInterval n 12) ≤
      (1 : ℚ) / 100000000000000 := by
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hy : (4 : ℚ) ≤ (yoshidaYInterval n).lower := by
    calc
      (4 : ℚ) = 4 * 1 := by ring
      _ ≤ 4 * (n : ℚ) := by gcongr
      _ ≤ (yoshidaYInterval n).lower :=
        four_mul_nat_le_yoshidaYInterval_lower n
  change 2 / ((yoshidaYInterval n).lower * (16 : ℚ) ^ 12) - 0 ≤ _
  rw [sub_zero]
  calc
    2 / ((yoshidaYInterval n).lower * (16 : ℚ) ^ 12) ≤
        2 / ((4 : ℚ) * 16 ^ 12) := by
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_right hy (by positivity))
    _ ≤ (1 : ℚ) / 100000000000000 := by norm_num

theorem sineDyadicCorrectionFullInterval_width_le_20
    {n : ℕ} (hn : 1 ≤ n) :
    width (sineDyadicCorrectionFullInterval n 20) ≤
      (1 : ℚ) / 1900000000 := by
  rw [sineDyadicCorrectionFullInterval, width_add]
  calc
    width (sineDyadicCorrectionHeadInterval n 20) +
        width (sineDyadicCorrectionTailInterval n 20) ≤
      (20 : ℚ) * ((1 : ℚ) / 39000000000) +
        (1 : ℚ) / 2000000000000 :=
      add_le_add (sineDyadicCorrectionHeadInterval_width_le hn 20)
        (sineDyadicCorrectionTailInterval_width_le_20 hn)
    _ ≤ (1 : ℚ) / 1900000000 := by norm_num

theorem factorTwoSecondDyadicCorrectionFullInterval_width_le_12
    {n : ℕ} (hn : 1 ≤ n) :
    width (factorTwoSecondDyadicCorrectionFullInterval n 12) ≤
      (1 : ℚ) / 3000000000 := by
  rw [factorTwoSecondDyadicCorrectionFullInterval, width_add]
  calc
    width (factorTwoSecondDyadicCorrectionHeadInterval n 12) +
        width (factorTwoSecondDyadicCorrectionTailInterval n 12) ≤
      (12 : ℚ) * ((1 : ℚ) / 38000000000) +
        (1 : ℚ) / 100000000000000 :=
      add_le_add
        (factorTwoSecondDyadicCorrectionHeadInterval_width_le hn 12)
        (factorTwoSecondDyadicCorrectionTailInterval_width_le_12 hn)
    _ ≤ (1 : ℚ) / 3000000000 := by norm_num

private theorem valid_neg {I : RatInterval} (hI : I.Valid) : (-I).Valid := by
  change -I.upper ≤ -I.lower
  exact neg_le_neg hI

private theorem absBound_neg {I : RatInterval} {B : ℚ}
    (hI : I.AbsBound B) : (-I).AbsBound B := by
  change -B ≤ -I.upper ∧ -I.lower ≤ B
  exact ⟨neg_le_neg hI.2, by simpa using neg_le_neg hI.1⟩

private theorem width_neg (I : RatInterval) : width (-I) = width I := by
  change -I.lower - -I.upper = I.upper - I.lower
  ring

theorem factorTwoHeadDefectInterval_valid :
    factorTwoHeadDefectInterval.Valid :=
  valid_of_contains factorTwoHeadDefectInterval_contains

theorem factorTwoHeadDefectInterval_absBound_quarter :
    factorTwoHeadDefectInterval.AbsBound (1 / 4 : ℚ) := by
  have hsubValid := valid_sub sqrtTwoInterval_valid (valid_pure 1)
  have hsubAbs : (sqrtTwoInterval - RatInterval.pure 1).AbsBound
      (1 / 2 : ℚ) := by
    change -(1 / 2 : ℚ) ≤ sqrtTwoInterval.lower - 1 ∧
      sqrtTwoInterval.upper - 1 ≤ (1 / 2 : ℚ)
    norm_num [sqrtTwoInterval]
  unfold factorTwoHeadDefectInterval
  have h := absBound_mul hsubValid hsubValid hsubAbs hsubAbs
    (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem factorTwoSymmetricSinHeadInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) :
    width (factorTwoSymmetricSinHeadInterval n) ≤
      (1 : ℚ) / 300000000000 := by
  let C := -(factorTwoHeadDefectInterval / RatInterval.pure 2)
  have hdefValid := factorTwoHeadDefectInterval_valid
  have hdivValid := valid_div_of_pos hdefValid (valid_pure 2)
    (by norm_num [RatInterval.pure])
  have hdivAbs : (factorTwoHeadDefectInterval / pure 2).AbsBound
      (1 / 8 : ℚ) := by
    have hraw := absBound_div_of_lower (m := (2 : ℚ))
      hdefValid (valid_pure 2)
      factorTwoHeadDefectInterval_absBound_quarter (by norm_num)
      (by norm_num) (by rfl)
    norm_num at hraw ⊢
    exact hraw
  have hCValid : C.Valid := valid_neg hdivValid
  have hCAbs : C.AbsBound (1 / 8 : ℚ) := absBound_neg hdivAbs
  have hCWidth : width C ≤ (1 : ℚ) / 200000000000000 := by
    dsimp only [C]
    rw [width_neg]
    change width (factorTwoHeadDefectInterval *
      (RatInterval.pure 2)⁻¹) ≤ _
    rw [show (RatInterval.pure (2 : ℚ))⁻¹ =
        RatInterval.pure (1 / 2 : ℚ) by
          change (⟨(2 : ℚ)⁻¹, (2 : ℚ)⁻¹⟩ : RatInterval) =
            ⟨(1 / 2 : ℚ), (1 / 2 : ℚ)⟩
          norm_num,
      width_mul_pure _ hdefValid]
    rw [abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 2)]
    calc
      (1 / 2 : ℚ) * width factorTwoHeadDefectInterval ≤
          (1 / 2 : ℚ) * (1 / 100000000000000 : ℚ) :=
        mul_le_mul_of_nonneg_left
          factorTwoPerturbationConstantIntervals_width_le.2.2 (by norm_num)
      _ = (1 : ℚ) / 200000000000000 := by norm_num
  change width (C * factorTwoSineMainInterval n 0) ≤ _
  calc
    width (C * factorTwoSineMainInterval n 0) ≤
        (1 / 4 : ℚ) * width C +
          (1 / 8 : ℚ) * width (factorTwoSineMainInterval n 0) := by
      exact width_mul_le hCValid (factorTwoSineMainInterval_valid n 0)
        hCAbs (factorTwoSineMainInterval_absBound_quarter hn 0)
        (by norm_num) (by norm_num)
    _ ≤ (1 / 4 : ℚ) * (1 / 200000000000000 : ℚ) +
        (1 / 8 : ℚ) * (1 / 40000000000 : ℚ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hCWidth (by norm_num))
        (mul_le_mul_of_nonneg_left
          (factorTwoSineMainInterval_width_le hn 0) (by norm_num))
    _ ≤ (1 : ℚ) / 300000000000 := by norm_num

theorem factorTwoPrimeBetaInterval_valid : factorTwoPrimeBetaInterval.Valid :=
  valid_of_contains factorTwoPrimeBetaInterval_contains

theorem factorTwoPrimeBetaInterval_absBound_one :
    factorTwoPrimeBetaInterval.AbsBound 1 := by
  have hlogTwoValid := valid_of_contains factorTwoPrimeLogTwoInterval_contains
  have hshiftValid := valid_of_contains factorTwoPrimeShiftInterval_contains
  have hlogTwoAbs : factorTwoPrimeLogTwoInterval.AbsBound 1 := by
    norm_num [AbsBound, factorTwoPrimeLogTwoInterval]
  have hshiftAbs : factorTwoPrimeShiftInterval.AbsBound (1 / 2 : ℚ) := by
    norm_num [AbsBound, factorTwoPrimeShiftInterval]
  have hlogThreeValid : factorTwoPrimeLogThreeInterval.Valid :=
    valid_add hlogTwoValid hshiftValid
  have hlogThreeAbs : factorTwoPrimeLogThreeInterval.AbsBound (3 / 2 : ℚ) := by
    unfold factorTwoPrimeLogThreeInterval
    have h := absBound_add hlogTwoAbs hshiftAbs
    norm_num at h ⊢
    exact h
  have hsqrtValid := valid_of_contains factorTwoPrimeSqrtThreeInterval_contains
  have hsqrtLower : (3 / 2 : ℚ) ≤
      factorTwoPrimeSqrtThreeInterval.lower := by
    norm_num [factorTwoPrimeSqrtThreeInterval]
  have hraw := absBound_div_of_lower (m := (3 / 2 : ℚ))
    hlogThreeValid hsqrtValid hlogThreeAbs (by norm_num) (by norm_num)
    hsqrtLower
  norm_num at hraw ⊢
  exact hraw

theorem factorTwoPrimeSinInterval_valid (n : Fin 201) :
    (factorTwoPrimeSinInterval n).Valid :=
  valid_of_contains (factorTwoPrimeSinInterval_contains n)

theorem factorTwoPrimeSinInterval_absBound_two (n : Fin 201) :
    (factorTwoPrimeSinInterval n).AbsBound 2 := by
  have hx := factorTwoPrimeSinInterval_contains n
  have hwq := factorTwoPrimeSinInterval_width_le n
  have hwCast := (Rat.cast_le (K := ℝ)).2 hwq
  have hw : (((factorTwoPrimeSinInterval n).upper : ℚ) : ℝ) -
      (((factorTwoPrimeSinInterval n).lower : ℚ) : ℝ) ≤
      (1 / 10000000000 : ℝ) := by
    rw [width] at hwCast
    norm_num only [Rat.cast_sub] at hwCast
    norm_num at hwCast ⊢
    exact hwCast
  have hxBounds : (-1 : ℝ) ≤
        Real.sin (2 * factorTwoMomentY n.1 * factorTwoPrimeShift) ∧
      Real.sin (2 * factorTwoMomentY n.1 * factorTwoPrimeShift) ≤ 1 :=
    ⟨neg_one_le_sin _, sin_le_one _⟩
  have hlower : (-2 : ℝ) ≤
      (((factorTwoPrimeSinInterval n).lower : ℚ) : ℝ) := by
    nlinarith [hx.2, hxBounds.1, hw]
  have hupper : (((factorTwoPrimeSinInterval n).upper : ℚ) : ℝ) ≤
      2 := by
    nlinarith [hx.1, hxBounds.2, hw]
  constructor
  · exact_mod_cast hlower
  · exact_mod_cast hupper

theorem factorTwoSymmetricSinPrimeInterval_width_le
    (n : FactorTwoCanonicalEvenIndex) :
    width (factorTwoSymmetricSinPrimeInterval n) ≤
      (1 : ℚ) / 9000000000 := by
  calc
    width (factorTwoSymmetricSinPrimeInterval n) ≤
        2 * width factorTwoPrimeBetaInterval +
          1 * width (factorTwoPrimeSinInterval n) := by
      exact width_mul_le factorTwoPrimeBetaInterval_valid
        (factorTwoPrimeSinInterval_valid n)
        factorTwoPrimeBetaInterval_absBound_one
        (factorTwoPrimeSinInterval_absBound_two n)
        (by norm_num) (by norm_num)
    _ ≤ 2 * (1 / 10000000000000 : ℚ) +
        1 * (1 / 10000000000 : ℚ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          factorTwoPerturbationConstantIntervals_width_le.1 (by norm_num))
        (mul_le_mul_of_nonneg_left
          (factorTwoPrimeSinInterval_width_le n) (by norm_num))
    _ ≤ (1 : ℚ) / 9000000000 := by norm_num

/-- The production checkpoint schedule has a uniform half-nanounit width on
the complementary low band.  The proof uses one finite-head estimate, one
rounding estimate, and the analytic ninth-order tail bound. -/
theorem higherRoundedSineCauchySeriesLow_width_le
    {n : ℕ} (hn : 1 ≤ n) (hn152 : n ≤ 152) :
    width (higherRoundedSineCauchySeriesInterval n (n / 6 + 1)
      1000000000000000000) ≤ (1 : ℚ) / 2000000000 := by
  have hKmin : 256 ≤ 256 * (n / 6 + 1) := by omega
  have hKratio : 300 * n ≤ 7 * (256 * (n / 6 + 1)) := by omega
  have htail := higherSineCauchyTailInterval_width_le hn hKmin hKratio
  have hblocks : n / 6 + 1 ≤ 26 := by omega
  calc
    width (higherRoundedSineCauchySeriesInterval n (n / 6 + 1)
        1000000000000000000) ≤
        (1 : ℚ) / 4500000000 +
          ((n / 6 + 1 : ℕ) : ℚ) *
            (2 / 1000000000000000000) +
          (1 : ℚ) / 4000000000 := by
      exact higherRoundedSineCauchySeriesInterval_width_le_uniform hn
        (n / 6 + 1) (by norm_num) htail
    _ ≤ (1 : ℚ) / 4500000000 +
          (26 : ℚ) * (2 / 1000000000000000000) +
          (1 : ℚ) / 4000000000 := by
      gcongr
      exact_mod_cast hblocks
    _ ≤ (1 : ℚ) / 2000000000 := by norm_num

/-- Every positive mode below the cubic construction's high-mode cutoff has
width at most `10⁻⁹`.  This proof is uniform in the mode: it combines
structural component estimates for the checkpoint head, accelerated tail,
dyadic corrections, and retained-prime phase. -/
theorem factorTwoSymmetricSinLowInterval_width_le
    (n : FactorTwoCanonicalEvenIndex) (hn001 : 1 ≤ n.1)
    (hn152 : n.1 ≤ 152) :
    width (factorTwoSymmetricSinLowInterval n) ≤
      (1 / 1000000000 : ℚ) := by
  let S := higherRoundedSineCauchySeriesInterval n.1 (n.1 / 6 + 1)
    1000000000000000000
  let F := sineDyadicCorrectionFullInterval n.1 20
  let M := factorTwoSineMainInterval n.1 0
  let Z := sineDyadicCorrectionInterval n.1 0
  let G := factorTwoSecondDyadicCorrectionFullInterval n.1 12
  let H := factorTwoSecondDyadicCorrectionInterval n.1 0
  let core := ((S - F - M + pure 2 * Z) + (G - H))
  have hSValid : S.Valid := by
    dsimp only [S]
    exact valid_of_contains
      (higherRoundedSineCauchySeriesInterval_contains
        (n := n.1) (blocks := n.1 / 6 + 1)
        (scale := 1000000000000000000) (by omega) (by omega) (by norm_num))
  have hFValid : F.Valid := by
    dsimp only [F]
    exact valid_of_contains (sineDyadicCorrectionFullInterval_contains
      (by omega) 20)
  have hMValid : M.Valid := by
    dsimp only [M]
    exact factorTwoSineMainInterval_valid n.1 0
  have hZValid : Z.Valid := by
    dsimp only [Z]
    exact sineDyadicCorrectionInterval_valid n.1 0
  have hGValid : G.Valid := by
    dsimp only [G]
    exact valid_of_contains
      (factorTwoSecondDyadicCorrectionFullInterval_contains (by omega) 12)
  have hHValid : H.Valid := by
    dsimp only [H]
    exact factorTwoSecondDyadicCorrectionInterval_valid n.1 0
  have hcoreValid : core.Valid := by
    dsimp only [core]
    exact valid_add
      (valid_add (valid_sub (valid_sub hSValid hFValid) hMValid)
        (valid_mul (valid_pure 2) hZValid))
      (valid_sub hGValid hHValid)
  have hSWidth : width S ≤ (1 : ℚ) / 2000000000 := by
    dsimp only [S]
    exact higherRoundedSineCauchySeriesLow_width_le hn001 hn152
  have hFWidth : width F ≤ (1 : ℚ) / 1900000000 := by
    dsimp only [F]
    exact sineDyadicCorrectionFullInterval_width_le_20 hn001
  have hMWidth : width M ≤ (1 : ℚ) / 40000000000 := by
    dsimp only [M]
    exact factorTwoSineMainInterval_width_le hn001 0
  have hZWidth : width Z ≤ (1 : ℚ) / 39000000000 := by
    dsimp only [Z]
    exact sineDyadicCorrectionInterval_width_le hn001 0
  have hGWidth : width G ≤ (1 : ℚ) / 3000000000 := by
    dsimp only [G]
    exact factorTwoSecondDyadicCorrectionFullInterval_width_le_12 hn001
  have hHWidth : width H ≤ (1 : ℚ) / 38000000000 := by
    dsimp only [H]
    exact factorTwoSecondDyadicCorrectionInterval_width_le hn001 0
  have hcoreWidth : width core ≤
      ((((1 : ℚ) / 2000000000 + (1 : ℚ) / 1900000000) +
          (1 : ℚ) / 40000000000) +
          2 * ((1 : ℚ) / 39000000000)) +
        ((1 : ℚ) / 3000000000 + (1 : ℚ) / 38000000000) := by
    dsimp only [core]
    rw [width_add (S - F - M + pure 2 * Z) (G - H),
      width_add (S - F - M) (pure 2 * Z),
      width_sub (S - F) M, width_sub S F,
      width_pure_mul 2 hZValid, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 2),
      width_sub G H]
    exact add_le_add
      (add_le_add
        (add_le_add (add_le_add hSWidth hFWidth) hMWidth)
        (mul_le_mul_of_nonneg_left hZWidth (by norm_num)))
      (add_le_add hGWidth hHWidth)
  change width
    (factorTwoSymmetricSinHeadInterval n.1 + pure (1 / 2) * core -
      factorTwoSymmetricSinPrimeInterval n) ≤ _
  rw [width_sub, width_add, width_pure_mul (1 / 2) hcoreValid,
    abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 2)]
  calc
    width (factorTwoSymmetricSinHeadInterval n.1) +
          (1 / 2 : ℚ) * width core +
        width (factorTwoSymmetricSinPrimeInterval n) ≤
      (1 : ℚ) / 300000000000 +
          (1 / 2 : ℚ) *
            (((((1 : ℚ) / 2000000000 + (1 : ℚ) / 1900000000) +
                (1 : ℚ) / 40000000000) +
                2 * ((1 : ℚ) / 39000000000)) +
              ((1 : ℚ) / 3000000000 + (1 : ℚ) / 38000000000)) +
        (1 : ℚ) / 9000000000 := by
      exact add_le_add
        (add_le_add (factorTwoSymmetricSinHeadInterval_width_le hn001)
          (mul_le_mul_of_nonneg_left hcoreWidth (by norm_num)))
        (factorTwoSymmetricSinPrimeInterval_width_le n)
    _ ≤ (1 / 1000000000 : ℚ) := by norm_num

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationSinLowEnclosures
