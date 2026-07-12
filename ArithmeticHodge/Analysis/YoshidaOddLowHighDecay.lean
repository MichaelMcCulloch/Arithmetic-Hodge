import ArithmeticHodge.Analysis.YoshidaOddRealSpaceAssembly
import ArithmeticHodge.Analysis.YoshidaSineMomentEnclosures
import ArithmeticHodge.Analysis.YoshidaWeightedTailBounds

/-!
# Yoshida's odd low/high coupling reduction

The exact real-space pairing formula reduces every odd low/high entry to two
sine moments.  The already certified low-mode boxes show that the entire
source pointwise decay (6.18), and hence its infinite `19 / 500` coupling
budget, follows from one scalar high-mode window:

`-79 / 50 ≤ Sₙ ≤ -31 / 20` for every `n ≥ 11`.

The scalar window remains an explicit premise.  This module proves the exact
reduction; it does not assume form boundedness or odd-tail coercivity.
-/

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaOddLowHighDecay

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaClippedMomentBridge
open YoshidaMomentIntegrability
open YoshidaOddGramPrefix
open YoshidaOddMomentTargets
open YoshidaSineMomentEnclosures
open YoshidaWeightedTailBounds

theorem oddMomentGram_offdiag_simplify
    (S D : ℕ → ℝ) {n m : ℕ} (hnm : n ≠ m) :
    oddMomentGram S D n m =
      (-1 : ℝ) ^ (n + m) *
        (((n : ℝ) * S m - (m : ℝ) * S n) /
          (Real.pi * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2))) := by
  rw [oddMomentGram, if_neg hnm]
  unfold yoshidaKappa
  field_simp [yoshidaLength_pos.ne', Real.pi_ne_zero]

/-- A compact uniform consequence of the certified first-ten sine boxes. -/
theorem odd_low_sine_uniform_bounds (i : YoshidaOddIndex) :
    (-196 / 125 : ℝ) ≤ yoshidaSineMoment (i.1 + 1) ∧
      yoshidaSineMoment (i.1 + 1) ≤ (-1441 / 1000 : ℝ) := by
  have h := sineTargetEnclosures_from_series192
    (i.1 + 1) (by omega) (by omega)
  constructor
  · have hbox : (-196 / 125 : ℝ) ≤
        ((yoshidaOddSineIntervals (i.1 + 1)).lower : ℚ) := by
      fin_cases i <;> norm_num [yoshidaOddSineIntervals]
    exact hbox.trans h.1
  · have hbox :
        ((yoshidaOddSineIntervals (i.1 + 1)).upper : ℚ) ≤
          (-1441 / 1000 : ℝ) := by
      fin_cases i <;> norm_num [yoshidaOddSineIntervals]
    exact h.2.trans hbox

/-- The scalar high-mode input sufficient for Yoshida's odd low/high decay. -/
def YoshidaOddHighSineBounds : Prop :=
  ∀ n : ℕ, 11 ≤ n →
    (-79 / 50 : ℝ) ≤ yoshidaSineMoment n ∧
      yoshidaSineMoment n ≤ (-31 / 20 : ℝ)

theorem abs_oddMomentGram_low_high_le
    (hHigh : YoshidaOddHighSineBounds)
    (i : YoshidaOddIndex) (k : ℕ) :
    |oddMomentGram yoshidaSineMoment yoshidaDiagonalMoment
        (11 + k) (i.1 + 1)| ≤
      (196 / 125 : ℝ) /
        (Real.pi * ((11 + k : ℕ) : ℝ)) := by
  let n : ℕ := 11 + k
  let m : ℕ := i.1 + 1
  have hn11 : 11 ≤ n := by omega
  have hm1 : 1 ≤ m := by omega
  have hm10 : m ≤ 10 := by omega
  have hmn : m < n := by omega
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 11) hn11)
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hden : (0 : ℝ) < (n : ℝ) ^ 2 - (m : ℝ) ^ 2 := by
    nlinarith [show (m : ℝ) < n by exact_mod_cast hmn]
  have hLow := odd_low_sine_uniform_bounds i
  have hHighN := hHigh n hn11
  have hnSmUpper := mul_le_mul_of_nonneg_left hLow.2 hn0.le
  have hmSnLower := mul_le_mul_of_nonneg_left hHighN.1 hm0
  have hnumNonpos :
      (n : ℝ) * yoshidaSineMoment m -
          (m : ℝ) * yoshidaSineMoment n ≤ 0 := by
    dsimp only [m] at hLow ⊢
    dsimp only [n] at hHighN hnSmUpper hmSnLower ⊢
    nlinarith [show (n : ℝ) ≥ 11 by exact_mod_cast hn11,
      show (m : ℝ) ≤ 10 by exact_mod_cast hm10]
  have hmSnUpper := mul_le_mul_of_nonneg_left hHighN.2 hm0
  have hnSmLower := mul_le_mul_of_nonneg_left hLow.1 hn0.le
  have hqUpper :
      (m : ℝ) * yoshidaSineMoment n -
          (n : ℝ) * yoshidaSineMoment m ≤
        (n : ℝ) * (196 / 125 : ℝ) -
          (m : ℝ) * (31 / 20 : ℝ) := by
    dsimp only [m] at hLow ⊢
    dsimp only [n] at hHighN hmSnUpper hnSmLower ⊢
    nlinarith
  have hratio :
      ((m : ℝ) * yoshidaSineMoment n -
          (n : ℝ) * yoshidaSineMoment m) /
          ((n : ℝ) ^ 2 - (m : ℝ) ^ 2) ≤
        (196 / 125 : ℝ) / (n : ℝ) := by
    apply (div_le_div_iff₀ hden hn0).2
    have hcross :
        (196 / 125 : ℝ) * (m : ℝ) ≤ (31 / 20 : ℝ) * (n : ℝ) := by
      nlinarith [show (n : ℝ) ≥ 11 by exact_mod_cast hn11,
        show (m : ℝ) ≤ 10 by exact_mod_cast hm10]
    nlinarith
  rw [oddMomentGram_offdiag_simplify _ _ (by omega : n ≠ m)]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_div, abs_of_nonpos hnumNonpos, neg_sub]
  rw [abs_of_pos Real.pi_pos, abs_of_pos hden]
  calc
    ((m : ℝ) * yoshidaSineMoment n -
          (n : ℝ) * yoshidaSineMoment m) /
        (Real.pi * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2)) =
      (((m : ℝ) * yoshidaSineMoment n -
          (n : ℝ) * yoshidaSineMoment m) /
        ((n : ℝ) ^ 2 - (m : ℝ) ^ 2)) / Real.pi := by
          field_simp [Real.pi_ne_zero, ne_of_gt hden]
    _ ≤ ((196 / 125 : ℝ) / (n : ℝ)) / Real.pi := by gcongr
    _ = (196 / 125 : ℝ) / (Real.pi * (n : ℝ)) := by
      field_simp [Real.pi_ne_zero, ne_of_gt hn0]

theorem oddMomentGram_low_high_sq_le
    (hHigh : YoshidaOddHighSineBounds)
    (i : YoshidaOddIndex) (k : ℕ) :
    |oddMomentGram yoshidaSineMoment yoshidaDiagonalMoment
        (11 + k) (i.1 + 1)| ^ 2 ≤
      (19 / 50 : ℝ) / (((11 + k : ℕ) : ℝ) ^ 2) := by
  have h := abs_oddMomentGram_low_high_le hHigh i k
  have hn : (0 : ℝ) < ((11 + k : ℕ) : ℝ) := by positivity
  have hrhs : 0 ≤
      (196 / 125 : ℝ) / (Real.pi * ((11 + k : ℕ) : ℝ)) := by positivity
  have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
  calc
    |oddMomentGram yoshidaSineMoment yoshidaDiagonalMoment
        (11 + k) (i.1 + 1)| ^ 2 ≤
      ((196 / 125 : ℝ) /
        (Real.pi * ((11 + k : ℕ) : ℝ))) ^ 2 := hsq
    _ ≤ (19 / 50 : ℝ) / (((11 + k : ℕ) : ℝ) ^ 2) := by
      have hpi := Real.pi_gt_three
      field_simp [Real.pi_ne_zero, ne_of_gt hn]
      nlinarith [sq_nonneg (Real.pi - 3)]

/-- The actual clipped low/high entry is the exact off-diagonal moment formula. -/
theorem odd_low_high_pairing_eq_moment
    (i : YoshidaOddIndex) (k : ℕ) :
    yoshidaClippedLocalCriticalForm yoshidaHalfLength yoshidaHalfLength_pos
        (yoshidaClippedOddMode yoshidaHalfLength (11 + k))
        (yoshidaClippedOddLowMode yoshidaHalfLength i) =
      (oddMomentGram yoshidaSineMoment yoshidaDiagonalMoment
        (11 + k) (i.1 + 1) : ℂ) := by
  rw [yoshidaClippedLocalCriticalForm_apply]
  unfold yoshidaClippedOddLowMode
  rw [YoshidaOddRealSpaceAssembly.yoshidaClippedLocalCriticalPairing_odd_eq_admissible
    (by omega : 11 + k ≠ 0) (by omega : i.1 + 1 ≠ 0)]
  norm_cast
  exact clippedOddAdmissibleRealSpaceGram_offdiag_eq_oddMomentGram
    (by omega) (by omega) (by omega)
    (yoshidaSineMomentIntegrand_intervalIntegrable (by omega))
    (yoshidaSineMomentIntegrand_intervalIntegrable (by omega))

/-- Uniform high sine-moment bounds imply Yoshida's concrete pointwise odd
low/high decay (6.18), with the certified source constant. -/
theorem odd_low_high_pairing_decay_of_high_sine_bounds
    (hHigh : YoshidaOddHighSineBounds)
    (i : YoshidaOddIndex) (k : ℕ) :
    ‖yoshidaClippedLocalCriticalForm yoshidaHalfLength yoshidaHalfLength_pos
        (yoshidaClippedOddMode yoshidaHalfLength (11 + k))
        (yoshidaClippedOddLowMode yoshidaHalfLength i)‖ ^ 2 ≤
      (19 / 50 : ℝ) / (((11 + k : ℕ) : ℝ) ^ 2) := by
  rw [odd_low_high_pairing_eq_moment]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    oddMomentGram_low_high_sq_le hHigh i k

/-- Actual squared coupling energy for one of the ten odd low modes. -/
def oddLowTailCouplingEnergy (i : YoshidaOddIndex) : ℝ :=
  ∑' k : ℕ,
    ‖yoshidaClippedLocalCriticalForm yoshidaHalfLength yoshidaHalfLength_pos
      (yoshidaClippedOddMode yoshidaHalfLength (11 + k))
      (yoshidaClippedOddLowMode yoshidaHalfLength i)‖ ^ 2

/-- The scalar high sine-moment window closes the full odd source coupling
budget, not merely each pointwise entry. -/
theorem oddLowTailCouplingEnergy_le_of_high_sine_bounds
    (hHigh : YoshidaOddHighSineBounds) (i : YoshidaOddIndex) :
    oddLowTailCouplingEnergy i ≤ 19 / 500 := by
  let actual : ℕ → ℝ := fun k ↦
    ‖yoshidaClippedLocalCriticalForm yoshidaHalfLength yoshidaHalfLength_pos
      (yoshidaClippedOddMode yoshidaHalfLength (11 + k))
      (yoshidaClippedOddLowMode yoshidaHalfLength i)‖ ^ 2
  let major : ℕ → ℝ := fun k ↦
    (19 / 50 : ℝ) / (((11 + k : ℕ) : ℝ) ^ 2)
  have hpoint : ∀ k, actual k ≤ major k :=
    odd_low_high_pairing_decay_of_high_sine_bounds hHigh i
  have hmajor : Summable major := by
    have hp : Summable (fun n : ℕ ↦
        ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
      exact (summable_nat_add_iff 1).2
        (Real.summable_nat_pow_inv.mpr (by norm_num))
    have hs : Summable (fun k : ℕ ↦
        1 / (((10 + 1 + k : ℕ) : ℝ) ^ 2)) := by
      simpa [one_div, Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
        add_left_comm] using (summable_nat_add_iff 10).2 hp
    convert hs.mul_left (19 / 50 : ℝ) using 1
    funext k
    norm_num [major, div_eq_mul_inv]
  have hactual : Summable actual :=
    hmajor.of_nonneg_of_le (fun k ↦ sq_nonneg _) hpoint
  have hsum := hactual.tsum_le_tsum hpoint hmajor
  unfold oddLowTailCouplingEnergy
  change (∑' k, actual k) ≤ 19 / 500
  calc
    (∑' k, actual k) ≤ ∑' k, major k := hsum
    _ = (19 / 50 : ℝ) *
        (∑' k : ℕ, 1 / (((10 + 1 + k : ℕ) : ℝ) ^ 2)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      norm_num [major, div_eq_mul_inv]
    _ ≤ (19 / 50 : ℝ) * (1 / (10 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (invSq_tail_le 10 (by norm_num))
        (by norm_num)
    _ = 19 / 500 := by norm_num

end

end ArithmeticHodge.Analysis.YoshidaOddLowHighDecay
