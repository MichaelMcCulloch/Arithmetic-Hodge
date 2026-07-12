import ArithmeticHodge.Analysis.YoshidaEvenPairingBridge
import ArithmeticHodge.Analysis.YoshidaClippedParityOrthogonality
import ArithmeticHodge.Analysis.YoshidaSectionSixAnalytic

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaEvenTailReduction

noncomputable section

open YoshidaCoercivityNumerics
open YoshidaEvenPairingBridge
open YoshidaSectionSixAnalytic
open YoshidaWeightedTailBounds

/-!
# Exact reductions for Yoshida's canonical even tail

This module records the lossless algebraic and summability consequences of
the existing Section 6 certificates for the canonical even cutoff.  The low
block is exactly the normalized zero mode and modes `1, ..., 199`; the tail
starts at `200 + k`.

Two analytic estimates remain explicit premises rather than conclusions:

* the homogeneous form of Yoshida's equation (6.7), needed for coercivity;
* the pointwise low/high decay (6.26), needed for the coupling budget.

The exact even pairing bridge supplies the concrete entries, while the
certified inverse-square tail closes the source budget without enlarging the
finite block.  Even parity does completely discharge the polar premise: its
polar energy is nonnegative.
-/

/-- The Lebesgue `L²` square appearing in Yoshida's coercivity statement. -/
def clippedLebesgueNormSq
    (a : ℝ) (f : YoshidaClippedSmooth a) : ℝ :=
  ∫ x in -a..a, ‖f x‖ ^ 2

/-- The clipped Lebesgue `L²` square is nonnegative on a nondegenerate
symmetric interval. -/
theorem clippedLebesgueNormSq_nonneg
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    0 ≤ clippedLebesgueNormSq a f := by
  unfold clippedLebesgueNormSq
  exact intervalIntegral.integral_nonneg (by linarith) fun _ _ ↦ sq_nonneg _

/-- The polar contribution causes no loss for a pointwise-even clipped
function. -/
theorem clippedPolarEnergy_nonneg_of_even
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (heven : ∀ x : ℝ, f (-x) = f x) :
    0 ≤ clippedPolarEnergy a ha f := by
  unfold clippedPolarEnergy
  rw [← yoshidaPositivePolar_even_eq_negative ha f heven]
  have hsq :
      (star (yoshidaPositivePolarLinear a ha f) *
        yoshidaPositivePolarLinear a ha f).re =
        Complex.normSq (yoshidaPositivePolarLinear a ha f) := by
    simp [Complex.mul_re, Complex.normSq_apply]
  rw [hsq]
  exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)

/-- Pointwise evenness supplies the polar lower bound used in Section 6. -/
theorem even_polar_section6_lower_bound
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (heven : ∀ x : ℝ, f (-x) = f x) :
    -(1 / Real.sqrt 2 - Real.log 2) ≤ clippedPolarEnergy a ha f := by
  have hloss : 0 ≤ 1 / Real.sqrt 2 - Real.log 2 := by
    have hsqrt : (7 / 5 : ℝ) < Real.sqrt 2 := by
      have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hinv : (7 / 10 : ℝ) < 1 / Real.sqrt 2 := by
      rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 10)
        (Real.sqrt_pos.2 (by norm_num))]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hlog : Real.log 2 < (7 / 10 : ℝ) :=
      Real.log_two_lt_d9.trans (by norm_num)
    linarith
  exact (neg_nonpos.mpr hloss).trans
    (clippedPolarEnergy_nonneg_of_even ha f heven)

/-- Exact homogeneous Section-(6.7) boundary for the even tail.

The displayed premise is the still-unproved homogeneous analytic inequality
on the canonical periodic even tail.  The certified numerical layer then
gives the source coercivity constant `102 / 25` with no further loss. -/
theorem even_coercivity_of_scaled_equation6_7
    (f : YoshidaClippedSmooth yoshidaA)
    (hequation6_7 :
      section6LowerBound 199 YoshidaTZeroTailBounds.yoshidaTZero 700 *
          clippedLebesgueNormSq yoshidaA f ≤
        clippedCriticalFormValue yoshidaA yoshidaA_pos f) :
    (102 / 25 : ℝ) * clippedLebesgueNormSq yoshidaA f ≤
      clippedCriticalFormValue yoshidaA yoshidaA_pos f := by
  exact (mul_le_mul_of_nonneg_right even_section6_lowerBound_ge
    (clippedLebesgueNormSq_nonneg yoshidaA_pos f)).trans hequation6_7

/-- The actual squared low/high coupling sum for a canonical even low mode.
The high index is exactly `200 + k`; the finite block is not enlarged. -/
def evenLowTailCouplingEnergy
    (a : ℝ) (ha : 0 < a) (i : YoshidaEvenIndex) : ℝ :=
  ∑' k : ℕ,
    ‖yoshidaClippedLocalCriticalForm a ha
      (yoshidaClippedEvenLowMode a i)
      (yoshidaClippedEvenMode a (200 + k))‖ ^ 2

/-- A pointwise inverse-square estimate with Yoshida's certified even
constant gives the exact source coupling budget `51 / 25000`.

The pointwise hypothesis is precisely the still-unproved concrete content of
Yoshida's equation (6.26), expressed through the exact removable-safe
Laplace pairing formula. -/
theorem evenLowTailCouplingEnergy_le_of_decay
    {a : ℝ} (ha : 0 < a) (i : YoshidaEvenIndex)
    (hdecay : ∀ k : ℕ,
      ‖yoshidaClippedEvenLowModePairingFormula a i (200 + k)‖ ^ 2 ≤
        (10149 / 25000 : ℝ) /
          (((200 + k : ℕ) : ℝ) ^ 2)) :
    evenLowTailCouplingEnergy a ha i ≤ 51 / 25000 := by
  have hpoint : ∀ k : ℕ,
      ‖yoshidaClippedLocalCriticalForm a ha
        (yoshidaClippedEvenLowMode a i)
        (yoshidaClippedEvenMode a (200 + k))‖ ^ 2 ≤
          (10149 / 25000 : ℝ) /
            (((200 + k : ℕ) : ℝ) ^ 2) := by
    intro k
    rw [yoshidaClippedLocalCriticalForm_evenLowMode_tail_eq_formula]
    exact hdecay k
  have hmajor : Summable (fun k : ℕ ↦
      (10149 / 25000 : ℝ) /
        (((200 + k : ℕ) : ℝ) ^ 2)) := by
    have hs : Summable (fun k : ℕ ↦
        1 / (((199 + 1 + k : ℕ) : ℝ) ^ 2)) := by
      have hp : Summable (fun n : ℕ ↦
          ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
        exact (summable_nat_add_iff 1).2
          (Real.summable_nat_pow_inv.mpr (by norm_num))
      simpa [one_div, Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
        add_left_comm] using
        (summable_nat_add_iff 199).2 hp
    convert hs.mul_left (10149 / 25000 : ℝ) using 1
    funext k
    norm_num [div_eq_mul_inv]
  have hactual : Summable (fun k : ℕ ↦
      ‖yoshidaClippedLocalCriticalForm a ha
        (yoshidaClippedEvenLowMode a i)
        (yoshidaClippedEvenMode a (200 + k))‖ ^ 2) :=
    hmajor.of_nonneg_of_le (fun k ↦ sq_nonneg _) hpoint
  have hsum := hactual.tsum_le_tsum hpoint hmajor
  unfold evenLowTailCouplingEnergy
  calc
    (∑' k : ℕ,
        ‖yoshidaClippedLocalCriticalForm a ha
          (yoshidaClippedEvenLowMode a i)
          (yoshidaClippedEvenMode a (200 + k))‖ ^ 2) ≤
        ∑' k : ℕ,
          (10149 / 25000 : ℝ) /
            (((200 + k : ℕ) : ℝ) ^ 2) := hsum
    _ = (10149 / 25000 : ℝ) *
        (∑' k : ℕ, 1 / (((199 + 1 + k : ℕ) : ℝ) ^ 2)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      norm_num [div_eq_mul_inv]
    _ ≤ (10149 / 25000 : ℝ) * (1 / (199 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (invSq_tail_le 199 (by norm_num))
        (by norm_num)
    _ = 51 / 25000 := by norm_num

end

end ArithmeticHodge.Analysis.YoshidaEvenTailReduction
