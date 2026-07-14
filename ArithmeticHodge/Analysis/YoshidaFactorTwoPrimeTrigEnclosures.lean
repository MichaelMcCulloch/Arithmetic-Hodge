import ArithmeticHodge.Analysis.RationalIntervalWidth
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationMomentSeries
import ArithmeticHodge.Analysis.YoshidaSineMomentEnclosures
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

open Set
open scoped Nat

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeTrigEnclosures

noncomputable section

open RatInterval
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseConcretePerturbationMoments
open YoshidaFactorTwoPhasePerturbationMomentSeries
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures

/-!
# Exact enclosures for the retained `p = 3` phase

For the canonical modes `n = 0, ..., 200`, this file encloses

`sin (2 * factorTwoMomentY n * factorTwoPrimeShift)` and
`cos (2 * factorTwoMomentY n * factorTwoPrimeShift)`

in exact rational intervals of width at most `10^-10`.  The large phase is
reduced by a kernel-checked quarter-turn index, and sine and cosine on the
resulting interval `[-4/5, 4/5]` are enclosed by Taylor polynomials with a
rigorous remainder.
-/

/-! ## Fine logarithmic constants -/

/-- A `10^-14` rational enclosure of `log 2`. -/
def factorTwoPrimeLogTwoInterval : RatInterval :=
  ⟨69314718055994 / 100000000000000,
    69314718055995 / 100000000000000⟩

/-- A `10^-14` rational enclosure of the retained-prime shift `log (3/2)`. -/
def factorTwoPrimeShiftInterval : RatInterval :=
  ⟨40546510810816 / 100000000000000,
    40546510810817 / 100000000000000⟩

/-- The existing twenty-decimal rational enclosure of `pi`. -/
def factorTwoPrimePiInterval : RatInterval := piFineInterval

private theorem strict_log_two_prime_bounds :
    (69314718055994 / 100000000000000 : ℝ) < Real.log 2 ∧
      Real.log 2 < (69314718055995 / 100000000000000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 16
  have hup := Real.log_div_le_sum_range_add
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at hlo hup ⊢
  constructor <;> linarith

private theorem strict_log_three_halves_prime_bounds :
    (40546510810816 / 100000000000000 : ℝ) < Real.log (3 / 2) ∧
      Real.log (3 / 2) < (40546510810817 / 100000000000000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div
    (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 10
  have hup := Real.log_div_le_sum_range_add
    (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at hlo hup ⊢
  constructor <;> linarith

theorem factorTwoPrimeLogTwoInterval_contains :
    factorTwoPrimeLogTwoInterval.Contains factorTwoMomentLength := by
  rw [factorTwoMomentLength_eq_yoshidaLength]
  constructor
  · have h := strict_log_two_prime_bounds.1
    norm_num [factorTwoPrimeLogTwoInterval, Contains, yoshidaLength] at h ⊢
    exact h.le
  · have h := strict_log_two_prime_bounds.2
    norm_num [factorTwoPrimeLogTwoInterval, Contains, yoshidaLength] at h ⊢
    exact h.le

theorem factorTwoPrimeShiftInterval_contains :
    factorTwoPrimeShiftInterval.Contains factorTwoPrimeShift := by
  constructor
  · have h := strict_log_three_halves_prime_bounds.1
    norm_num [factorTwoPrimeShiftInterval, Contains, factorTwoPrimeShift] at h ⊢
    exact h.le
  · have h := strict_log_three_halves_prime_bounds.2
    norm_num [factorTwoPrimeShiftInterval, Contains, factorTwoPrimeShift] at h ⊢
    exact h.le

theorem factorTwoPrimePiInterval_contains :
    factorTwoPrimePiInterval.Contains Real.pi := by
  exact piFineInterval_contains

/-! ## Quarter-turn reduction -/

/-- Nearest-quarter-turn certificate computed from the rational surrogate
`2.33985` for `4 * log (3/2) / log 2`. -/
def factorTwoPrimeQuarterIndex (n : Fin 201) : ℕ :=
  (233985 * n.1 + 50000) / 100000

/-- Direct rational enclosure of the unreduced retained-prime phase. -/
def factorTwoPrimePhaseInterval (n : Fin 201) : RatInterval :=
  pure 2 * factorTwoPrimePiInterval * pure n.1 *
      factorTwoPrimeShiftInterval / factorTwoPrimeLogTwoInterval

/-- Rational enclosure after subtracting the certified number of quarter turns. -/
def factorTwoPrimeResidualInterval (n : Fin 201) : RatInterval :=
  factorTwoPrimePhaseInterval n -
    pure (factorTwoPrimeQuarterIndex n) * factorTwoPrimePiInterval / pure 2

/-- The exact real reduced phase corresponding to
`factorTwoPrimeResidualInterval`. -/
def factorTwoPrimeResidual (n : Fin 201) : ℝ :=
  2 * factorTwoMomentY n.1 * factorTwoPrimeShift -
    factorTwoPrimeQuarterIndex n * Real.pi / 2

theorem factorTwoPrimePhaseInterval_contains (n : Fin 201) :
    (factorTwoPrimePhaseInterval n).Contains
      (2 * factorTwoMomentY n.1 * factorTwoPrimeShift) := by
  have hnum :
      (pure 2 * factorTwoPrimePiInterval * pure n.1 *
          factorTwoPrimeShiftInterval).Contains
        (2 * Real.pi * (n.1 : ℝ) * factorTwoPrimeShift) :=
    contains_mul
      (contains_mul
        (contains_mul (contains_pure 2) factorTwoPrimePiInterval_contains)
        (contains_pure n.1))
      factorTwoPrimeShiftInterval_contains
  have hphase := contains_div_of_pos
    (I := pure 2 * factorTwoPrimePiInterval * pure n.1 *
      factorTwoPrimeShiftInterval)
    (J := factorTwoPrimeLogTwoInterval)
    (by norm_num [factorTwoPrimeLogTwoInterval]) hnum
    factorTwoPrimeLogTwoInterval_contains
  unfold factorTwoPrimePhaseInterval
  convert hphase using 1
  unfold factorTwoMomentY factorTwoNaturalFrequency
  rw [factorTwoMomentLength_eq_yoshidaLength]
  ring

theorem factorTwoPrimeResidualInterval_contains (n : Fin 201) :
    (factorTwoPrimeResidualInterval n).Contains
      (factorTwoPrimeResidual n) := by
  have hquarter :
      (pure (factorTwoPrimeQuarterIndex n) * factorTwoPrimePiInterval /
          pure 2).Contains
        (factorTwoPrimeQuarterIndex n * Real.pi / 2) :=
    contains_div_of_pos (by norm_num [RatInterval.pure])
      (contains_mul (contains_pure (factorTwoPrimeQuarterIndex n))
        factorTwoPrimePiInterval_contains)
      (contains_pure 2)
  exact contains_sub (factorTwoPrimePhaseInterval_contains n) hquarter

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem factorTwoPrimeResidualInterval_absBound :
    ∀ n : Fin 201,
      (factorTwoPrimeResidualInterval n).AbsBound (4 / 5) := by
  intro n
  unfold RatInterval.AbsBound
  fin_cases n <;> decide +kernel

theorem factorTwoPrimeResidual_abs_le (n : Fin 201) :
    |factorTwoPrimeResidual n| ≤ (4 / 5 : ℝ) := by
  have hmem := factorTwoPrimeResidualInterval_contains n
  have hbox := factorTwoPrimeResidualInterval_absBound n
  rw [abs_le]
  constructor
  · calc
      -(4 / 5 : ℝ) ≤ ((factorTwoPrimeResidualInterval n).lower : ℝ) := by
        simpa using (Rat.cast_le (K := ℝ)).2 hbox.1
      _ ≤ factorTwoPrimeResidual n := hmem.1
  · calc
      factorTwoPrimeResidual n ≤
          ((factorTwoPrimeResidualInterval n).upper : ℝ) := hmem.2
      _ ≤ (4 / 5 : ℝ) := by
        simpa using (Rat.cast_le (K := ℝ)).2 hbox.2

/-! ## Taylor enclosure on `[-4/5, 4/5]` -/

private def factorTwoPrimeSinTaylor (x : ℝ) : ℝ :=
  let z := x * x
  x * (1 + z * (-1 / 6 + z * (1 / 120 + z *
    (-1 / 5040 + z * (1 / 362880 + z *
      (-1 / 39916800 + z * (1 / 6227020800)))))))

private def factorTwoPrimeCosTaylor (x : ℝ) : ℝ :=
  let z := x * x
  1 + z * (-1 / 2 + z * (1 / 24 + z *
    (-1 / 720 + z * (1 / 40320 + z *
      (-1 / 3628800 + z * (1 / 479001600))))))

/-- Rational Taylor remainder used for both sine and cosine. -/
def factorTwoPrimeTaylorError : ℚ :=
  (4 / 5) ^ 14 / 6227020800

def factorTwoPrimeTaylorErrorInterval : RatInterval :=
  ⟨-factorTwoPrimeTaylorError, factorTwoPrimeTaylorError⟩

/-- Horner evaluation of the degree-13 sine Taylor polynomial. -/
def factorTwoPrimeSinTaylorInterval (I : RatInterval) : RatInterval :=
  let z := I * I
  I * (pure 1 + z * (pure (-1 / 6) + z * (pure (1 / 120) + z *
    (pure (-1 / 5040) + z * (pure (1 / 362880) + z *
      (pure (-1 / 39916800) + z * pure (1 / 6227020800)))))))

/-- Horner evaluation of the degree-12 cosine Taylor polynomial. -/
def factorTwoPrimeCosTaylorInterval (I : RatInterval) : RatInterval :=
  let z := I * I
  pure 1 + z * (pure (-1 / 2) + z * (pure (1 / 24) + z *
    (pure (-1 / 720) + z * (pure (1 / 40320) + z *
      (pure (-1 / 3628800) + z * pure (1 / 479001600))))))

private theorem factorTwoPrimeSinTaylor_error_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ (4 / 5 : ℝ)) :
    |Real.sin x - factorTwoPrimeSinTaylor x| ≤
      (4 / 5 : ℝ) ^ 14 / 13 ! := by
  have hpos : (0 : ℝ) < 4 / 5 := by norm_num
  have hzero : (0 : ℝ) ∈ Icc 0 (4 / 5) := by norm_num
  have ht :
      taylorWithinEval Real.sin 13 (Icc 0 (4 / 5)) 0 x =
        factorTwoPrimeSinTaylor x := by
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ,
      Real.iteratedDerivWithin_sin_Icc _ hpos hzero,
      factorTwoPrimeSinTaylor]
    ring
  have h := taylor_mean_remainder_bound
    (f := Real.sin) (a := 0) (b := (4 / 5 : ℝ))
    (C := 1) (x := x) (n := 13)
    (by norm_num) Real.contDiff_sin.contDiffOn ⟨hx0, hx1⟩ (by
      intro y hy
      rw [Real.iteratedDerivWithin_sin_Icc 14 hpos hy, Real.norm_eq_abs]
      exact Real.abs_iteratedDeriv_sin_le_one 14 y)
  rw [ht] at h
  norm_num only [one_mul, sub_zero] at h
  have hp : x ^ 14 ≤ (4 / 5 : ℝ) ^ 14 :=
    pow_le_pow_left₀ hx0 hx1 14
  norm_num [Nat.factorial] at h ⊢
  exact h.trans (by linarith)

private theorem factorTwoPrimeCosTaylor_error_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ (4 / 5 : ℝ)) :
    |Real.cos x - factorTwoPrimeCosTaylor x| ≤
      (4 / 5 : ℝ) ^ 14 / 13 ! := by
  have hpos : (0 : ℝ) < 4 / 5 := by norm_num
  have hzero : (0 : ℝ) ∈ Icc 0 (4 / 5) := by norm_num
  have ht :
      taylorWithinEval Real.cos 13 (Icc 0 (4 / 5)) 0 x =
        factorTwoPrimeCosTaylor x := by
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ,
      Real.iteratedDerivWithin_cos_Icc _ hpos hzero,
      factorTwoPrimeCosTaylor]
    ring
  have h := taylor_mean_remainder_bound
    (f := Real.cos) (a := 0) (b := (4 / 5 : ℝ))
    (C := 1) (x := x) (n := 13)
    (by norm_num) Real.contDiff_cos.contDiffOn ⟨hx0, hx1⟩ (by
      intro y hy
      rw [Real.iteratedDerivWithin_cos_Icc 14 hpos hy, Real.norm_eq_abs]
      exact Real.abs_iteratedDeriv_cos_le_one 14 y)
  rw [ht] at h
  norm_num only [one_mul, sub_zero] at h
  have hp : x ^ 14 ≤ (4 / 5 : ℝ) ^ 14 :=
    pow_le_pow_left₀ hx0 hx1 14
  norm_num [Nat.factorial] at h ⊢
  exact h.trans (by linarith)

private theorem factorTwoPrimeSinTaylor_error
    {x : ℝ} (hx : |x| ≤ (4 / 5 : ℝ)) :
    |Real.sin x - factorTwoPrimeSinTaylor x| ≤
      (4 / 5 : ℝ) ^ 14 / 13 ! := by
  by_cases h : 0 ≤ x
  · exact factorTwoPrimeSinTaylor_error_nonneg h
      (by simpa [abs_of_nonneg h] using hx)
  · have hn : x < 0 := lt_of_not_ge h
    have hu := factorTwoPrimeSinTaylor_error_nonneg
      (x := -x) (by linarith) (by simpa [abs_of_neg hn] using hx)
    have hi :
        Real.sin (-x) - factorTwoPrimeSinTaylor (-x) =
          -(Real.sin x - factorTwoPrimeSinTaylor x) := by
      rw [Real.sin_neg]
      simp only [factorTwoPrimeSinTaylor]
      ring
    rw [hi, abs_neg] at hu
    exact hu

private theorem factorTwoPrimeCosTaylor_error
    {x : ℝ} (hx : |x| ≤ (4 / 5 : ℝ)) :
    |Real.cos x - factorTwoPrimeCosTaylor x| ≤
      (4 / 5 : ℝ) ^ 14 / 13 ! := by
  by_cases h : 0 ≤ x
  · exact factorTwoPrimeCosTaylor_error_nonneg h
      (by simpa [abs_of_nonneg h] using hx)
  · have hn : x < 0 := lt_of_not_ge h
    have hu := factorTwoPrimeCosTaylor_error_nonneg
      (x := -x) (by linarith) (by simpa [abs_of_neg hn] using hx)
    have hi :
        Real.cos (-x) - factorTwoPrimeCosTaylor (-x) =
          Real.cos x - factorTwoPrimeCosTaylor x := by
      rw [Real.cos_neg]
      simp only [factorTwoPrimeCosTaylor]
      ring
    rw [hi] at hu
    exact hu

private theorem factorTwoPrimeSinTaylorInterval_contains
    {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (factorTwoPrimeSinTaylorInterval I).Contains
      (factorTwoPrimeSinTaylor x) := by
  have hz := contains_mul hx hx
  have h6 := contains_add (contains_pure (-1 / 39916800))
    (contains_mul hz (contains_pure (1 / 6227020800)))
  have h5 := contains_add (contains_pure (1 / 362880)) (contains_mul hz h6)
  have h4 := contains_add (contains_pure (-1 / 5040)) (contains_mul hz h5)
  have h3 := contains_add (contains_pure (1 / 120)) (contains_mul hz h4)
  have h2 := contains_add (contains_pure (-1 / 6)) (contains_mul hz h3)
  have h1 := contains_add (contains_pure 1) (contains_mul hz h2)
  simpa [factorTwoPrimeSinTaylorInterval, factorTwoPrimeSinTaylor] using
    contains_mul hx h1

private theorem factorTwoPrimeCosTaylorInterval_contains
    {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (factorTwoPrimeCosTaylorInterval I).Contains
      (factorTwoPrimeCosTaylor x) := by
  have hz := contains_mul hx hx
  have h6 := contains_add (contains_pure (-1 / 3628800))
    (contains_mul hz (contains_pure (1 / 479001600)))
  have h5 := contains_add (contains_pure (1 / 40320)) (contains_mul hz h6)
  have h4 := contains_add (contains_pure (-1 / 720)) (contains_mul hz h5)
  have h3 := contains_add (contains_pure (1 / 24)) (contains_mul hz h4)
  have h2 := contains_add (contains_pure (-1 / 2)) (contains_mul hz h3)
  have h1 := contains_add (contains_pure 1) (contains_mul hz h2)
  simpa [factorTwoPrimeCosTaylorInterval, factorTwoPrimeCosTaylor] using h1

private theorem factorTwoPrimeTaylorErrorInterval_contains
    {x : ℝ}
    (hx : |x| ≤ (4 / 5 : ℝ) ^ 14 / 13 !) :
    factorTwoPrimeTaylorErrorInterval.Contains x := by
  have hx' : |x| ≤ ((factorTwoPrimeTaylorError : ℚ) : ℝ) := by
    simpa [factorTwoPrimeTaylorError, Nat.factorial] using hx
  simpa [factorTwoPrimeTaylorErrorInterval, Contains] using (abs_le.mp hx')

/-- Sine enclosure before restoring the removed quarter turns. -/
def factorTwoPrimeReducedSinInterval (n : Fin 201) : RatInterval :=
  factorTwoPrimeSinTaylorInterval (factorTwoPrimeResidualInterval n) +
    factorTwoPrimeTaylorErrorInterval

/-- Cosine enclosure before restoring the removed quarter turns. -/
def factorTwoPrimeReducedCosInterval (n : Fin 201) : RatInterval :=
  factorTwoPrimeCosTaylorInterval (factorTwoPrimeResidualInterval n) +
    factorTwoPrimeTaylorErrorInterval

theorem factorTwoPrimeReducedSinInterval_contains (n : Fin 201) :
    (factorTwoPrimeReducedSinInterval n).Contains
      (Real.sin (factorTwoPrimeResidual n)) := by
  have hp := factorTwoPrimeSinTaylorInterval_contains
    (factorTwoPrimeResidualInterval_contains n)
  have he := factorTwoPrimeTaylorErrorInterval_contains
    (factorTwoPrimeSinTaylor_error (factorTwoPrimeResidual_abs_le n))
  have h := contains_add hp he
  unfold factorTwoPrimeReducedSinInterval
  convert h using 1
  ring

theorem factorTwoPrimeReducedCosInterval_contains (n : Fin 201) :
    (factorTwoPrimeReducedCosInterval n).Contains
      (Real.cos (factorTwoPrimeResidual n)) := by
  have hp := factorTwoPrimeCosTaylorInterval_contains
    (factorTwoPrimeResidualInterval_contains n)
  have he := factorTwoPrimeTaylorErrorInterval_contains
    (factorTwoPrimeCosTaylor_error (factorTwoPrimeResidual_abs_le n))
  have h := contains_add hp he
  unfold factorTwoPrimeReducedCosInterval
  convert h using 1
  ring

/-! ## Restore the quarter turns -/

private def quarterSin (q : ℕ) (s c : ℝ) : ℝ :=
  match q % 4 with
  | 0 => s
  | 1 => c
  | 2 => -s
  | _ => -c

private def quarterCos (q : ℕ) (s c : ℝ) : ℝ :=
  match q % 4 with
  | 0 => c
  | 1 => -s
  | 2 => -c
  | _ => s

private def quarterSinInterval
    (q : ℕ) (S C : RatInterval) : RatInterval :=
  match q % 4 with
  | 0 => S
  | 1 => C
  | 2 => -S
  | _ => -C

private def quarterCosInterval
    (q : ℕ) (S C : RatInterval) : RatInterval :=
  match q % 4 with
  | 0 => C
  | 1 => -S
  | 2 => -C
  | _ => S

private theorem sin_add_nat_mul_pi_div_two (x : ℝ) (q : ℕ) :
    Real.sin (x + (q : ℝ) * Real.pi / 2) =
      quarterSin q (Real.sin x) (Real.cos x) := by
  have hd : q % 4 + 4 * (q / 4) = q := Nat.mod_add_div q 4
  have hdr : (q : ℝ) = (q % 4 : ℕ) + 4 * (q / 4 : ℕ) := by
    exact_mod_cast hd.symm
  have harg :
      x + (q : ℝ) * Real.pi / 2 =
        (x + (q % 4 : ℕ) * Real.pi / 2) +
          (q / 4 : ℕ) * (2 * Real.pi) := by
    rw [hdr]
    ring
  rw [harg, Real.sin_add_nat_mul_two_pi]
  have hlt : q % 4 < 4 := Nat.mod_lt q (by norm_num)
  interval_cases h : q % 4
  · simp [quarterSin, h]
  · simp [quarterSin, h, Real.sin_add_pi_div_two]
  · rw [show x + (2 : ℕ) * Real.pi / 2 = x + Real.pi by
      norm_num]
    simp [quarterSin, h]
  · rw [show x + (3 : ℕ) * Real.pi / 2 =
        (x + Real.pi) + Real.pi / 2 by
      ring_nf]
    simp [quarterSin, h, Real.sin_add_pi_div_two]

private theorem cos_add_nat_mul_pi_div_two (x : ℝ) (q : ℕ) :
    Real.cos (x + (q : ℝ) * Real.pi / 2) =
      quarterCos q (Real.sin x) (Real.cos x) := by
  have hd : q % 4 + 4 * (q / 4) = q := Nat.mod_add_div q 4
  have hdr : (q : ℝ) = (q % 4 : ℕ) + 4 * (q / 4 : ℕ) := by
    exact_mod_cast hd.symm
  have harg :
      x + (q : ℝ) * Real.pi / 2 =
        (x + (q % 4 : ℕ) * Real.pi / 2) +
          (q / 4 : ℕ) * (2 * Real.pi) := by
    rw [hdr]
    ring
  rw [harg, Real.cos_add_nat_mul_two_pi]
  have hlt : q % 4 < 4 := Nat.mod_lt q (by norm_num)
  interval_cases h : q % 4
  · simp [quarterCos, h]
  · simp [quarterCos, h, Real.cos_add_pi_div_two]
  · rw [show x + (2 : ℕ) * Real.pi / 2 = x + Real.pi by
      norm_num]
    simp [quarterCos, h]
  · rw [show x + (3 : ℕ) * Real.pi / 2 =
        (x + Real.pi) + Real.pi / 2 by
      ring_nf]
    simp [quarterCos, h, Real.cos_add_pi_div_two]

private theorem quarterSinInterval_contains
    {q : ℕ} {S C : RatInterval} {s c : ℝ}
    (hs : S.Contains s) (hc : C.Contains c) :
    (quarterSinInterval q S C).Contains (quarterSin q s c) := by
  have hlt : q % 4 < 4 := Nat.mod_lt q (by norm_num)
  interval_cases h : q % 4
  · simpa [quarterSinInterval, quarterSin, h] using hs
  · simpa [quarterSinInterval, quarterSin, h] using hc
  · simpa [quarterSinInterval, quarterSin, h] using contains_neg hs
  · simpa [quarterSinInterval, quarterSin, h] using contains_neg hc

private theorem quarterCosInterval_contains
    {q : ℕ} {S C : RatInterval} {s c : ℝ}
    (hs : S.Contains s) (hc : C.Contains c) :
    (quarterCosInterval q S C).Contains (quarterCos q s c) := by
  have hlt : q % 4 < 4 := Nat.mod_lt q (by norm_num)
  interval_cases h : q % 4
  · simpa [quarterCosInterval, quarterCos, h] using hc
  · simpa [quarterCosInterval, quarterCos, h] using contains_neg hs
  · simpa [quarterCosInterval, quarterCos, h] using contains_neg hc
  · simpa [quarterCosInterval, quarterCos, h] using hs

/-- Public exact rational enclosure of the retained-prime sine phase. -/
def factorTwoPrimeSinInterval (n : Fin 201) : RatInterval :=
  quarterSinInterval (factorTwoPrimeQuarterIndex n)
    (factorTwoPrimeReducedSinInterval n)
    (factorTwoPrimeReducedCosInterval n)

/-- Public exact rational enclosure of the retained-prime cosine phase. -/
def factorTwoPrimeCosInterval (n : Fin 201) : RatInterval :=
  quarterCosInterval (factorTwoPrimeQuarterIndex n)
    (factorTwoPrimeReducedSinInterval n)
    (factorTwoPrimeReducedCosInterval n)

theorem factorTwoPrimeSinInterval_contains (n : Fin 201) :
    (factorTwoPrimeSinInterval n).Contains
      (Real.sin (2 * factorTwoMomentY n.1 * factorTwoPrimeShift)) := by
  have h := quarterSinInterval_contains
    (q := factorTwoPrimeQuarterIndex n)
    (factorTwoPrimeReducedSinInterval_contains n)
    (factorTwoPrimeReducedCosInterval_contains n)
  rw [← sin_add_nat_mul_pi_div_two] at h
  unfold factorTwoPrimeSinInterval
  convert h using 1
  unfold factorTwoPrimeResidual
  ring

theorem factorTwoPrimeCosInterval_contains (n : Fin 201) :
    (factorTwoPrimeCosInterval n).Contains
      (Real.cos (2 * factorTwoMomentY n.1 * factorTwoPrimeShift)) := by
  have h := quarterCosInterval_contains
    (q := factorTwoPrimeQuarterIndex n)
    (factorTwoPrimeReducedSinInterval_contains n)
    (factorTwoPrimeReducedCosInterval_contains n)
  rw [← cos_add_nat_mul_pi_div_two] at h
  unfold factorTwoPrimeCosInterval
  convert h using 1
  unfold factorTwoPrimeResidual
  ring

/-! ## Exact width certificates -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem factorTwoPrimeTrigIntervals_width_le :
    ∀ n : Fin 201,
      width (factorTwoPrimeSinInterval n) ≤ (1 / 10000000000 : ℚ) ∧
      width (factorTwoPrimeCosInterval n) ≤ (1 / 10000000000 : ℚ) := by
  intro n
  fin_cases n <;> decide +kernel

theorem factorTwoPrimeSinInterval_width_le (n : Fin 201) :
    width (factorTwoPrimeSinInterval n) ≤ (1 / 10000000000 : ℚ) :=
  (factorTwoPrimeTrigIntervals_width_le n).1

theorem factorTwoPrimeCosInterval_width_le (n : Fin 201) :
    width (factorTwoPrimeCosInterval n) ≤ (1 / 10000000000 : ℚ) :=
  (factorTwoPrimeTrigIntervals_width_le n).2

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeTrigEnclosures
