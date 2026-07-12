import ArithmeticHodge.Analysis.YoshidaConstantBounds
import ArithmeticHodge.Analysis.YoshidaOddGramPrefix
import Mathlib.Analysis.PSeries

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaDiagonalSeriesTail

open YoshidaConstantBounds
open YoshidaOddGramPrefix

/-!
# Certified tails for the accelerated Yoshida diagonal series

The paired diagonal summand contains a universal `k⁻²` term.  Removing

`(1 / (2L) + 1 / 4) / k²`

leaves an `O(k⁻³)` correction.  This module proves that statement using only
rational inequalities, restores the two dyadic endpoint exponentials, and
gives a uniform absolute tail bound for Yoshida's first ten modes.

The exact analytic assembly of these summands into `yoshidaDiagonalMoment`
belongs to `YoshidaDiagonalMomentSeries`; this file is its algebraic and
summability certificate layer.
-/

/-- Closed value of
`∫₀ᴸ exp (-a u) (1 - u / L) cos (κu) du` at a complete period, with
`p = κ²` and `q = exp (-aL)`. -/
def diagonalRampClosed (L p a q : ℝ) : ℝ :=
  ((q - 1 + a * L) * (a ^ 2 - p) + 2 * a * p * L) /
    (L * (a ^ 2 + p) ^ 2)

/-- The paired summand after setting its endpoint exponentials to zero and
removing its universal `k⁻²` asymptote. -/
def diagonalPairedCore (L p k : ℝ) : ℝ :=
  2 * diagonalRampClosed L p (2 * k + 1 / 2) 0 - 1 / k +
    (1 / (2 * L) + 1 / 4) / k ^ 2

/-- Expanded numerator of `diagonalPairedCore`. -/
def diagonalCoreNumerator (L p k : ℝ) : ℝ :=
  256 * k ^ 3 * L * p - 64 * k ^ 3 * L - 256 * k ^ 3 +
    64 * k ^ 2 * L * p - 48 * k ^ 2 * L - 384 * k ^ 2 * p - 160 * k ^ 2 +
    64 * k * L * p ^ 2 - 32 * k * L * p - 12 * k * L - 128 * k * p - 32 * k -
    16 * L * p ^ 2 - 8 * L * p - L - 32 * p ^ 2 - 16 * p - 2

/-- A denominator-aligned numerator used to prove the expanded core identity
without asking normalization tactics to discover a large square factor. -/
def diagonalRawNumerator (L p k a : ℝ) : ℝ :=
  4 * a ^ 4 * k * L - a ^ 4 * L - 2 * a ^ 4 - 8 * a ^ 3 * k ^ 2 * L +
    8 * a ^ 2 * k ^ 2 + 8 * a ^ 2 * k * L * p - 2 * a ^ 2 * L * p -
    4 * a ^ 2 * p - 8 * a * k ^ 2 * L * p - 8 * k ^ 2 * p +
    4 * k * L * p ^ 2 - L * p ^ 2 - 2 * p ^ 2

theorem diagonalPairedRaw_eq
    {L p k a : ℝ} (hL : L ≠ 0) (hk : k ≠ 0) (hden : a ^ 2 + p ≠ 0) :
    2 * diagonalRampClosed L p a 0 - 1 / k +
        (1 / (2 * L) + 1 / 4) / k ^ 2 =
      -diagonalRawNumerator L p k a /
        (4 * k ^ 2 * L * (a ^ 2 + p) ^ 2) := by
  have hR : 4 * k ^ 2 * L * (a ^ 2 + p) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hk)) hL)
      (pow_ne_zero _ hden)
  apply (eq_div_iff hR).2
  unfold diagonalRampClosed diagonalRawNumerator
  field_simp [hL, hk, hden]
  ring

theorem diagonalRawNumerator_specialize (L p k : ℝ) :
    16 * diagonalRawNumerator L p k (2 * k + 1 / 2) =
      diagonalCoreNumerator L p k := by
  unfold diagonalRawNumerator diagonalCoreNumerator
  ring

/-- Exact rational identity for the accelerated core. -/
theorem diagonalPairedCore_eq
    {L p k : ℝ} (hL : L ≠ 0) (hk : k ≠ 0)
    (hden : (2 * k + 1 / 2) ^ 2 + p ≠ 0) :
    diagonalPairedCore L p k =
      -diagonalCoreNumerator L p k /
        (64 * k ^ 2 * L * ((2 * k + 1 / 2) ^ 2 + p) ^ 2) := by
  unfold diagonalPairedCore
  rw [diagonalPairedRaw_eq hL hk hden]
  rw [← diagonalRawNumerator_specialize L p k]
  field_simp [hL, hk, hden]
  ring

/-- Sum of the absolute monomials in `diagonalCoreNumerator`. -/
def diagonalCoreMagnitude (L p k : ℝ) : ℝ :=
  256 * k ^ 3 * L * p + 64 * k ^ 3 * L + 256 * k ^ 3 +
    64 * k ^ 2 * L * p + 48 * k ^ 2 * L + 384 * k ^ 2 * p + 160 * k ^ 2 +
    64 * k * L * p ^ 2 + 32 * k * L * p + 12 * k * L + 128 * k * p + 32 * k +
    16 * L * p ^ 2 + 8 * L * p + L + 32 * p ^ 2 + 16 * p + 2

theorem diagonalCoreNumerator_abs_le_magnitude
    {L p k : ℝ} (hL : 0 ≤ L) (hp : 0 ≤ p) (hk : 0 ≤ k) :
    |diagonalCoreNumerator L p k| ≤ diagonalCoreMagnitude L p k := by
  rw [abs_le]
  constructor
  · have h : 0 ≤ diagonalCoreMagnitude L p k + diagonalCoreNumerator L p k := by
      unfold diagonalCoreMagnitude diagonalCoreNumerator
      ring_nf
      positivity
    linarith
  · have h : 0 ≤ diagonalCoreMagnitude L p k - diagonalCoreNumerator L p k := by
      unfold diagonalCoreMagnitude diagonalCoreNumerator
      ring_nf
      positivity
    linarith

theorem diagonalCoreMagnitude_le
    {L p k : ℝ} (hLhi : L ≤ 7 / 10)
    (hp : 0 ≤ p) (hk : 1 ≤ k) (hpk : p ≤ k ^ 2) :
    diagonalCoreMagnitude L p k ≤ (900 * p + 600) * k ^ 3 := by
  have hk0 : 0 ≤ k := by linarith
  have hk2 : 0 ≤ k ^ 2 := sq_nonneg k
  have hk3 : 0 ≤ k ^ 3 := by positivity
  have hk_le_k2 : k ≤ k ^ 2 := by
    nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hk)]
  have hk2_le_k3 : k ^ 2 ≤ k ^ 3 := by
    nlinarith [mul_nonneg hk2 (sub_nonneg.mpr hk)]
  have hone_le_k3 : 1 ≤ k ^ 3 := by linarith
  have hpk1 : p * k ≤ p * k ^ 3 :=
    mul_le_mul_of_nonneg_left (hk_le_k2.trans hk2_le_k3) hp
  have hpk2 : p * k ^ 2 ≤ p * k ^ 3 :=
    mul_le_mul_of_nonneg_left hk2_le_k3 hp
  have hp1 : p ≤ p * k ^ 3 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone_le_k3 hp
  have hp2k : p ^ 2 * k ≤ p * k ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right hpk (show 0 ≤ p * k by positivity)
    nlinarith
  have hp2 : p ^ 2 ≤ p * k ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left hpk hp
    simpa only [pow_two] using hm.trans hpk2
  have hLk3p : k ^ 3 * L * p ≤ (7 / 10 : ℝ) * (p * k ^ 3) := by
    have hm := mul_le_mul_of_nonneg_right hLhi (show 0 ≤ p * k ^ 3 by positivity)
    nlinarith
  have hLk3 : k ^ 3 * L ≤ (7 / 10 : ℝ) * k ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right hLhi hk3
    nlinarith
  have hLk2p : k ^ 2 * L * p ≤ (7 / 10 : ℝ) * (p * k ^ 3) := by
    have hm := mul_le_mul_of_nonneg_right hLhi (show 0 ≤ p * k ^ 2 by positivity)
    nlinarith
  have hLk2 : k ^ 2 * L ≤ (7 / 10 : ℝ) * k ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right hLhi hk2
    nlinarith
  have hLkp2 : k * L * p ^ 2 ≤ (7 / 10 : ℝ) * (p * k ^ 3) := by
    have hm := mul_le_mul_of_nonneg_right hLhi (show 0 ≤ p ^ 2 * k by positivity)
    nlinarith
  have hLkp : k * L * p ≤ (7 / 10 : ℝ) * (p * k ^ 3) := by
    have hm := mul_le_mul_of_nonneg_right hLhi (show 0 ≤ p * k by positivity)
    nlinarith
  have hLk : k * L ≤ (7 / 10 : ℝ) * k ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right hLhi hk0
    nlinarith
  have hLp2 : L * p ^ 2 ≤ (7 / 10 : ℝ) * (p * k ^ 3) := by
    have hm := mul_le_mul_of_nonneg_right hLhi (sq_nonneg p)
    nlinarith
  have hLp : L * p ≤ (7 / 10 : ℝ) * (p * k ^ 3) := by
    have hm := mul_le_mul_of_nonneg_right hLhi hp
    nlinarith
  have hLone : L ≤ (7 / 10 : ℝ) * k ^ 3 := by
    nlinarith
  unfold diagonalCoreMagnitude
  nlinarith

/-- Generic `O(k⁻³)` bound.  The condition `p ≤ k²` is the natural point
after which the mode frequency is below the series index. -/
theorem diagonalPairedCore_abs_le
    {L p k : ℝ}
    (hLlo : (69 / 100 : ℝ) ≤ L) (hLhi : L ≤ 7 / 10)
    (hp : 0 ≤ p) (hk : 1 ≤ k) (hpk : p ≤ k ^ 2) :
    |diagonalPairedCore L p k| ≤ (2 * p + 1) / k ^ 3 := by
  have hk0 : 0 < k := by linarith
  have hL0 : 0 < L := by linarith
  have hrate : 0 < (2 * k + 1 / 2) ^ 2 + p := by positivity
  rw [diagonalPairedCore_eq hL0.ne' hk0.ne' hrate.ne']
  rw [show 64 * k ^ 2 * L * ((2 * k + 1 / 2) ^ 2 + p) ^ 2 =
      4 * k ^ 2 * L * (16 * k ^ 2 + 8 * k + 4 * p + 1) ^ 2 by ring]
  have hmag := diagonalCoreNumerator_abs_le_magnitude hL0.le hp hk0.le
  have hmag' := diagonalCoreMagnitude_le hLhi hp hk hpk
  let B := diagonalCoreNumerator L p k
  let Q := 16 * k ^ 2 + 8 * k + 4 * p + 1
  let D := 4 * k ^ 2 * L * Q ^ 2
  have hQ : 16 * k ^ 2 ≤ Q := by dsimp [Q]; nlinarith [sq_nonneg k]
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  have hD : 0 < D := by dsimp [D]; positivity
  have hk3 : 0 < k ^ 3 := by positivity
  have hQsq : (16 * k ^ 2) ^ 2 ≤ Q ^ 2 :=
    pow_le_pow_left₀ (by positivity) hQ 2
  have hDlo : 700 * k ^ 6 ≤ D := by
    have h1 := mul_le_mul_of_nonneg_left hQsq
      (show 0 ≤ 4 * (69 / 100 : ℝ) * k ^ 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_right hLlo
      (show 0 ≤ 4 * k ^ 2 * Q ^ 2 by positivity)
    dsimp [D, Q] at h1 h2 ⊢
    nlinarith
  have hB : |B| ≤ (900 * p + 600) * k ^ 3 := by
    dsimp [B]
    exact hmag.trans hmag'
  have hcoef : 900 * p + 600 ≤ 700 * (2 * p + 1) := by linarith
  have hnum : |B| * k ^ 3 ≤ (2 * p + 1) * D := by
    have h1 := mul_le_mul_of_nonneg_right hB (show 0 ≤ k ^ 3 by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ k ^ 6 by positivity)
    have h3 := mul_le_mul_of_nonneg_left hDlo (show 0 ≤ 2 * p + 1 by positivity)
    nlinarith
  have hfrac : |B| / D ≤ (2 * p + 1) / k ^ 3 := by
    rw [div_le_div_iff₀ hD hk3]
    exact hnum
  change |-B / D| ≤ (2 * p + 1) / k ^ 3
  rw [abs_div, abs_neg, abs_of_pos hD]
  exact hfrac

/-- Endpoint-exponential contribution omitted by `diagonalPairedCore`. -/
def diagonalExponentialError (L p k q r : ℝ) : ℝ :=
  2 * q * ((2 * k + 1 / 2) ^ 2 - p) /
      (L * (((2 * k + 1 / 2) ^ 2 + p) ^ 2)) + r / k

/-- Fully restored accelerated paired summand.  For Yoshida's series,
`q = exp (-(2k+1/2)L)` and `r = exp (-2kL)`. -/
def diagonalPairedCorrection (L p k q r : ℝ) : ℝ :=
  2 * diagonalRampClosed L p (2 * k + 1 / 2) q - (1 - r) / k +
    (1 / (2 * L) + 1 / 4) / k ^ 2

theorem diagonalPairedCorrection_eq (L p k q r : ℝ) :
    diagonalPairedCorrection L p k q r =
      diagonalPairedCore L p k + diagonalExponentialError L p k q r := by
  unfold diagonalPairedCorrection diagonalPairedCore diagonalExponentialError
    diagonalRampClosed
  ring

/-- The dyadic endpoint error costs at most one additional `k⁻³`. -/
theorem diagonalExponentialError_bounds
    {L p k q r : ℝ}
    (hL : (69 / 100 : ℝ) ≤ L)
    (hp0 : 0 ≤ p) (hpk : p ≤ k ^ 2)
    (hk : 16 ≤ k)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / (4 * k ^ 2))
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / (4 * k ^ 2)) :
    0 ≤ diagonalExponentialError L p k q r ∧
      diagonalExponentialError L p k q r ≤ 1 / k ^ 3 := by
  let a : ℝ := 2 * k + 1 / 2
  let d : ℝ := a ^ 2 + p
  let num : ℝ := a ^ 2 - p
  have hk0 : 0 < k := by linarith
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < a := by dsimp [a]; linarith
  have ha2 : 4 * k ^ 2 ≤ a ^ 2 := by
    dsimp [a]
    nlinarith [sq_nonneg k]
  have hnum0 : 0 ≤ num := by
    dsimp [num]
    nlinarith
  have hnumd : num ≤ d := by dsimp [num, d]; linarith
  have hdlo : 4 * k ^ 2 ≤ d := by dsimp [d]; linarith
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hdlo
  have hqscaled : 4 * q * k ^ 2 ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hq (show 0 ≤ 4 * k ^ 2 by positivity)
    field_simp [hk0.ne'] at hm
    nlinarith
  have hfirstNumerator : 128 * q * num * k ^ 3 ≤ 32 * k * num := by
    have hm := mul_le_mul_of_nonneg_right hqscaled
      (show 0 ≤ 32 * k * num by positivity)
    nlinarith
  have hnumToD : 32 * k * num ≤ 32 * k * d :=
    mul_le_mul_of_nonneg_left hnumd (by positivity)
  have hLd : 32 * k ≤ L * d := by
    have h1 := mul_le_mul_of_nonneg_left hdlo hL0.le
    have h2 := mul_le_mul_of_nonneg_right hL (show 0 ≤ 4 * k ^ 2 by positivity)
    nlinarith
  have hdenStep : 32 * k * d ≤ L * d ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hLd hd0.le
    nlinarith
  have hfirst :
      2 * q * num / (L * d ^ 2) ≤ 1 / (64 * k ^ 3) := by
    rw [div_le_div_iff₀ (by positivity : 0 < L * d ^ 2)
      (by positivity : 0 < 64 * k ^ 3)]
    nlinarith [hfirstNumerator.trans (hnumToD.trans hdenStep)]
  have hrterm : r / k ≤ 1 / (4 * k ^ 3) := by
    rw [div_le_div_iff₀ hk0 (by positivity : 0 < 4 * k ^ 3)]
    have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 4 * k ^ 2 by positivity)
    field_simp [hk0.ne'] at hm
    nlinarith
  have herr0 : 0 ≤ 2 * q * num / (L * d ^ 2) + r / k := by positivity
  have herr : 2 * q * num / (L * d ^ 2) + r / k ≤ 1 / k ^ 3 := by
    have hk3 : 0 < k ^ 3 := by positivity
    calc
      2 * q * num / (L * d ^ 2) + r / k ≤
          1 / (64 * k ^ 3) + 1 / (4 * k ^ 3) := add_le_add hfirst hrterm
      _ ≤ 1 / k ^ 3 := by
        field_simp [hk3.ne']
        norm_num
  simpa only [diagonalExponentialError, a, d, num] using And.intro herr0 herr

/-- Generic `O(k⁻³)` bound for the actual endpoint-restored summand. -/
theorem diagonalPairedCorrection_abs_le
    {L p k q r : ℝ}
    (hLlo : (69 / 100 : ℝ) ≤ L) (hLhi : L ≤ 7 / 10)
    (hp : 0 ≤ p) (hk : 16 ≤ k) (hpk : p ≤ k ^ 2)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / (4 * k ^ 2))
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / (4 * k ^ 2)) :
    |diagonalPairedCorrection L p k q r| ≤ (2 * p + 2) / k ^ 3 := by
  have hcore := diagonalPairedCore_abs_le hLlo hLhi hp (by linarith) hpk
  have herr := diagonalExponentialError_bounds hLlo hp hpk hk hq0 hq hr0 hr
  rw [diagonalPairedCorrection_eq]
  calc
    |diagonalPairedCore L p k + diagonalExponentialError L p k q r| ≤
        |diagonalPairedCore L p k| + |diagonalExponentialError L p k q r| :=
      abs_add_le _ _
    _ = |diagonalPairedCore L p k| + diagonalExponentialError L p k q r := by
      rw [abs_of_nonneg herr.1]
    _ ≤ (2 * p + 1) / k ^ 3 + 1 / k ^ 3 := add_le_add hcore herr.2
    _ = (2 * p + 2) / k ^ 3 := by ring

/-- Elementary domination of the dyadic endpoint factors by a rational
inverse square. -/
theorem four_mul_natCast_sq_le_four_pow
    {k : ℕ} (hk : 2 ≤ k) :
    (4 : ℝ) * (k : ℝ) ^ 2 ≤ (4 : ℝ) ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ]
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      have hsquare : ((k : ℝ) + 1) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((k : ℝ) - 1)]
      calc
        (4 : ℝ) * ((k : ℝ) + 1) ^ 2 ≤ 4 * (4 * (k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsquare (by norm_num)
        _ ≤ 4 * (4 : ℝ) ^ k := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (4 : ℝ) ^ k * 4 := by ring

theorem dyadic_endpoint_factors_le
    {k : ℕ} (hk : 2 ≤ k) :
    (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k ≤ 1 / (4 * (k : ℝ) ^ 2) ∧
      1 / (4 : ℝ) ^ k ≤ 1 / (4 * (k : ℝ) ^ 2) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpow := four_mul_natCast_sq_le_four_pow hk
  have hinv : 1 / (4 : ℝ) ^ k ≤ 1 / (4 * (k : ℝ) ^ 2) :=
    one_div_le_one_div_of_le (by positivity) hpow
  have hsqrt : (Real.sqrt 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact Real.one_le_sqrt.mpr (by norm_num)
  constructor
  · calc
      (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k ≤ 1 / (4 : ℝ) ^ k := by
        exact div_le_div_of_nonneg_right hsqrt (by positivity)
      _ ≤ 1 / (4 * (k : ℝ) ^ 2) := hinv
  · exact hinv

/-- Yoshida's actual dyadic accelerated correction at index `k ≥ 1`. -/
def diagonalDyadicPairedCorrection (L p : ℝ) (k : ℕ) : ℝ :=
  diagonalPairedCorrection L p k
    ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) (1 / (4 : ℝ) ^ k)

theorem diagonalDyadicPairedCorrection_abs_le
    {L p : ℝ} {k : ℕ}
    (hLlo : (69 / 100 : ℝ) ≤ L) (hLhi : L ≤ 7 / 10)
    (hp : 0 ≤ p) (hk : 16 ≤ k) (hpk : p ≤ (k : ℝ) ^ 2) :
    |diagonalDyadicPairedCorrection L p k| ≤
      (2 * p + 2) / (k : ℝ) ^ 3 := by
  have hfac := dyadic_endpoint_factors_le (by omega : 2 ≤ k)
  apply diagonalPairedCorrection_abs_le hLlo hLhi hp
    (by exact_mod_cast hk) hpk
  · positivity
  · exact hfac.1
  · positivity
  · exact hfac.2

private theorem hasSum_inv_sq_telescope (N : ℕ) (hN : 1 ≤ N) :
    HasSum (fun j : ℕ ↦
      (1 : ℝ) / ((N + j : ℕ) : ℝ) ^ 2 -
        1 / ((N + j + 1 : ℕ) : ℝ) ^ 2)
      (1 / (N : ℝ) ^ 2) := by
  have hnonneg : ∀ j : ℕ,
      0 ≤ (1 : ℝ) / ((N + j : ℕ) : ℝ) ^ 2 -
        1 / ((N + j + 1 : ℕ) : ℝ) ^ 2 := by
    intro j
    simp only [Nat.cast_add, Nat.cast_one]
    let m : ℝ := (N : ℝ) + (j : ℝ)
    have hm : 0 < m := by dsimp [m]; exact_mod_cast (by omega : 0 < N + j)
    change 0 ≤ 1 / m ^ 2 - 1 / (m + 1) ^ 2
    rw [sub_nonneg, div_le_div_iff₀ (by positivity : 0 < (m + 1) ^ 2)
      (by positivity : 0 < m ^ 2)]
    have hmle : m ≤ m + 1 := by linarith
    simpa only [one_mul] using pow_le_pow_left₀ hm.le hmle 2
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2
  have hnat : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hcast : Filter.Tendsto (fun n : ℕ ↦ (N : ℝ) + (n : ℝ))
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left Filter.atTop (N : ℝ) hnat
  have hinv : Filter.Tendsto (fun n : ℕ ↦ ((N : ℝ) + (n : ℝ))⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp hcast
  have htail : Filter.Tendsto
      (fun n : ℕ ↦ (1 : ℝ) / ((N + n : ℕ) : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
    convert hinv.pow 2 using 1
    · funext n
      simp only [Nat.cast_add, one_div, inv_pow]
    · norm_num
  have hconst : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ) / (N : ℝ) ^ 2)
      Filter.atTop (nhds (1 / (N : ℝ) ^ 2)) := tendsto_const_nhds
  have hlim : Filter.Tendsto
      (fun n : ℕ ↦ (1 : ℝ) / (N : ℝ) ^ 2 -
        1 / ((N + n : ℕ) : ℝ) ^ 2)
      Filter.atTop (nhds (1 / (N : ℝ) ^ 2)) := by
    simpa only [sub_zero] using hconst.sub htail
  have hpartial : (fun n : ℕ ↦ ∑ i ∈ Finset.range n,
      ((1 : ℝ) / ((N + i : ℕ) : ℝ) ^ 2 -
        1 / ((N + i + 1 : ℕ) : ℝ) ^ 2)) =
      fun n : ℕ ↦ 1 / (N : ℝ) ^ 2 - 1 / ((N + n : ℕ) : ℝ) ^ 2 := by
    funext n
    rw [show (fun i : ℕ ↦ (1 : ℝ) / ((N + i : ℕ) : ℝ) ^ 2 -
          1 / ((N + i + 1 : ℕ) : ℝ) ^ 2) =
        fun i : ℕ ↦ (1 : ℝ) / ((N + i : ℕ) : ℝ) ^ 2 -
          1 / ((N + (i + 1) : ℕ) : ℝ) ^ 2 by
      funext i
      rw [Nat.add_assoc]]
    exact Finset.sum_range_sub' (fun i : ℕ ↦
      (1 : ℝ) / ((N + i : ℕ) : ℝ) ^ 2) n
  rw [hpartial]
  exact hlim

/-- Rational integral-test substitute used by the final correction tail. -/
theorem one_div_cube_tail_bound (N : ℕ) (hN : 1 ≤ N) :
    ∑' j : ℕ, (1 : ℝ) / ((N + j : ℕ) : ℝ) ^ 3 ≤
      2 / (N : ℝ) ^ 2 := by
  let f : ℕ → ℝ := fun j ↦ (1 : ℝ) / ((N + j : ℕ) : ℝ) ^ 3
  let g : ℕ → ℝ := fun j ↦ 2 *
    ((1 : ℝ) / ((N + j : ℕ) : ℝ) ^ 2 -
      1 / ((N + j + 1 : ℕ) : ℝ) ^ 2)
  have htel := (hasSum_inv_sq_telescope N hN).mul_left (2 : ℝ)
  have hg : HasSum g (2 / (N : ℝ) ^ 2) := by
    simpa only [g, div_eq_mul_inv, one_mul] using htel
  have hf0 : ∀ j, 0 ≤ f j := by intro j; positivity
  have hfg : ∀ j, f j ≤ g j := by
    intro j
    dsimp only [f, g]
    simp only [Nat.cast_add, Nat.cast_one]
    let m : ℝ := (N : ℝ) + (j : ℝ)
    have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast (by omega : 1 ≤ N + j)
    change 1 / m ^ 3 ≤ 2 * (1 / m ^ 2 - 1 / (m + 1) ^ 2)
    have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
    have hm10 : 0 < m + 1 := by linarith
    field_simp [ne_of_gt hm0, ne_of_gt hm10]
    nlinarith [sq_nonneg (m - 1)]
  have hf : Summable f := hg.summable.of_nonneg_of_le hf0 hfg
  have hle := hf.tsum_le_tsum hfg hg.summable
  simpa only [f, g, hg.tsum_eq] using hle

/-- A sharper telescoping estimate once the tail starts beyond the analytic
threshold used by the diagonal correction bound. -/
theorem one_div_cube_tail_bound_sharp (N : ℕ) (hN : 16 ≤ N) :
    ∑' j : ℕ, (1 : ℝ) / ((N + j : ℕ) : ℝ) ^ 3 ≤
      11 / (20 * (N : ℝ) ^ 2) := by
  let f : ℕ → ℝ := fun j ↦ (1 : ℝ) / ((N + j : ℕ) : ℝ) ^ 3
  let g : ℕ → ℝ := fun j ↦ (11 / 20 : ℝ) *
    ((1 : ℝ) / ((N + j : ℕ) : ℝ) ^ 2 -
      1 / ((N + j + 1 : ℕ) : ℝ) ^ 2)
  have htel := (hasSum_inv_sq_telescope N (by omega)).mul_left (11 / 20 : ℝ)
  have hg : HasSum g (11 / (20 * (N : ℝ) ^ 2)) := by
    dsimp only [g]
    convert htel using 1
    ring
  have hf0 : ∀ j, 0 ≤ f j := by intro j; positivity
  have hfg : ∀ j, f j ≤ g j := by
    intro j
    dsimp only [f, g]
    simp only [Nat.cast_add, Nat.cast_one]
    let m : ℝ := (N : ℝ) + (j : ℝ)
    have hm : 16 ≤ m := by
      dsimp [m]
      exact_mod_cast (by omega : 16 ≤ N + j)
    have hm0 : 0 < m := by linarith
    have hm10 : 0 < m + 1 := by linarith
    change 1 / m ^ 3 ≤ (11 / 20 : ℝ) *
      (1 / m ^ 2 - 1 / (m + 1) ^ 2)
    field_simp [hm0.ne', hm10.ne']
    nlinarith [mul_nonneg (sub_nonneg.mpr hm)
      (show 0 ≤ 2 * m + 3 by linarith)]
  have hf : Summable f := hg.summable.of_nonneg_of_le hf0 hfg
  have hle := hf.tsum_le_tsum hfg hg.summable
  simpa only [f, g, hg.tsum_eq] using hle

theorem summable_abs_diagonalDyadicPairedCorrection_tail
    {L p : ℝ} {N : ℕ}
    (hLlo : (69 / 100 : ℝ) ≤ L) (hLhi : L ≤ 7 / 10)
    (hp : 0 ≤ p) (hN : 16 ≤ N) (hpN : p ≤ (N : ℝ) ^ 2) :
    Summable (fun j : ℕ ↦
      |diagonalDyadicPairedCorrection L p (N + j)|) := by
  let f : ℕ → ℝ := fun j ↦ (1 : ℝ) / ((N + j : ℕ) : ℝ) ^ 3
  let C : ℝ := 2 * p + 2
  let g : ℕ → ℝ := fun j ↦ C * f j
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hpoint : ∀ j : ℕ,
      |diagonalDyadicPairedCorrection L p (N + j)| ≤ g j := by
    intro j
    have hk : 16 ≤ N + j := by omega
    have hcast : (N : ℝ) ≤ (N + j : ℕ) := by
      exact_mod_cast Nat.le_add_right N j
    have hsq : (N : ℝ) ^ 2 ≤ ((N + j : ℕ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ hN0 hcast 2
    have hpk : p ≤ ((N + j : ℕ) : ℝ) ^ 2 := hpN.trans hsq
    have h := diagonalDyadicPairedCorrection_abs_le hLlo hLhi hp hk hpk
    dsimp only [g, C, f]
    simpa only [div_eq_mul_inv, one_mul] using h
  have hall : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ 3) := by
    simpa only [one_div] using
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (3 : ℕ)))
  have hf : Summable f := by
    have hshift := (summable_nat_add_iff N).2 hall
    simpa only [f, Nat.add_comm] using hshift
  have hg : Summable g := by
    dsimp only [g]
    exact hf.mul_left C
  exact hg.of_nonneg_of_le (fun j ↦ abs_nonneg _) hpoint

/-- Absolute dyadic correction tail for arbitrary frequency square `p`. -/
theorem diagonalDyadicPairedCorrection_abs_tail_le
    {L p : ℝ} {N : ℕ}
    (hLlo : (69 / 100 : ℝ) ≤ L) (hLhi : L ≤ 7 / 10)
    (hp : 0 ≤ p) (hN : 16 ≤ N) (hpN : p ≤ (N : ℝ) ^ 2) :
    (∑' j : ℕ, |diagonalDyadicPairedCorrection L p (N + j)|) ≤
      (4 * p + 4) / (N : ℝ) ^ 2 := by
  let f : ℕ → ℝ := fun j ↦ (1 : ℝ) / ((N + j : ℕ) : ℝ) ^ 3
  let C : ℝ := 2 * p + 2
  let g : ℕ → ℝ := fun j ↦ C * f j
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hpoint : ∀ j : ℕ,
      |diagonalDyadicPairedCorrection L p (N + j)| ≤ g j := by
    intro j
    have hk : 16 ≤ N + j := by omega
    have hcast : (N : ℝ) ≤ (N + j : ℕ) := by exact_mod_cast Nat.le_add_right N j
    have hsq : (N : ℝ) ^ 2 ≤ ((N + j : ℕ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ hN0 hcast 2
    have hpk : p ≤ ((N + j : ℕ) : ℝ) ^ 2 := hpN.trans hsq
    have h := diagonalDyadicPairedCorrection_abs_le hLlo hLhi hp hk hpk
    dsimp only [g, C, f]
    simpa only [div_eq_mul_inv, one_mul] using h
  have hall : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ 3) := by
    simpa only [one_div] using
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (3 : ℕ)))
  have hf : Summable f := by
    have hshift := (summable_nat_add_iff N).2 hall
    simpa only [f, Nat.add_comm] using hshift
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hg : Summable g := by
    dsimp only [g]
    exact hf.mul_left C
  have habs : Summable (fun j : ℕ ↦
      |diagonalDyadicPairedCorrection L p (N + j)|) :=
    hg.of_nonneg_of_le (fun j ↦ abs_nonneg _) hpoint
  have hle := habs.tsum_le_tsum hpoint hg
  calc
    (∑' j : ℕ, |diagonalDyadicPairedCorrection L p (N + j)|) ≤
        ∑' j : ℕ, g j := hle
    _ = C * ∑' j : ℕ, f j := by
      exact hf.tsum_mul_left C
    _ ≤ C * (2 / (N : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact one_div_cube_tail_bound N (by omega)
    _ = (4 * p + 4) / (N : ℝ) ^ 2 := by
      dsimp [C]
      ring

/-- Sharpened absolute correction tail, using the asymptotically optimal
telescoping scale up to a factor `11/10`. -/
theorem diagonalDyadicPairedCorrection_abs_tail_le_sharp
    {L p : ℝ} {N : ℕ}
    (hLlo : (69 / 100 : ℝ) ≤ L) (hLhi : L ≤ 7 / 10)
    (hp : 0 ≤ p) (hN : 16 ≤ N) (hpN : p ≤ (N : ℝ) ^ 2) :
    (∑' j : ℕ, |diagonalDyadicPairedCorrection L p (N + j)|) ≤
      11 * (p + 1) / (10 * (N : ℝ) ^ 2) := by
  let f : ℕ → ℝ := fun j ↦ (1 : ℝ) / ((N + j : ℕ) : ℝ) ^ 3
  let C : ℝ := 2 * p + 2
  let g : ℕ → ℝ := fun j ↦ C * f j
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hpoint : ∀ j : ℕ,
      |diagonalDyadicPairedCorrection L p (N + j)| ≤ g j := by
    intro j
    have hk : 16 ≤ N + j := by omega
    have hcast : (N : ℝ) ≤ (N + j : ℕ) := by
      exact_mod_cast Nat.le_add_right N j
    have hsq : (N : ℝ) ^ 2 ≤ ((N + j : ℕ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ hN0 hcast 2
    have hpk : p ≤ ((N + j : ℕ) : ℝ) ^ 2 := hpN.trans hsq
    have h := diagonalDyadicPairedCorrection_abs_le hLlo hLhi hp hk hpk
    dsimp only [g, C, f]
    simpa only [div_eq_mul_inv, one_mul] using h
  have hall : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ 3) := by
    simpa only [one_div] using
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (3 : ℕ)))
  have hf : Summable f := by
    have hshift := (summable_nat_add_iff N).2 hall
    simpa only [f, Nat.add_comm] using hshift
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hg : Summable g := by
    dsimp only [g]
    exact hf.mul_left C
  have habs : Summable (fun j : ℕ ↦
      |diagonalDyadicPairedCorrection L p (N + j)|) :=
    hg.of_nonneg_of_le (fun j ↦ abs_nonneg _) hpoint
  have hle := habs.tsum_le_tsum hpoint hg
  calc
    (∑' j : ℕ, |diagonalDyadicPairedCorrection L p (N + j)|) ≤
        ∑' j : ℕ, g j := hle
    _ = C * ∑' j : ℕ, f j := by
      exact hf.tsum_mul_left C
    _ ≤ C * (11 / (20 * (N : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact one_div_cube_tail_bound_sharp N hN
    _ = 11 * (p + 1) / (10 * (N : ℝ) ^ 2) := by
      dsimp [C]
      ring

theorem yoshidaLength_coarse_bounds :
    (69 / 100 : ℝ) ≤ yoshidaLength ∧ yoshidaLength ≤ 7 / 10 := by
  rw [yoshidaLength]
  have h := strict_log_two_bounds
  constructor <;> linarith

/-- Coarse mode-frequency square bound, sufficient to start every tail at
`N ≥ 10n`. -/
theorem yoshidaKappa_sq_le_hundred_mul_sq (n : ℕ) :
    yoshidaKappa n ^ 2 ≤ 100 * (n : ℝ) ^ 2 := by
  have hL := yoshidaLength_coarse_bounds
  have hL0 : 0 < yoshidaLength := yoshidaLength_pos
  have hpi := Real.pi_lt_d20
  have hratio : 2 * Real.pi / yoshidaLength < 10 := by
    rw [div_lt_iff₀ hL0]
    norm_num at hpi ⊢
    nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hkappa : yoshidaKappa n ≤ 10 * (n : ℝ) := by
    rw [yoshidaKappa]
    have hm := mul_le_mul_of_nonneg_right hratio.le hn0
    convert hm using 1
    all_goals ring
  have hkappa0 : 0 ≤ yoshidaKappa n := by
    rw [yoshidaKappa]
    positivity
  have hsquare := pow_le_pow_left₀ hkappa0 hkappa 2
  nlinarith

def yoshidaDiagonalDyadicPairedCorrection (n k : ℕ) : ℝ :=
  diagonalDyadicPairedCorrection yoshidaLength (yoshidaKappa n ^ 2) k

theorem summable_abs_yoshidaDiagonalDyadicPairedCorrection_tail
    {n N : ℕ} (hN : 16 ≤ N) (hmode : 10 * n ≤ N) :
    Summable (fun j : ℕ ↦
      |yoshidaDiagonalDyadicPairedCorrection n (N + j)|) := by
  have hL := yoshidaLength_coarse_bounds
  have hp : 0 ≤ yoshidaKappa n ^ 2 := sq_nonneg _
  have hpN : yoshidaKappa n ^ 2 ≤ (N : ℝ) ^ 2 := by
    have hkappa := yoshidaKappa_sq_le_hundred_mul_sq n
    have hcast : (10 : ℝ) * n ≤ N := by exact_mod_cast hmode
    have hsquare := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 10 * n) hcast 2
    nlinarith
  simpa only [yoshidaDiagonalDyadicPairedCorrection] using
    summable_abs_diagonalDyadicPairedCorrection_tail hL.1 hL.2 hp hN hpN

theorem yoshidaDiagonalDyadicPairedCorrection_abs_tail_le
    {n N : ℕ} (hN : 16 ≤ N) (hmode : 10 * n ≤ N) :
    (∑' j : ℕ, |yoshidaDiagonalDyadicPairedCorrection n (N + j)|) ≤
      (4 * yoshidaKappa n ^ 2 + 4) / (N : ℝ) ^ 2 := by
  have hL := yoshidaLength_coarse_bounds
  have hp : 0 ≤ yoshidaKappa n ^ 2 := sq_nonneg _
  have hpN : yoshidaKappa n ^ 2 ≤ (N : ℝ) ^ 2 := by
    have hkappa := yoshidaKappa_sq_le_hundred_mul_sq n
    have hcast : (10 : ℝ) * n ≤ N := by exact_mod_cast hmode
    have hsquare := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 10 * n) hcast 2
    nlinarith
  simpa only [yoshidaDiagonalDyadicPairedCorrection] using
    diagonalDyadicPairedCorrection_abs_tail_le hL.1 hL.2 hp hN hpN

theorem yoshidaDiagonalDyadicPairedCorrection_abs_tail_le_sharp
    {n N : ℕ} (hN : 16 ≤ N) (hmode : 10 * n ≤ N) :
    (∑' j : ℕ, |yoshidaDiagonalDyadicPairedCorrection n (N + j)|) ≤
      11 * (yoshidaKappa n ^ 2 + 1) / (10 * (N : ℝ) ^ 2) := by
  have hL := yoshidaLength_coarse_bounds
  have hp : 0 ≤ yoshidaKappa n ^ 2 := sq_nonneg _
  have hpN : yoshidaKappa n ^ 2 ≤ (N : ℝ) ^ 2 := by
    have hkappa := yoshidaKappa_sq_le_hundred_mul_sq n
    have hcast : (10 : ℝ) * n ≤ N := by exact_mod_cast hmode
    have hsquare := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 10 * n) hcast 2
    nlinarith
  simpa only [yoshidaDiagonalDyadicPairedCorrection] using
    diagonalDyadicPairedCorrection_abs_tail_le_sharp hL.1 hL.2 hp hN hpN

/-- Uniform rational tail budget for all ten target modes. -/
theorem yoshida_first_ten_diagonal_tail_le_three_div_twenty_thousand
    {n : ℕ} (hn : n ≤ 10) :
    (∑' j : ℕ,
      |yoshidaDiagonalDyadicPairedCorrection n (16384 + j)|) ≤
        (3 / 20000 : ℝ) := by
  have htail := yoshidaDiagonalDyadicPairedCorrection_abs_tail_le
    (n := n) (N := 16384) (by norm_num) (by omega)
  have hkappa := yoshidaKappa_sq_le_hundred_mul_sq n
  have hnR : (n : ℝ) ≤ 10 := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnSq : (n : ℝ) ^ 2 ≤ 100 := by nlinarith
  calc
    (∑' j : ℕ,
        |yoshidaDiagonalDyadicPairedCorrection n (16384 + j)|) ≤
      (4 * yoshidaKappa n ^ 2 + 4) / (16384 : ℝ) ^ 2 := htail
    _ ≤ (3 / 20000 : ℝ) := by
      norm_num
      nlinarith

end ArithmeticHodge.Analysis.YoshidaDiagonalSeriesTail
