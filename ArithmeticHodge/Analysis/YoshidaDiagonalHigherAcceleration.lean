import ArithmeticHodge.Analysis.YoshidaDiagonalMomentEnclosures

set_option autoImplicit false

open Filter Real
open scoped BigOperators Topology

namespace ArithmeticHodge.Analysis.YoshidaDiagonalHigherAcceleration

noncomputable section

open RatInterval
open YoshidaConstantBounds
open YoshidaDiagonalAcceleratedSeries
open YoshidaDiagonalMomentEnclosures
open YoshidaDiagonalSeriesTail
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures

/-!
# Higher-order acceleration for Yoshida diagonal moments

The production diagonal correction has an exact rational core plus two
dyadic endpoint terms.  This module retains the first three inverse-power
terms of that rational core.  The remaining rational error is sixth order,
while the dyadic error is ninth order from the production threshold
`k >= 16` onward.
-/

/-- Coefficient of `k^-3` in the rational diagonal core. -/
def diagonalCoreCoeffThree (L p : ℝ) : ℝ :=
  -(4 * L * p - L - 4) / (16 * L)

/-- Coefficient of `k^-4` in the rational diagonal core. -/
def diagonalCoreCoeffFour (L p : ℝ) : ℝ :=
  (12 * L * p - L + 24 * p - 6) / (64 * L)

/-- Coefficient of `k^-5` in the rational diagonal core. -/
def diagonalCoreCoeffFive (L p : ℝ) : ℝ :=
  (16 * L * p ^ 2 - 24 * L * p + L - 96 * p + 8) / (256 * L)

/-- Three-term inverse-power model for the rational diagonal core. -/
def diagonalHigherMain (L p k : ℝ) : ℝ :=
  diagonalCoreCoeffThree L p / k ^ 3 +
    diagonalCoreCoeffFour L p / k ^ 4 +
    diagonalCoreCoeffFive L p / k ^ 5

/-- Exact numerator left after removing the `k^-3`, `k^-4`, and `k^-5`
terms from `diagonalPairedCore`. -/
def diagonalHigherRemainderNumerator (L p k : ℝ) : ℝ :=
  -5120 * L * k ^ 3 * p ^ 2 + 2560 * L * k ^ 3 * p - 64 * L * k ^ 3 -
    1024 * L * k ^ 2 * p ^ 3 - 1280 * L * k ^ 2 * p ^ 2 +
    1600 * L * k ^ 2 * p - 48 * L * k ^ 2 - 1792 * L * k * p ^ 3 +
    960 * L * k * p ^ 2 + 304 * L * k * p - 12 * L * k -
    256 * L * p ^ 4 + 256 * L * p ^ 3 + 160 * L * p ^ 2 + 16 * L * p - L -
    10240 * k ^ 3 * p ^ 2 + 15360 * k ^ 3 * p - 640 * k ^ 3 +
    5120 * k ^ 2 * p ^ 2 + 7680 * k ^ 2 * p - 448 * k ^ 2 -
    1536 * k * p ^ 3 + 5760 * k * p ^ 2 + 1120 * k * p - 104 * k +
    1536 * p ^ 3 + 640 * p ^ 2 + 32 * p - 8

private theorem higher_rational_identity_aux
    {L p k Q : ℝ} (hL : L ≠ 0) (hk : k ≠ 0) (hQ : Q ≠ 0)
    (hQdef : Q = 16 * k ^ 2 + 8 * k + 4 * p + 1) :
    -diagonalCoreNumerator L p k / (4 * k ^ 2 * L * Q ^ 2) -
        diagonalHigherMain L p k =
      diagonalHigherRemainderNumerator L p k / (256 * L * k ^ 5 * Q ^ 2) := by
  unfold diagonalCoreNumerator diagonalHigherMain diagonalCoreCoeffThree
    diagonalCoreCoeffFour diagonalCoreCoeffFive diagonalHigherRemainderNumerator
  field_simp [hL, hk, hQ]
  rw [hQdef]
  ring

/-- Exact algebraic identity behind the higher-order acceleration. -/
theorem diagonalPairedCore_sub_higherMain_eq
    {L p k : ℝ} (hL : L ≠ 0) (hk : k ≠ 0)
    (hden : (2 * k + 1 / 2) ^ 2 + p ≠ 0) :
    diagonalPairedCore L p k - diagonalHigherMain L p k =
      diagonalHigherRemainderNumerator L p k /
        (4096 * L * k ^ 5 * ((2 * k + 1 / 2) ^ 2 + p) ^ 2) := by
  have hQ : 16 * k ^ 2 + 8 * k + 4 * p + 1 ≠ 0 := by
    rw [show 16 * k ^ 2 + 8 * k + 4 * p + 1 =
      4 * ((2 * k + 1 / 2) ^ 2 + p) by ring]
    exact mul_ne_zero (by norm_num) hden
  rw [diagonalPairedCore_eq hL hk hden]
  rw [show 64 * k ^ 2 * L * ((2 * k + 1 / 2) ^ 2 + p) ^ 2 =
      4 * k ^ 2 * L * (16 * k ^ 2 + 8 * k + 4 * p + 1) ^ 2 by ring]
  rw [show 4096 * L * k ^ 5 * ((2 * k + 1 / 2) ^ 2 + p) ^ 2 =
      256 * L * k ^ 5 * (16 * k ^ 2 + 8 * k + 4 * p + 1) ^ 2 by ring]
  exact higher_rational_identity_aux hL hk hQ rfl

/-- A deliberately simple positive majorant for the exact sixth-order
remainder numerator.  Its grouped shape is what survives division by the
quartic denominator. -/
def diagonalHigherRemainderMagnitude (L p k : ℝ) : ℝ :=
  20000 * (L + 1) *
    (k ^ 3 * (p + 1) ^ 2 + k ^ 2 * (p + 1) ^ 3 +
      k * (p + 1) ^ 3 + (p + 1) ^ 4)

private theorem diagonalHigherRemainderNumerator_abs_le_magnitude
    {L p k : ℝ} (hL : 0 ≤ L) (hp : 0 ≤ p) (hk : 1 ≤ k) :
    |diagonalHigherRemainderNumerator L p k| ≤
      diagonalHigherRemainderMagnitude L p k := by
  rw [abs_le]
  constructor
  · have h : 0 ≤ diagonalHigherRemainderMagnitude L p k +
        diagonalHigherRemainderNumerator L p k := by
      unfold diagonalHigherRemainderMagnitude diagonalHigherRemainderNumerator
      ring_nf
      positivity
    linarith
  · have h : 0 ≤ diagonalHigherRemainderMagnitude L p k -
        diagonalHigherRemainderNumerator L p k := by
      unfold diagonalHigherRemainderMagnitude diagonalHigherRemainderNumerator
      ring_nf
      positivity
    linarith

/-- Pointwise sixth-order envelope for the rational remainder. -/
def diagonalHigherRemainderBound (p k : ℝ) : ℝ :=
  (p + 1) ^ 2 / k ^ 6 + (p + 1) ^ 3 / k ^ 7 +
    (p + 1) ^ 3 / k ^ 8 + (p + 1) ^ 4 / k ^ 9

theorem diagonalPairedCore_sub_higherMain_abs_le
    {L p k : ℝ}
    (hLlo : (69 / 100 : ℝ) ≤ L) (hp : 0 ≤ p) (hk : 1 ≤ k) :
    |diagonalPairedCore L p k - diagonalHigherMain L p k| ≤
      diagonalHigherRemainderBound p k := by
  have hL0 : 0 < L := by linarith
  have hk0 : 0 < k := by linarith
  have hd : 0 < (2 * k + 1 / 2) ^ 2 + p := by positivity
  have hQ : 0 < 16 * k ^ 2 + 8 * k + 4 * p + 1 := by positivity
  rw [diagonalPairedCore_sub_higherMain_eq hL0.ne' hk0.ne' hd.ne']
  rw [show 4096 * L * k ^ 5 * ((2 * k + 1 / 2) ^ 2 + p) ^ 2 =
      256 * L * k ^ 5 * (16 * k ^ 2 + 8 * k + 4 * p + 1) ^ 2 by ring]
  let A : ℝ := k ^ 3 * (p + 1) ^ 2 + k ^ 2 * (p + 1) ^ 3 +
    k * (p + 1) ^ 3 + (p + 1) ^ 4
  let D : ℝ := 256 * L * k ^ 5 *
    (16 * k ^ 2 + 8 * k + 4 * p + 1) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hnum := diagonalHigherRemainderNumerator_abs_le_magnitude
    hL0.le hp hk
  have hcoef : 20000 * (L + 1) ≤ 65536 * L := by nlinarith
  have hQlo : 16 * k ^ 2 ≤ 16 * k ^ 2 + 8 * k + 4 * p + 1 := by
    nlinarith
  have hQsq : (16 * k ^ 2) ^ 2 ≤
      (16 * k ^ 2 + 8 * k + 4 * p + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hQlo 2
  have hDlo : 65536 * L * k ^ 9 ≤ D := by
    dsimp [D]
    have hm := mul_le_mul_of_nonneg_left hQsq
      (show 0 ≤ 256 * L * k ^ 5 by positivity)
    nlinarith
  have hM : diagonalHigherRemainderMagnitude L p k ≤ 65536 * L * A := by
    dsimp [diagonalHigherRemainderMagnitude, A]
    exact mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hnumA : |diagonalHigherRemainderNumerator L p k| ≤
      65536 * L * A := hnum.trans hM
  have hk9 : 0 < k ^ 9 := by positivity
  have hboundEq : diagonalHigherRemainderBound p k = A / k ^ 9 := by
    dsimp [diagonalHigherRemainderBound, A]
    field_simp [hk0.ne']
  rw [abs_div, abs_of_pos hD, hboundEq]
  rw [div_le_div_iff₀ hD hk9]
  have hleft := mul_le_mul_of_nonneg_right hnumA (show 0 ≤ k ^ 9 by positivity)
  have hright := mul_le_mul_of_nonneg_left hDlo hA
  nlinarith

/-! ## Dyadic endpoint errors at ninth order -/

theorem natCast_pow_eight_le_four_pow
    {k : ℕ} (hk : 16 ≤ k) :
    (k : ℝ) ^ 8 ≤ (4 : ℝ) ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ]
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hkR : (16 : ℝ) ≤ k := by exact_mod_cast hk
      have hstep : (k : ℝ) + 1 ≤ (17 / 16 : ℝ) * k := by nlinarith
      have hp : ((k : ℝ) + 1) ^ 8 ≤ ((17 / 16 : ℝ) * k) ^ 8 :=
        pow_le_pow_left₀ (by positivity) hstep 8
      calc
        ((k : ℝ) + 1) ^ 8 ≤ ((17 / 16 : ℝ) * k) ^ 8 := hp
        _ = (17 / 16 : ℝ) ^ 8 * (k : ℝ) ^ 8 := by ring
        _ ≤ 4 * (k : ℝ) ^ 8 := by
          apply mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ ≤ 4 * (4 : ℝ) ^ k := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (4 : ℝ) ^ k * 4 := by ring

theorem dyadic_endpoint_factors_le_inv_eight
    {k : ℕ} (hk : 16 ≤ k) :
    (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k ≤ 1 / (k : ℝ) ^ 8 ∧
      1 / (4 : ℝ) ^ k ≤ 1 / (k : ℝ) ^ 8 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpow := natCast_pow_eight_le_four_pow hk
  have hinv : 1 / (4 : ℝ) ^ k ≤ 1 / (k : ℝ) ^ 8 :=
    one_div_le_one_div_of_le (by positivity) hpow
  have hsqrt : (Real.sqrt 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact Real.one_le_sqrt.mpr (by norm_num)
  constructor
  · calc
      (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k ≤ 1 / (4 : ℝ) ^ k := by
        exact div_le_div_of_nonneg_right hsqrt (by positivity)
      _ ≤ 1 / (k : ℝ) ^ 8 := hinv
  · exact hinv

private theorem diagonalExponentialError_le_inv_nine
    {L p k q r : ℝ}
    (hL : (69 / 100 : ℝ) ≤ L) (hp : 0 ≤ p) (hpk : p ≤ k ^ 2)
    (hk : 16 ≤ k) (hq0 : 0 ≤ q) (hq : q ≤ 1 / k ^ 8)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / k ^ 8) :
    0 ≤ diagonalExponentialError L p k q r ∧
      diagonalExponentialError L p k q r ≤ 2 / k ^ 9 := by
  let a : ℝ := 2 * k + 1 / 2
  let d : ℝ := a ^ 2 + p
  let num : ℝ := a ^ 2 - p
  have hk0 : 0 < k := by linarith
  have hL0 : 0 < L := by linarith
  have ha2 : 4 * k ^ 2 ≤ a ^ 2 := by dsimp [a]; nlinarith [sq_nonneg k]
  have hnum0 : 0 ≤ num := by dsimp [num]; nlinarith
  have hnumd : num ≤ d := by dsimp [num, d]; linarith
  have hdlo : 4 * k ^ 2 ≤ d := by dsimp [d]; linarith
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hdlo
  have hLdk : 2 * k ^ 2 ≤ L * d := by
    have h1 := mul_le_mul_of_nonneg_left hdlo hL0.le
    have h2 := mul_le_mul_of_nonneg_right hL (show 0 ≤ 4 * k ^ 2 by positivity)
    nlinarith
  have hfirst : 2 * q * num / (L * d ^ 2) ≤ 1 / k ^ 10 := by
    rw [div_le_div_iff₀ (by positivity : 0 < L * d ^ 2)
      (by positivity : 0 < k ^ 10)]
    have hqscaled : q * k ^ 8 ≤ 1 := by
      have hm := mul_le_mul_of_nonneg_right hq (show 0 ≤ k ^ 8 by positivity)
      field_simp [hk0.ne'] at hm
      nlinarith
    have hnumstep := mul_le_mul_of_nonneg_left hnumd (show 0 ≤ 2 * q by positivity)
    have hdenstep := mul_le_mul_of_nonneg_right hLdk hd0.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hqscaled)
      (show 0 ≤ 2 * num * k ^ 2 by positivity)]
  have hrterm : r / k ≤ 1 / k ^ 9 := by
    rw [div_le_div_iff₀ hk0 (by positivity : 0 < k ^ 9)]
    have hm := mul_le_mul_of_nonneg_right hr (show 0 ≤ k ^ 8 by positivity)
    field_simp [hk0.ne'] at hm
    nlinarith
  have herr0 : 0 ≤ 2 * q * num / (L * d ^ 2) + r / k := by positivity
  have herr : 2 * q * num / (L * d ^ 2) + r / k ≤ 2 / k ^ 9 := by
    have hk9 : 0 < k ^ 9 := by positivity
    calc
      2 * q * num / (L * d ^ 2) + r / k ≤
          1 / k ^ 10 + 1 / k ^ 9 := add_le_add hfirst hrterm
      _ ≤ 2 / k ^ 9 := by
        field_simp [hk0.ne']
        nlinarith
  simpa only [diagonalExponentialError, a, d, num] using And.intro herr0 herr

theorem diagonalDyadicExponentialError_le_inv_nine
    {L p : ℝ} {k : ℕ}
    (hL : (69 / 100 : ℝ) ≤ L) (hp : 0 ≤ p)
    (hk : 16 ≤ k) (hpk : p ≤ (k : ℝ) ^ 2) :
    0 ≤ diagonalExponentialError L p k
        ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) (1 / (4 : ℝ) ^ k) ∧
      diagonalExponentialError L p k
        ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) (1 / (4 : ℝ) ^ k) ≤
          2 / (k : ℝ) ^ 9 := by
  have hfac := dyadic_endpoint_factors_le_inv_eight hk
  apply diagonalExponentialError_le_inv_nine hL hp hpk (by exact_mod_cast hk)
  · positivity
  · exact hfac.1
  · positivity
  · exact hfac.2

/-- The production dyadic correction differs from its three-term inverse-power
model by a sixth-order rational remainder and a ninth-order endpoint error. -/
theorem diagonalDyadicPairedCorrection_sub_higherMain_abs_le
    {L p : ℝ} {k : ℕ}
    (hL : (69 / 100 : ℝ) ≤ L) (hp : 0 ≤ p)
    (hk : 16 ≤ k) (hpk : p ≤ (k : ℝ) ^ 2) :
    |diagonalDyadicPairedCorrection L p k - diagonalHigherMain L p k| ≤
      diagonalHigherRemainderBound p k + 2 / (k : ℝ) ^ 9 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hcore := diagonalPairedCore_sub_higherMain_abs_le hL hp hkR
  have herr := diagonalDyadicExponentialError_le_inv_nine hL hp hk hpk
  rw [diagonalDyadicPairedCorrection, diagonalPairedCorrection_eq]
  calc
    |diagonalPairedCore L p k +
          diagonalExponentialError L p k
            ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) (1 / (4 : ℝ) ^ k) -
        diagonalHigherMain L p k| ≤
        |diagonalPairedCore L p k - diagonalHigherMain L p k| +
          |diagonalExponentialError L p k
            ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) (1 / (4 : ℝ) ^ k)| := by
      rw [show diagonalPairedCore L p k +
          diagonalExponentialError L p k
            ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) (1 / (4 : ℝ) ^ k) -
          diagonalHigherMain L p k =
        (diagonalPairedCore L p k - diagonalHigherMain L p k) +
          diagonalExponentialError L p k
            ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) (1 / (4 : ℝ) ^ k) by ring]
      exact abs_add_le _ _
    _ = |diagonalPairedCore L p k - diagonalHigherMain L p k| +
          diagonalExponentialError L p k
            ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) (1 / (4 : ℝ) ^ k) := by
      rw [abs_of_nonneg herr.1]
    _ ≤ diagonalHigherRemainderBound p k + 2 / (k : ℝ) ^ 9 :=
      add_le_add hcore herr.2

theorem yoshidaDiagonalCorrection_sub_higherMain_abs_le
    {n k : ℕ} (hk : 16 ≤ k) (hmode : 10 * n ≤ k) :
    |yoshidaDiagonalDyadicPairedCorrection n k -
        diagonalHigherMain yoshidaLength (yoshidaKappa n ^ 2) k| ≤
      diagonalHigherRemainderBound (yoshidaKappa n ^ 2) k + 2 / (k : ℝ) ^ 9 := by
  have hL := yoshidaLength_coarse_bounds
  have hp : 0 ≤ yoshidaKappa n ^ 2 := sq_nonneg _
  have hpK : yoshidaKappa n ^ 2 ≤ (k : ℝ) ^ 2 := by
    have hkappa := yoshidaKappa_sq_le_hundred_mul_sq n
    have hcast : (10 : ℝ) * n ≤ k := by exact_mod_cast hmode
    have hsquare := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 10 * n) hcast 2
    nlinarith
  simpa only [yoshidaDiagonalDyadicPairedCorrection] using
    diagonalDyadicPairedCorrection_sub_higherMain_abs_le hL.1 hp hk hpK

/-! ## Tight reciprocal-power tails for the explicit main terms -/

def diagonalInvPow (x : ℝ) (s : ℕ) (j : ℕ) : ℝ :=
  1 / (x + j) ^ s

def diagonalInvPowLowerPotential (x : ℝ) (s : ℕ) (j : ℕ) : ℝ :=
  1 / ((s - 1 : ℕ) * (x + j) ^ (s - 1))

def diagonalInvPowUpperPotential (x : ℝ) (s : ℕ) (j : ℕ) : ℝ :=
  diagonalInvPow x s j + diagonalInvPowLowerPotential x s j

private theorem summable_diagonalInvPow
    {x : ℝ} (hx : 1 ≤ x) {s : ℕ} (hs : 1 < s) :
    Summable (diagonalInvPow x s) := by
  have h := (Real.summable_one_div_nat_add_rpow x (s : ℝ)).2 (by
    exact_mod_cast hs)
  apply h.congr
  intro j
  rw [diagonalInvPow, abs_of_pos (by positivity : 0 < (j : ℝ) + x),
    Real.rpow_natCast]
  congr 2
  ring

private theorem tendsto_diagonalInvPow
    (x : ℝ) {s : ℕ} (hs : 0 < s) :
    Tendsto (diagonalInvPow x s) atTop (nhds 0) := by
  have htop : Tendsto (fun j : ℕ ↦ x + (j : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv : Tendsto (fun j : ℕ ↦ (x + (j : ℝ))⁻¹) atTop (nhds 0) := by
    simpa only [one_div] using htop.const_div_atTop 1
  have hp := hinv.pow s
  convert hp using 1
  · funext j
    rw [diagonalInvPow, one_div, inv_pow]
  · simp [hs.ne']

private theorem tendsto_diagonalInvPowLowerPotential
    (x : ℝ) {s : ℕ} (hs : 1 < s) :
    Tendsto (diagonalInvPowLowerPotential x s) atTop (nhds 0) := by
  have hp := tendsto_diagonalInvPow x (Nat.sub_pos_of_lt hs)
  have hscale := hp.const_mul (((s - 1 : ℕ) : ℝ))⁻¹
  have heq : diagonalInvPowLowerPotential x s =
      fun j ↦ (((s - 1 : ℕ) : ℝ))⁻¹ * diagonalInvPow x (s - 1) j := by
    funext j
    rw [diagonalInvPowLowerPotential, diagonalInvPow]
    ring
  rw [heq]
  simpa using hscale

private theorem tendsto_diagonalInvPowUpperPotential
    (x : ℝ) {s : ℕ} (hs : 1 < s) :
    Tendsto (diagonalInvPowUpperPotential x s) atTop (nhds 0) := by
  simpa only [diagonalInvPowUpperPotential, zero_add] using
    (tendsto_diagonalInvPow x (by omega : 0 < s)).add
      (tendsto_diagonalInvPowLowerPotential x hs)

private theorem tsum_bounds_of_telescope
    {f lower upper : ℕ → ℝ}
    (hs : Summable f)
    (hlower : ∀ j, lower j - lower (j + 1) ≤ f j)
    (hupper : ∀ j, f j ≤ upper j - upper (j + 1))
    (hlowerLim : Tendsto lower atTop (nhds 0))
    (hupperLim : Tendsto upper atTop (nhds 0)) :
    lower 0 ≤ ∑' j, f j ∧ (∑' j, f j) ≤ upper 0 := by
  have hpartialLower (N : ℕ) :
      lower 0 - lower N ≤ ∑ j ∈ Finset.range N, f j := by
    rw [← Finset.sum_range_sub' lower]
    exact Finset.sum_le_sum fun j _ ↦ hlower j
  have hpartialUpper (N : ℕ) :
      (∑ j ∈ Finset.range N, f j) ≤ upper 0 - upper N := by
    rw [← Finset.sum_range_sub' upper]
    exact Finset.sum_le_sum fun j _ ↦ hupper j
  have hpartial := hs.hasSum.tendsto_sum_nat
  have hlowerLimit : Tendsto (fun N ↦ lower 0 - lower N)
      atTop (nhds (lower 0)) := by
    simpa using tendsto_const_nhds.sub hlowerLim
  have hupperLimit : Tendsto (fun N ↦ upper 0 - upper N)
      atTop (nhds (upper 0)) := by
    simpa using tendsto_const_nhds.sub hupperLim
  exact ⟨le_of_tendsto_of_tendsto hlowerLimit hpartial
      (Filter.Eventually.of_forall hpartialLower),
    le_of_tendsto_of_tendsto hpartial hupperLimit
      (Filter.Eventually.of_forall hpartialUpper)⟩

private theorem diagonalInvPowLowerPotential_sub_succ_le
    {x : ℝ} (hx : 1 ≤ x) {s : ℕ}
    (hs : s = 3 ∨ s = 4 ∨ s = 5) (j : ℕ) :
    diagonalInvPowLowerPotential x s j -
        diagonalInvPowLowerPotential x s (j + 1) ≤
      diagonalInvPow x s j := by
  let a : ℝ := x + j
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha1 : 0 < a + 1 := by positivity
  rcases hs with (rfl | rfl | rfl)
  · dsimp [diagonalInvPowLowerPotential, diagonalInvPow, a]
    push_cast
    field_simp [ha.ne', ha1.ne']
    nlinarith
  · dsimp [diagonalInvPowLowerPotential, diagonalInvPow, a]
    push_cast
    field_simp [ha.ne', ha1.ne']
    nlinarith [sq_nonneg a, sq_nonneg (a + 1)]
  · dsimp [diagonalInvPowLowerPotential, diagonalInvPow, a]
    push_cast
    field_simp [ha.ne', ha1.ne']
    nlinarith [sq_nonneg a, sq_nonneg (a + 1),
      sq_nonneg (a ^ 2), sq_nonneg ((a + 1) ^ 2)]

private theorem diagonalInvPow_le_upperPotential_sub_succ
    {x : ℝ} (hx : 1 ≤ x) {s : ℕ}
    (hs : s = 3 ∨ s = 4 ∨ s = 5) (j : ℕ) :
    diagonalInvPow x s j ≤
      diagonalInvPowUpperPotential x s j -
        diagonalInvPowUpperPotential x s (j + 1) := by
  let a : ℝ := x + j
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha1 : 0 < a + 1 := by positivity
  rcases hs with (rfl | rfl | rfl)
  · dsimp [diagonalInvPowUpperPotential, diagonalInvPowLowerPotential,
      diagonalInvPow, a]
    push_cast
    field_simp [ha.ne', ha1.ne']
    nlinarith [sq_nonneg a, sq_nonneg (a + 1)]
  · dsimp [diagonalInvPowUpperPotential, diagonalInvPowLowerPotential,
      diagonalInvPow, a]
    push_cast
    field_simp [ha.ne', ha1.ne']
    nlinarith [sq_nonneg a, sq_nonneg (a + 1),
      sq_nonneg (a ^ 2), sq_nonneg ((a + 1) ^ 2)]
  · dsimp [diagonalInvPowUpperPotential, diagonalInvPowLowerPotential,
      diagonalInvPow, a]
    push_cast
    field_simp [ha.ne', ha1.ne']
    nlinarith [sq_nonneg a, sq_nonneg (a + 1),
      sq_nonneg (a ^ 2), sq_nonneg ((a + 1) ^ 2),
      sq_nonneg (a ^ 3), sq_nonneg ((a + 1) ^ 3)]

/-- Tight rational two-sided bounds for the three explicit inverse-power
tails retained by `diagonalHigherMain`. -/
theorem diagonalInvPow_tsum_bounds
    {x : ℝ} (hx : 1 ≤ x) {s : ℕ}
    (hs : s = 3 ∨ s = 4 ∨ s = 5) :
    diagonalInvPowLowerPotential x s 0 ≤
        ∑' j, diagonalInvPow x s j ∧
      (∑' j, diagonalInvPow x s j) ≤
        diagonalInvPowUpperPotential x s 0 := by
  have hs1 : 1 < s := by rcases hs with (rfl | rfl | rfl) <;> norm_num
  exact tsum_bounds_of_telescope
    (summable_diagonalInvPow hx hs1)
    (diagonalInvPowLowerPotential_sub_succ_le hx hs)
    (diagonalInvPow_le_upperPotential_sub_succ hx hs)
    (tendsto_diagonalInvPowLowerPotential x hs1)
    (tendsto_diagonalInvPowUpperPotential x hs1)

/-! ## Summed sixth-order remainder -/

def diagonalHigherTailScale (p N : ℝ) : ℝ :=
  (p + 1) ^ 2 / N ^ 3 + (p + 1) ^ 3 / N ^ 4 +
    (p + 1) ^ 3 / N ^ 5 + ((p + 1) ^ 4 + 2) / N ^ 6

def diagonalHigherResidualTailRadius (p N : ℝ) : ℝ :=
  11 * diagonalHigherTailScale p N / (20 * N ^ 2)

private theorem one_div_pow_le_scaled_cube
    {x y : ℝ} {s : ℕ} (hx : 0 < x) (hxy : x ≤ y) (hs : 3 ≤ s) :
    1 / y ^ s ≤ (1 / x ^ (s - 3)) * (1 / y ^ 3) := by
  have hy : 0 < y := hx.trans_le hxy
  have hpow : x ^ (s - 3) ≤ y ^ (s - 3) :=
    pow_le_pow_left₀ hx.le hxy (s - 3)
  have hinv : 1 / y ^ (s - 3) ≤ 1 / x ^ (s - 3) :=
    one_div_le_one_div_of_le (by positivity) hpow
  calc
    1 / y ^ s = (1 / y ^ (s - 3)) * (1 / y ^ 3) := by
      rw [show s = (s - 3) + 3 by omega, pow_add]
      field_simp [hy.ne']
      congr 1
    _ ≤ (1 / x ^ (s - 3)) * (1 / y ^ 3) :=
      mul_le_mul_of_nonneg_right hinv (by positivity)

private theorem higher_pointwise_bound_le_scaled_cube
    {p N k : ℝ} (hp : 0 ≤ p) (hN : 0 < N) (hNk : N ≤ k) :
    diagonalHigherRemainderBound p k + 2 / k ^ 9 ≤
      diagonalHigherTailScale p N * (1 / k ^ 3) := by
  have h6 := one_div_pow_le_scaled_cube hN hNk (by norm_num : 3 ≤ 6)
  have h7 := one_div_pow_le_scaled_cube hN hNk (by norm_num : 3 ≤ 7)
  have h8 := one_div_pow_le_scaled_cube hN hNk (by norm_num : 3 ≤ 8)
  have h9 := one_div_pow_le_scaled_cube hN hNk (by norm_num : 3 ≤ 9)
  norm_num at h6 h7 h8 h9
  have h6' := mul_le_mul_of_nonneg_left h6 (show 0 ≤ (p + 1) ^ 2 by positivity)
  have h7' := mul_le_mul_of_nonneg_left h7 (show 0 ≤ (p + 1) ^ 3 by positivity)
  have h8' := mul_le_mul_of_nonneg_left h8 (show 0 ≤ (p + 1) ^ 3 by positivity)
  have h9' := mul_le_mul_of_nonneg_left h9 (show 0 ≤ (p + 1) ^ 4 + 2 by positivity)
  calc
    diagonalHigherRemainderBound p k + 2 / k ^ 9 =
        (p + 1) ^ 2 * (1 / k ^ 6) +
          (p + 1) ^ 3 * (1 / k ^ 7) +
          (p + 1) ^ 3 * (1 / k ^ 8) +
          ((p + 1) ^ 4 + 2) * (1 / k ^ 9) := by
      unfold diagonalHigherRemainderBound
      ring
    _ ≤ (p + 1) ^ 2 * ((1 / N ^ 3) * (1 / k ^ 3)) +
          (p + 1) ^ 3 * ((1 / N ^ 4) * (1 / k ^ 3)) +
          (p + 1) ^ 3 * ((1 / N ^ 5) * (1 / k ^ 3)) +
          ((p + 1) ^ 4 + 2) * ((1 / N ^ 6) * (1 / k ^ 3)) := by
      simpa only [one_div] using
        add_le_add (add_le_add (add_le_add h6' h7') h8') h9'
    _ = diagonalHigherTailScale p N * (1 / k ^ 3) := by
      unfold diagonalHigherTailScale
      ring

def diagonalHigherMainTail (L p : ℝ) (N : ℕ) : ℝ :=
  diagonalCoreCoeffThree L p * (∑' j, diagonalInvPow N 3 j) +
    diagonalCoreCoeffFour L p * (∑' j, diagonalInvPow N 4 j) +
    diagonalCoreCoeffFive L p * (∑' j, diagonalInvPow N 5 j)

private theorem summable_diagonalHigherMain_tail
    {L p : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun j : ℕ ↦
      diagonalHigherMain L p (((N + j : ℕ) : ℝ))) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h3 := summable_diagonalInvPow hNR (by norm_num : 1 < 3)
  have h4 := summable_diagonalInvPow hNR (by norm_num : 1 < 4)
  have h5 := summable_diagonalInvPow hNR (by norm_num : 1 < 5)
  have hsum := ((h3.mul_left (diagonalCoreCoeffThree L p)).add
    (h4.mul_left (diagonalCoreCoeffFour L p))).add
      (h5.mul_left (diagonalCoreCoeffFive L p))
  apply hsum.congr
  intro j
  unfold diagonalHigherMain diagonalInvPow
  norm_num only [Nat.cast_add]
  ring

private theorem tsum_diagonalHigherMain_tail
    {L p : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    (∑' j : ℕ, diagonalHigherMain L p (((N + j : ℕ) : ℝ))) =
      diagonalHigherMainTail L p N := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h3 := summable_diagonalInvPow hNR (by norm_num : 1 < 3)
  have h4 := summable_diagonalInvPow hNR (by norm_num : 1 < 4)
  have h5 := summable_diagonalInvPow hNR (by norm_num : 1 < 5)
  have hfun : (fun j : ℕ ↦
      diagonalHigherMain L p (((N + j : ℕ) : ℝ))) =
      fun j ↦ diagonalCoreCoeffThree L p * diagonalInvPow N 3 j +
        diagonalCoreCoeffFour L p * diagonalInvPow N 4 j +
        diagonalCoreCoeffFive L p * diagonalInvPow N 5 j := by
    funext j
    unfold diagonalHigherMain diagonalInvPow
    norm_num only [Nat.cast_add]
    ring
  rw [hfun]
  rw [Summable.tsum_add
    ((h3.mul_left (diagonalCoreCoeffThree L p)).add
      (h4.mul_left (diagonalCoreCoeffFour L p)))
    (h5.mul_left (diagonalCoreCoeffFive L p))]
  rw [Summable.tsum_add (h3.mul_left (diagonalCoreCoeffThree L p))
    (h4.mul_left (diagonalCoreCoeffFour L p))]
  rw [h3.tsum_mul_left, h4.tsum_mul_left, h5.tsum_mul_left]
  rfl

/-- The actual infinite correction tail is enclosed by the explicit
three-term inverse-power tail plus the sixth-order residual radius. -/
theorem diagonalDyadicCorrection_tail_sub_higherMainTail_abs_le
    {L p : ℝ} {N : ℕ}
    (hLlo : (69 / 100 : ℝ) ≤ L) (hLhi : L ≤ 7 / 10)
    (hp : 0 ≤ p) (hN : 16 ≤ N) (hpN : p ≤ (N : ℝ) ^ 2) :
    |(∑' j : ℕ, diagonalDyadicPairedCorrection L p (N + j)) -
        diagonalHigherMainTail L p N| ≤
      diagonalHigherResidualTailRadius p N := by
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNR0 : (0 : ℝ) < N := by positivity
  have hactualAbs := summable_abs_diagonalDyadicPairedCorrection_tail
    hLlo hLhi hp hN hpN
  have hactual : Summable (fun j : ℕ ↦
      diagonalDyadicPairedCorrection L p (N + j)) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using hactualAbs
  have hmain := summable_diagonalHigherMain_tail (L := L) (p := p) hN1
  have hscale : 0 ≤ diagonalHigherTailScale p N := by
    unfold diagonalHigherTailScale
    positivity
  let g : ℕ → ℝ := fun j ↦
    diagonalHigherTailScale p N * diagonalInvPow N 3 j
  have hg : Summable g := by
    dsimp [g]
    exact (summable_diagonalInvPow hNR (by norm_num : 1 < 3)).mul_left _
  have hpoint : ∀ j : ℕ,
      |diagonalDyadicPairedCorrection L p (N + j) -
          diagonalHigherMain L p (((N + j : ℕ) : ℝ))| ≤ g j := by
    intro j
    have hk : 16 ≤ N + j := by omega
    have hcast : (N : ℝ) ≤ (N + j : ℕ) := by
      exact_mod_cast Nat.le_add_right N j
    have hsq : (N : ℝ) ^ 2 ≤ ((N + j : ℕ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hcast 2
    have hpk : p ≤ ((N + j : ℕ) : ℝ) ^ 2 := hpN.trans hsq
    have hterm := diagonalDyadicPairedCorrection_sub_higherMain_abs_le
      hLlo hp hk hpk
    have hscaled := higher_pointwise_bound_le_scaled_cube hp hNR0 hcast
    calc
      |diagonalDyadicPairedCorrection L p (N + j) -
          diagonalHigherMain L p (((N + j : ℕ) : ℝ))| ≤
          diagonalHigherRemainderBound p (((N + j : ℕ) : ℝ)) +
            2 / ((N + j : ℕ) : ℝ) ^ 9 := hterm
      _ ≤ diagonalHigherTailScale p N *
          (1 / ((N + j : ℕ) : ℝ) ^ 3) := hscaled
      _ = g j := by
        unfold g diagonalInvPow
        norm_num only [Nat.cast_add]
  have hdiffAbs : Summable (fun j : ℕ ↦
      |diagonalDyadicPairedCorrection L p (N + j) -
        diagonalHigherMain L p (((N + j : ℕ) : ℝ))|) :=
    hg.of_nonneg_of_le (fun j ↦ abs_nonneg _) hpoint
  have hnorm :
      |(∑' j : ℕ, (diagonalDyadicPairedCorrection L p (N + j) -
          diagonalHigherMain L p (((N + j : ℕ) : ℝ))))| ≤
        ∑' j : ℕ, |diagonalDyadicPairedCorrection L p (N + j) -
          diagonalHigherMain L p (((N + j : ℕ) : ℝ))| := by
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_le_tsum_norm (f := fun j : ℕ ↦
        diagonalDyadicPairedCorrection L p (N + j) -
          diagonalHigherMain L p (((N + j : ℕ) : ℝ))) hdiffAbs)
  have hsumPoint := hdiffAbs.tsum_le_tsum hpoint hg
  have hcube := one_div_cube_tail_bound_sharp N hN
  have hgSum : (∑' j : ℕ, g j) = diagonalHigherTailScale p N *
      (∑' j : ℕ, (1 : ℝ) / ((N + j : ℕ) : ℝ) ^ 3) := by
    calc
      (∑' j : ℕ, g j) = diagonalHigherTailScale p N *
          (∑' j : ℕ, diagonalInvPow N 3 j) := by
        dsimp [g]
        rw [(summable_diagonalInvPow hNR (by norm_num : 1 < 3)).tsum_mul_left]
      _ = diagonalHigherTailScale p N *
          (∑' j : ℕ, (1 : ℝ) / ((N + j : ℕ) : ℝ) ^ 3) := by
        congr 1
        apply tsum_congr
        intro j
        unfold diagonalInvPow
        norm_num only [Nat.cast_add]
  have hradius : (∑' j : ℕ, g j) ≤
      diagonalHigherResidualTailRadius p N := by
    rw [hgSum]
    unfold diagonalHigherResidualTailRadius
    have hm := mul_le_mul_of_nonneg_left hcube hscale
    calc
      diagonalHigherTailScale p N *
          (∑' j : ℕ, (1 : ℝ) / ((N + j : ℕ) : ℝ) ^ 3) ≤
          diagonalHigherTailScale p N * (11 / (20 * (N : ℝ) ^ 2)) := hm
      _ = 11 * diagonalHigherTailScale p N / (20 * (N : ℝ) ^ 2) := by ring
  rw [← tsum_diagonalHigherMain_tail (L := L) (p := p) hN1]
  rw [← hactual.tsum_sub hmain]
  exact hnorm.trans (hsumPoint.trans hradius)

theorem yoshidaDiagonalCorrection_tail_sub_higherMainTail_abs_le
    {n N : ℕ} (hN : 16 ≤ N) (hmode : 10 * n ≤ N) :
    |(∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)) -
        diagonalHigherMainTail yoshidaLength (yoshidaKappa n ^ 2) N| ≤
      diagonalHigherResidualTailRadius (yoshidaKappa n ^ 2) N := by
  have hL := yoshidaLength_coarse_bounds
  have hp : 0 ≤ yoshidaKappa n ^ 2 := sq_nonneg _
  have hpN : yoshidaKappa n ^ 2 ≤ (N : ℝ) ^ 2 := by
    have hkappa := yoshidaKappa_sq_le_hundred_mul_sq n
    have hcast : (10 : ℝ) * n ≤ N := by exact_mod_cast hmode
    have hsquare := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 10 * n) hcast 2
    nlinarith
  simpa only [yoshidaDiagonalDyadicPairedCorrection] using
    diagonalDyadicCorrection_tail_sub_higherMainTail_abs_le
      hL.1 hL.2 hp hN hpN

/-! ## Rational interval API -/

def diagonalCoreCoeffThreeInterval (n : ℕ) : RatInterval :=
  let L := logTwoFineInterval
  let p := kappaSqInterval n
  (pure 0 - (pure 4 * L * p - L - pure 4)) / (pure 16 * L)

def diagonalCoreCoeffFourInterval (n : ℕ) : RatInterval :=
  let L := logTwoFineInterval
  let p := kappaSqInterval n
  (pure 12 * L * p - L + pure 24 * p - pure 6) / (pure 64 * L)

def diagonalCoreCoeffFiveInterval (n : ℕ) : RatInterval :=
  let L := logTwoFineInterval
  let p := kappaSqInterval n
  let p2 := p * p
  (pure 16 * L * p2 - pure 24 * L * p + L - pure 96 * p + pure 8) /
    (pure 256 * L)

private theorem interval_mul_lower_pos
    {I J : RatInterval} (hI : 0 < I.lower) (hJ : 0 < J.lower)
    (hIv : I.Valid) (hJv : J.Valid) :
    0 < (I * J).lower := by
  have hIu : 0 < I.upper := hI.trans_le hIv
  have hJu : 0 < J.upper := hJ.trans_le hJv
  change 0 < min (min (I.lower * J.lower) (I.lower * J.upper))
    (min (I.upper * J.lower) (I.upper * J.upper))
  simp only [lt_min_iff]
  exact ⟨⟨mul_pos hI hJ, mul_pos hI hJu⟩,
    ⟨mul_pos hIu hJ, mul_pos hIu hJu⟩⟩

private theorem coeffDenomSixteen_lower_pos :
    0 < (pure 16 * logTwoFineInterval).lower := by
  apply interval_mul_lower_pos
  · norm_num [RatInterval.pure]
  · norm_num [logTwoFineInterval]
  · exact valid_of_contains (contains_pure 16)
  · exact valid_of_contains logTwoFineInterval_contains

private theorem coeffDenomSixtyFour_lower_pos :
    0 < (pure 64 * logTwoFineInterval).lower := by
  apply interval_mul_lower_pos
  · norm_num [RatInterval.pure]
  · norm_num [logTwoFineInterval]
  · exact valid_of_contains (contains_pure 64)
  · exact valid_of_contains logTwoFineInterval_contains

private theorem coeffDenomTwoFiftySix_lower_pos :
    0 < (pure 256 * logTwoFineInterval).lower := by
  apply interval_mul_lower_pos
  · norm_num [RatInterval.pure]
  · norm_num [logTwoFineInterval]
  · exact valid_of_contains (contains_pure 256)
  · exact valid_of_contains logTwoFineInterval_contains

theorem diagonalCoreCoeffThreeInterval_contains (n : ℕ) :
    (diagonalCoreCoeffThreeInterval n).Contains
      (diagonalCoreCoeffThree yoshidaLength (yoshidaKappa n ^ 2)) := by
  have hL := logTwoFineInterval_contains
  have hp := kappaSqInterval_contains n
  have h4 : (pure (4 : ℚ)).Contains (4 : ℝ) := contains_pure 4
  have h16 : (pure (16 : ℚ)).Contains (16 : ℝ) := contains_pure 16
  unfold diagonalCoreCoeffThreeInterval diagonalCoreCoeffThree
  exact contains_div_of_pos coeffDenomSixteen_lower_pos
    (by
      have hz : (pure (0 : ℚ)).Contains (0 : ℝ) := by
        norm_num [Contains, RatInterval.pure]
      have hsub := contains_sub hz (contains_sub (contains_sub
        (contains_mul (contains_mul h4 hL) hp) hL) h4)
      convert hsub using 1
      ring)
    (contains_mul h16 hL)

theorem diagonalCoreCoeffFourInterval_contains (n : ℕ) :
    (diagonalCoreCoeffFourInterval n).Contains
      (diagonalCoreCoeffFour yoshidaLength (yoshidaKappa n ^ 2)) := by
  have hL := logTwoFineInterval_contains
  have hp := kappaSqInterval_contains n
  have h12 : (pure (12 : ℚ)).Contains (12 : ℝ) := contains_pure 12
  have h24 : (pure (24 : ℚ)).Contains (24 : ℝ) := contains_pure 24
  have h6 : (pure (6 : ℚ)).Contains (6 : ℝ) := contains_pure 6
  have h64 : (pure (64 : ℚ)).Contains (64 : ℝ) := contains_pure 64
  unfold diagonalCoreCoeffFourInterval diagonalCoreCoeffFour
  exact contains_div_of_pos coeffDenomSixtyFour_lower_pos
    (contains_sub (contains_add (contains_sub
      (contains_mul (contains_mul h12 hL) hp) hL)
      (contains_mul h24 hp)) h6)
    (contains_mul h64 hL)

theorem diagonalCoreCoeffFiveInterval_contains (n : ℕ) :
    (diagonalCoreCoeffFiveInterval n).Contains
      (diagonalCoreCoeffFive yoshidaLength (yoshidaKappa n ^ 2)) := by
  have hL := logTwoFineInterval_contains
  have hp := kappaSqInterval_contains n
  have hp2 : (kappaSqInterval n * kappaSqInterval n).Contains
      ((yoshidaKappa n ^ 2) ^ 2) := by
    convert contains_mul hp hp using 1
    ring
  have h16 : (pure (16 : ℚ)).Contains (16 : ℝ) := contains_pure 16
  have h24 : (pure (24 : ℚ)).Contains (24 : ℝ) := contains_pure 24
  have h96 : (pure (96 : ℚ)).Contains (96 : ℝ) := contains_pure 96
  have h8 : (pure (8 : ℚ)).Contains (8 : ℝ) := contains_pure 8
  have h256 : (pure (256 : ℚ)).Contains (256 : ℝ) := contains_pure 256
  unfold diagonalCoreCoeffFiveInterval diagonalCoreCoeffFive
  exact contains_div_of_pos coeffDenomTwoFiftySix_lower_pos
    (contains_add
      (contains_sub
        (contains_add
          (contains_sub
            (contains_mul (contains_mul h16 hL) hp2)
            (contains_mul (contains_mul h24 hL) hp)) hL)
        (contains_mul h96 hp)) h8)
    (contains_mul h256 hL)

def diagonalInvPowTailInterval (N s : ℕ) : RatInterval :=
  ⟨1 / ((s - 1 : ℕ) * (N : ℚ) ^ (s - 1)),
    1 / (N : ℚ) ^ s + 1 / ((s - 1 : ℕ) * (N : ℚ) ^ (s - 1))⟩

theorem diagonalInvPowTailInterval_contains
    {N s : ℕ} (hN : 1 ≤ N) (hs : s = 3 ∨ s = 4 ∨ s = 5) :
    (diagonalInvPowTailInterval N s).Contains
      (∑' j : ℕ, diagonalInvPow N s j) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h := diagonalInvPow_tsum_bounds hNR hs
  rcases hs with (rfl | rfl | rfl)
  all_goals
    norm_num [diagonalInvPowTailInterval, Contains,
      diagonalInvPowLowerPotential, diagonalInvPowUpperPotential,
      diagonalInvPow] at h ⊢
    exact h

def diagonalHigherMainTailInterval (n N : ℕ) : RatInterval :=
  diagonalCoreCoeffThreeInterval n * diagonalInvPowTailInterval N 3 +
    diagonalCoreCoeffFourInterval n * diagonalInvPowTailInterval N 4 +
    diagonalCoreCoeffFiveInterval n * diagonalInvPowTailInterval N 5

theorem diagonalHigherMainTailInterval_contains
    {n N : ℕ} (hN : 1 ≤ N) :
    (diagonalHigherMainTailInterval n N).Contains
      (diagonalHigherMainTail yoshidaLength (yoshidaKappa n ^ 2) N) := by
  unfold diagonalHigherMainTailInterval diagonalHigherMainTail
  exact contains_add
    (contains_add
      (contains_mul (diagonalCoreCoeffThreeInterval_contains n)
        (diagonalInvPowTailInterval_contains hN (Or.inl rfl)))
      (contains_mul (diagonalCoreCoeffFourInterval_contains n)
        (diagonalInvPowTailInterval_contains hN (Or.inr (Or.inl rfl)))))
    (contains_mul (diagonalCoreCoeffFiveInterval_contains n)
      (diagonalInvPowTailInterval_contains hN (Or.inr (Or.inr rfl))))

def diagonalHigherTailScaleInterval (n N : ℕ) : RatInterval :=
  let P := kappaSqInterval n + pure 1
  let P2 := P * P
  let P3 := P2 * P
  let P4 := P3 * P
  P2 / pure ((N : ℚ) ^ 3) + P3 / pure ((N : ℚ) ^ 4) +
    P3 / pure ((N : ℚ) ^ 5) + (P4 + pure 2) / pure ((N : ℚ) ^ 6)

def diagonalHigherResidualRadiusInterval (n N : ℕ) : RatInterval :=
  pure 11 * diagonalHigherTailScaleInterval n N /
    (pure 20 * pure ((N : ℚ) ^ 2))

theorem diagonalHigherResidualRadiusInterval_contains
    {n N : ℕ} (hN : 1 ≤ N) :
    (diagonalHigherResidualRadiusInterval n N).Contains
      (diagonalHigherResidualTailRadius (yoshidaKappa n ^ 2) N) := by
  have hp := kappaSqInterval_contains n
  have hone : (RatInterval.pure (1 : ℚ)).Contains (1 : ℝ) :=
    by norm_num [Contains, RatInterval.pure]
  have htwo : (RatInterval.pure (2 : ℚ)).Contains (2 : ℝ) :=
    by norm_num [Contains, RatInterval.pure]
  have h11 : (RatInterval.pure (11 : ℚ)).Contains (11 : ℝ) :=
    by norm_num [Contains, RatInterval.pure]
  have h20 : (RatInterval.pure (20 : ℚ)).Contains (20 : ℝ) :=
    by norm_num [Contains, RatInterval.pure]
  have hP := contains_add hp hone
  have hP2 := contains_mul hP hP
  have hP3 := contains_mul hP2 hP
  have hP4 := contains_mul hP3 hP
  have hP2' : ((kappaSqInterval n + RatInterval.pure 1) *
      (kappaSqInterval n + RatInterval.pure 1)).Contains
        ((yoshidaKappa n ^ 2 + 1) ^ 2) := by
    convert hP2 using 1
    ring
  have hP3' : ((kappaSqInterval n + RatInterval.pure 1) *
      (kappaSqInterval n + RatInterval.pure 1) *
        (kappaSqInterval n + RatInterval.pure 1)).Contains
        ((yoshidaKappa n ^ 2 + 1) ^ 3) := by
    convert hP3 using 1
    ring
  have hP4' : ((kappaSqInterval n + RatInterval.pure 1) *
      (kappaSqInterval n + RatInterval.pure 1) *
        (kappaSqInterval n + RatInterval.pure 1) *
        (kappaSqInterval n + RatInterval.pure 1)).Contains
          ((yoshidaKappa n ^ 2 + 1) ^ 4) := by
    convert hP4 using 1
    ring
  have hN3 : (RatInterval.pure ((N : ℚ) ^ 3)).Contains ((N : ℝ) ^ 3) := by
    norm_num [Contains, RatInterval.pure]
  have hN4 : (RatInterval.pure ((N : ℚ) ^ 4)).Contains ((N : ℝ) ^ 4) := by
    norm_num [Contains, RatInterval.pure]
  have hN5 : (RatInterval.pure ((N : ℚ) ^ 5)).Contains ((N : ℝ) ^ 5) := by
    norm_num [Contains, RatInterval.pure]
  have hN6 : (RatInterval.pure ((N : ℚ) ^ 6)).Contains ((N : ℝ) ^ 6) := by
    norm_num [Contains, RatInterval.pure]
  have hN2 : (RatInterval.pure ((N : ℚ) ^ 2)).Contains ((N : ℝ) ^ 2) := by
    norm_num [Contains, RatInterval.pure]
  have hN3pos : 0 < (N : ℚ) ^ 3 := by positivity
  have hN4pos : 0 < (N : ℚ) ^ 4 := by positivity
  have hN5pos : 0 < (N : ℚ) ^ 5 := by positivity
  have hN6pos : 0 < (N : ℚ) ^ 6 := by positivity
  have hscale : (diagonalHigherTailScaleInterval n N).Contains
      (diagonalHigherTailScale (yoshidaKappa n ^ 2) N) := by
    unfold diagonalHigherTailScaleInterval diagonalHigherTailScale
    exact contains_add
      (contains_add
        (contains_add
          (contains_div_of_pos hN3pos hP2' hN3)
          (contains_div_of_pos hN4pos hP3' hN4))
        (contains_div_of_pos hN5pos hP3' hN5))
      (contains_div_of_pos hN6pos (contains_add hP4' htwo) hN6)
  unfold diagonalHigherResidualRadiusInterval diagonalHigherResidualTailRadius
  exact contains_div_of_pos (by
      apply interval_mul_lower_pos
      · norm_num [RatInterval.pure]
      · norm_num [RatInterval.pure]
        positivity
      · exact valid_of_contains h20
      · exact valid_of_contains hN2)
    (contains_mul h11 hscale) (contains_mul h20 hN2)

def diagonalHigherTailInterval (n N : ℕ) : RatInterval :=
  let r := (diagonalHigherResidualRadiusInterval n N).upper
  diagonalHigherMainTailInterval n N + ⟨-r, r⟩

/-- Reusable rational enclosure for the exact production correction tail. -/
theorem diagonalHigherTailInterval_contains
    {n N : ℕ} (hN : 16 ≤ N) (hmode : 10 * n ≤ N) :
    (diagonalHigherTailInterval n N).Contains
      (∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)) := by
  have hmain := diagonalHigherMainTailInterval_contains (n := n) (by omega : 1 ≤ N)
  have hradI := diagonalHigherResidualRadiusInterval_contains
    (n := n) (by omega : 1 ≤ N)
  have herr := yoshidaDiagonalCorrection_tail_sub_higherMainTail_abs_le hN hmode
  let r : ℝ := ((diagonalHigherResidualRadiusInterval n N).upper : ℚ)
  have hradius : diagonalHigherResidualTailRadius (yoshidaKappa n ^ 2) N ≤ r :=
    hradI.2
  have he : -r ≤
      (∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)) -
        diagonalHigherMainTail yoshidaLength (yoshidaKappa n ^ 2) N ∧
      (∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)) -
        diagonalHigherMainTail yoshidaLength (yoshidaKappa n ^ 2) N ≤ r := by
    rw [abs_le] at herr
    constructor <;> linarith
  have heI : (⟨-(diagonalHigherResidualRadiusInterval n N).upper,
      (diagonalHigherResidualRadiusInterval n N).upper⟩ : RatInterval).Contains
        ((∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)) -
          diagonalHigherMainTail yoshidaLength (yoshidaKappa n ^ 2) N) := by
    simpa only [Contains, Rat.cast_neg] using he
  unfold diagonalHigherTailInterval
  have h := contains_add hmain heI
  convert h using 1
  ring

def diagonalHigherSeriesInterval (n N : ℕ) : RatInterval :=
  diagonalBaseInterval n - diagonalHeadInterval n (N - 1) -
    diagonalHigherTailInterval n N

/-- Full production moment enclosure using the exact finite head and the
higher-order infinite tail. -/
theorem diagonalHigherSeriesInterval_contains
    {n N : ℕ} (hn : n ≠ 0) (hN : 16 ≤ N) (hmode : 10 * n ≤ N) :
    (diagonalHigherSeriesInterval n N).Contains (yoshidaDiagonalMoment n) := by
  rw [yoshidaDiagonalMoment_eq_acceleratedSeries hn]
  rw [← diagonalCorrection_head_add_tail_eq_tsum
    (n := n) (N := N) hn (by omega)]
  have hbase := diagonalBaseInterval_contains_acceleratedBase n
  have hhead := diagonalHeadInterval_contains n (N - 1)
  have htail := diagonalHigherTailInterval_contains hN hmode
  unfold diagonalHigherSeriesInterval
  have hcombine := contains_sub (contains_sub hbase hhead) htail
  convert hcombine using 1
  ring

/-! ## Compiled cutoff regression

The old absolute-value tail at mode three needed `N = 18432` to fit its
production budget.  The higher-order tail below starts at `N = 512` and fits
inside a two-millionth-wide rational box. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem modeThreeHigherTail_512_kernel_certificate :
    IsSubinterval (diagonalHigherTailInterval 3 512)
      ⟨-352 / 1000000, -350 / 1000000⟩ := by
  decide +kernel

theorem modeThreeHigherTail_512_contains :
    (⟨-352 / 1000000, -350 / 1000000⟩ : RatInterval).Contains
      (∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection 3 (512 + j)) := by
  exact contains_of_subinterval modeThreeHigherTail_512_kernel_certificate
    (diagonalHigherTailInterval_contains (by norm_num) (by norm_num))

theorem modeThree_old_18432_tail_width_gt_four_millionths :
    (4 / 1000000 : ℚ) < 2 * diagonalTailRadius 3 18432 := by
  decide +kernel

theorem modeThree_higher_cutoff_reduction : (512 : ℕ) < 18432 := by
  norm_num
end

end ArithmeticHodge.Analysis.YoshidaDiagonalHigherAcceleration
