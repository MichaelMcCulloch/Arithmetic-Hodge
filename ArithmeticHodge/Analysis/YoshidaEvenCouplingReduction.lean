import ArithmeticHodge.Analysis.YoshidaEvenTailReduction

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.YoshidaEvenCouplingReduction

noncomputable section

open YoshidaEvenPairingBridge

/-!
# Yoshida even low/high coupling reduction

This module reduces the canonical even pointwise decay (6.26) to exactly two
source-specific analytic interfaces:

* equality of the actual removable-safe clipped pairing with the printed
  formula (6.25);
* the sharp digamma-imaginary remainder arising from source equation (5.11).

Everything after those interfaces is proved here.  In particular, the first
rational term and the infinite geometric term have their exact `C₂ / m`
bounds, the zero row uses the required `1 / sqrt 2` normalization, the first
row retains the sharp `1 / 12` remainder, and rows `n >= 2` close with the
standard `1 / 10` consequence.  The low block remains exactly modes
`0, ..., 199`, and every high mode is `200 + k`.

Neither analytic interface is inferred merely from the exact Laplace formula.
The digamma interface below is the simplified imaginary-mode consequence
still to be derived from the source's complex estimate; it is not asserted as
an automatic rewriting of that estimate.
-/

def doubledDenominator (a : ℝ) (n : ℕ) : ℝ :=
  1 + (2 * Real.pi * (n : ℝ) / a) ^ 2

def evenFirstKernel (a : ℝ) (n m : ℕ) : ℝ :=
  (4 / a) * (2 / (doubledDenominator a n * doubledDenominator a m))

/-- The first term in (6.25) already has the `1 / m` decay appearing in
(6.27), uniformly for `0 ≤ n < m`. -/
theorem abs_evenFirstKernel_le
    {a : ℝ} (ha : 0 < a) {n m : ℕ} (hnm : n < m) :
    |evenFirstKernel a n m| ≤
      (2 * a / Real.pi ^ 2) / (m : ℝ) := by
  have hmNat : 1 ≤ m := by omega
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hnm)
  have ha0 : a ≠ 0 := ha.ne'
  have hdn : 0 < doubledDenominator a n := by
    unfold doubledDenominator
    positivity
  have hdm : 0 < doubledDenominator a m := by
    unfold doubledDenominator
    positivity
  have hdmLower :
      (2 * Real.pi * (m : ℝ) / a) ^ 2 ≤ doubledDenominator a m := by
    unfold doubledDenominator
    linarith
  have hdnOne : 1 ≤ doubledDenominator a n := by
    unfold doubledDenominator
    nlinarith [sq_nonneg (2 * Real.pi * (n : ℝ) / a)]
  have hcore :
      4 * Real.pi ^ 2 * (m : ℝ) ≤
        a ^ 2 * doubledDenominator a n * doubledDenominator a m := by
    have hmOne : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmNat
    have hsq :
        4 * Real.pi ^ 2 * (m : ℝ) ^ 2 ≤
          a ^ 2 * doubledDenominator a m := by
      have haSq : 0 < a ^ 2 := sq_pos_of_pos ha
      have h := mul_le_mul_of_nonneg_left hdmLower haSq.le
      field_simp [ha0] at h
      nlinarith
    calc
      4 * Real.pi ^ 2 * (m : ℝ) ≤
          4 * Real.pi ^ 2 * (m : ℝ) ^ 2 := by
        have hp4 : 0 ≤ 4 * Real.pi ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left (by nlinarith) hp4
      _ ≤ a ^ 2 * doubledDenominator a m := hsq
      _ ≤ a ^ 2 * doubledDenominator a n * doubledDenominator a m := by
        have hleft : a ^ 2 ≤ a ^ 2 * doubledDenominator a n := by
          nlinarith [sq_nonneg a,
            mul_le_mul_of_nonneg_left hdnOne (sq_nonneg a)]
        exact mul_le_mul_of_nonneg_right hleft hdm.le
  unfold evenFirstKernel
  rw [abs_of_nonneg (by positivity)]
  rw [show (4 / a) *
      (2 / (doubledDenominator a n * doubledDenominator a m)) =
      8 / (a * doubledDenominator a n * doubledDenominator a m) by ring]
  rw [show (2 * a / Real.pi ^ 2) / (m : ℝ) =
      2 * a / (Real.pi ^ 2 * (m : ℝ)) by ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

def halfOdd (k : ℕ) : ℝ := 2 * (k : ℝ) + 1 / 2

def archDenominator (a : ℝ) (k n : ℕ) : ℝ :=
  halfOdd k ^ 2 + (Real.pi * (n : ℝ) / a) ^ 2

def evenGeometricTerm (a : ℝ) (n m k : ℕ) : ℝ :=
  halfOdd k ^ 2 * Real.exp (-2 * a * halfOdd k) /
    (archDenominator a k n * archDenominator a k m)

theorem evenGeometricTerm_nonneg
    (a : ℝ) (n m k : ℕ) :
    0 ≤ evenGeometricTerm a n m k := by
  unfold evenGeometricTerm archDenominator halfOdd
  positivity

/-- Each geometric summand in (6.25) is bounded by the geometric numerator
times `a²/(pi² m²)`. -/
theorem evenGeometricTerm_le
    {a : ℝ} (ha : 0 < a) (n : ℕ) {m : ℕ} (hm : 0 < m) (k : ℕ) :
    evenGeometricTerm a n m k ≤
      (a ^ 2 / (Real.pi ^ 2 * (m : ℝ) ^ 2)) *
        Real.exp (-2 * a * halfOdd k) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hq : 0 < halfOdd k := by
    unfold halfOdd
    positivity
  have hdn : 0 < archDenominator a k n := by
    unfold archDenominator
    positivity
  have hdm : 0 < archDenominator a k m := by
    unfold archDenominator
    positivity
  have hqFrac : halfOdd k ^ 2 / archDenominator a k n ≤ 1 := by
    rw [div_le_one hdn]
    unfold archDenominator
    nlinarith [sq_nonneg (Real.pi * (n : ℝ) / a)]
  have hmFrac : 1 / archDenominator a k m ≤
      a ^ 2 / (Real.pi ^ 2 * (m : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ hdm (by positivity)]
    unfold archDenominator
    have hsquare :
        a ^ 2 * (Real.pi * (m : ℝ) / a) ^ 2 =
          Real.pi ^ 2 * (m : ℝ) ^ 2 := by
      field_simp [ha0]
    rw [mul_add, hsquare]
    nlinarith [sq_nonneg a, sq_nonneg (halfOdd k)]
  have he : 0 ≤ Real.exp (-2 * a * halfOdd k) := (Real.exp_pos _).le
  unfold evenGeometricTerm
  rw [show
      halfOdd k ^ 2 * Real.exp (-2 * a * halfOdd k) /
          (archDenominator a k n * archDenominator a k m) =
        (halfOdd k ^ 2 / archDenominator a k n) *
          (1 / archDenominator a k m) *
            Real.exp (-2 * a * halfOdd k) by
    field_simp [hdn.ne', hdm.ne']]
  apply mul_le_mul_of_nonneg_right _ he
  calc
    (halfOdd k ^ 2 / archDenominator a k n) *
        (1 / archDenominator a k m) ≤
      1 * (1 / archDenominator a k m) :=
        mul_le_mul_of_nonneg_right hqFrac (by positivity)
    _ ≤ 1 * (a ^ 2 / (Real.pi ^ 2 * (m : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hmFrac (by norm_num)
    _ = a ^ 2 / (Real.pi ^ 2 * (m : ℝ) ^ 2) := one_mul _

theorem exp_halfOdd_eq_geometric
    {a : ℝ} (k : ℕ) :
    Real.exp (-2 * a * halfOdd k) =
      Real.exp (-a) * (Real.exp (-4 * a)) ^ k := by
  rw [← Real.exp_nat_mul]
  rw [← Real.exp_add]
  congr 1
  unfold halfOdd
  ring

theorem summable_exp_halfOdd {a : ℝ} (ha : 0 < a) :
    Summable (fun k : ℕ ↦ Real.exp (-2 * a * halfOdd k)) := by
  have hr : ‖Real.exp (-4 * a)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hs := (summable_geometric_of_norm_lt_one hr).mul_left (Real.exp (-a))
  exact hs.congr fun k ↦ (exp_halfOdd_eq_geometric k).symm

theorem tsum_exp_halfOdd {a : ℝ} (ha : 0 < a) :
    (∑' k : ℕ, Real.exp (-2 * a * halfOdd k)) =
      Real.exp (-a) / (1 - Real.exp (-4 * a)) := by
  have hr : ‖Real.exp (-4 * a)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  calc
    (∑' k : ℕ, Real.exp (-2 * a * halfOdd k)) =
        ∑' k : ℕ, Real.exp (-a) * (Real.exp (-4 * a)) ^ k := by
      apply tsum_congr
      exact exp_halfOdd_eq_geometric
    _ = Real.exp (-a) *
        (∑' k : ℕ, (Real.exp (-4 * a)) ^ k) := tsum_mul_left
    _ = Real.exp (-a) * (1 - Real.exp (-4 * a))⁻¹ := by
      rw [tsum_geometric_of_norm_lt_one hr]
    _ = Real.exp (-a) / (1 - Real.exp (-4 * a)) := by
      rw [div_eq_mul_inv]

def evenGeometricKernel (a : ℝ) (n m : ℕ) : ℝ :=
  (2 / a) * ∑' k : ℕ, evenGeometricTerm a n m k

/-- The geometric-series term of (6.25) has the second `C₂/m` bound from
(6.27). -/
theorem evenGeometricKernel_le
    {a : ℝ} (ha : 0 < a) {n m : ℕ} (hnm : n < m) :
    evenGeometricKernel a n m ≤
      ((2 * a / Real.pi ^ 2) *
        (Real.exp (-a) / (1 - Real.exp (-4 * a)))) / (m : ℝ) := by
  have hm : 0 < m := Nat.zero_lt_of_lt hnm
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmOne : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hterms : Summable (fun k : ℕ ↦ evenGeometricTerm a n m k) := by
    have hmajor := (summable_exp_halfOdd ha).mul_left
      (a ^ 2 / (Real.pi ^ 2 * (m : ℝ) ^ 2))
    exact hmajor.of_nonneg_of_le
      (evenGeometricTerm_nonneg a n m)
      (evenGeometricTerm_le ha n hm)
  have hmajor := (summable_exp_halfOdd ha).mul_left
    (a ^ 2 / (Real.pi ^ 2 * (m : ℝ) ^ 2))
  have hsum := hterms.tsum_le_tsum (evenGeometricTerm_le ha n hm) hmajor
  unfold evenGeometricKernel
  calc
    (2 / a) * ∑' k : ℕ, evenGeometricTerm a n m k ≤
        (2 / a) * ∑' k : ℕ,
          (a ^ 2 / (Real.pi ^ 2 * (m : ℝ) ^ 2)) *
            Real.exp (-2 * a * halfOdd k) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2 / a) *
        ((a ^ 2 / (Real.pi ^ 2 * (m : ℝ) ^ 2)) *
          (Real.exp (-a) / (1 - Real.exp (-4 * a)))) := by
      rw [tsum_mul_left, tsum_exp_halfOdd ha]
    _ ≤ ((2 * a / Real.pi ^ 2) *
          (Real.exp (-a) / (1 - Real.exp (-4 * a)))) / (m : ℝ) := by
      have hgeom : 0 ≤ Real.exp (-a) / (1 - Real.exp (-4 * a)) := by
        have : Real.exp (-4 * a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
        exact div_nonneg (Real.exp_pos _).le (sub_nonneg.mpr this.le)
      field_simp [ha.ne', ne_of_gt hmR, Real.pi_ne_zero]
      nlinarith

def digammaErrorWeight (n m : ℕ) : ℝ :=
  (1 / (n : ℝ) ^ 2 + 1 / (m : ℝ) ^ 2) / 2 *
    (1 / ((m : ℝ) - n) + 1 / ((m : ℝ) + n))

/-- Independent absolute-value bounds for the two digamma remainders fit
the exact `(6.27)` error budget as soon as the low frequency is at least two.
The exceptional frequency `n = 1` needs either the sign of the remainder or
the sharper pre-weakened `1/12` estimate from (5.11). -/
theorem digammaErrorWeight_le_inv
    {n m : ℕ} (hn : 2 ≤ n) (hnm : n < m) :
    digammaErrorWeight n m ≤ 1 / (m : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hn)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hnm)
  have hnmlt : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hdiff : (0 : ℝ) < (m : ℝ) - n := sub_pos.mpr hnmlt
  have hsum : (0 : ℝ) < (m : ℝ) + n := by positivity
  have hsqdiff : (0 : ℝ) < (m : ℝ) ^ 2 - (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((m : ℝ) - n)]
  have hnTwo : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hstep : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hnm
  unfold digammaErrorWeight
  rw [show
      (1 / (n : ℝ) ^ 2 + 1 / (m : ℝ) ^ 2) / 2 *
          (1 / ((m : ℝ) - n) + 1 / ((m : ℝ) + n)) =
        (((m : ℝ) ^ 2 + (n : ℝ) ^ 2) * (m : ℝ)) /
          ((n : ℝ) ^ 2 * (m : ℝ) ^ 2 *
            ((m : ℝ) ^ 2 - (n : ℝ) ^ 2)) by
    field_simp [hnR.ne', hmR.ne', hdiff.ne', hsum.ne', hsqdiff.ne']
    ring]
  rw [div_le_div_iff₀
    (mul_pos (mul_pos (sq_pos_of_pos hnR) (sq_pos_of_pos hmR)) hsqdiff) hmR]
  have hsquareStep : ((n : ℝ) + 1) ^ 2 ≤ (m : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hstep 2
  have hpoly :
      (m : ℝ) ^ 2 + (n : ℝ) ^ 2 ≤
        (n : ℝ) ^ 2 * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2) := by
    nlinarith [sq_nonneg ((n : ℝ) - 2),
      mul_nonneg (sq_nonneg ((n : ℝ)))
        (sub_nonneg.mpr hsquareStep)]
  have hposFactor : 0 ≤ (n : ℝ) ^ 2 * (m : ℝ) ^ 2 := by positivity
  nlinarith

/-- The naive independent-remainder estimate misses the exact budget at the
first possible pair by the rational factor `40001 / 39999`. -/
theorem digammaErrorWeight_one_twoHundred :
    digammaErrorWeight 1 200 =
      (40001 / 39999 : ℝ) * (1 / 200 : ℝ) := by
  norm_num [digammaErrorWeight]

theorem digammaErrorWeight_one_twoHundred_exceeds_inv :
    (1 / 200 : ℝ) < digammaErrorWeight 1 200 := by
  rw [digammaErrorWeight_one_twoHundred]
  norm_num

/-- Retaining the `1/12` remainder of source (5.11), instead of first
weakening it to `1/10`, supplies enough margin for the exceptional `n = 1`
row. -/
theorem five_six_mul_digammaErrorWeight_one_le_inv
    {m : ℕ} (hm : 4 ≤ m) :
    (5 / 6 : ℝ) * digammaErrorWeight 1 m ≤ 1 / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hm)
  have hmOne : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hm)
  have hdiff : (0 : ℝ) < (m : ℝ) ^ 2 - 1 := by nlinarith
  rw [show digammaErrorWeight 1 m =
      ((m : ℝ) ^ 2 + 1) / ((m : ℝ) * ((m : ℝ) ^ 2 - 1)) by
    unfold digammaErrorWeight
    field_simp [hmR.ne', (sub_pos.mpr hmOne).ne', (by positivity : (m : ℝ) + 1 ≠ 0)]
    ring]
  rw [le_div_iff₀ hmR]
  rw [show (5 / 6 : ℝ) *
      (((m : ℝ) ^ 2 + 1) / ((m : ℝ) * ((m : ℝ) ^ 2 - 1))) * (m : ℝ) =
      (5 / 6 : ℝ) * (((m : ℝ) ^ 2 + 1) / ((m : ℝ) ^ 2 - 1)) by
    field_simp [hmR.ne', hdiff.ne']]
  rw [show (5 / 6 : ℝ) * (((m : ℝ) ^ 2 + 1) / ((m : ℝ) ^ 2 - 1)) =
      ((5 / 6 : ℝ) * ((m : ℝ) ^ 2 + 1)) / ((m : ℝ) ^ 2 - 1) by ring]
  rw [div_le_iff₀ hdiff]
  have hmFour : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmSq : (16 : ℝ) ≤ (m : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((m : ℝ) - 4)]
  linarith

def digammaAsymptoticMain (a : ℝ) (j : ℕ) : ℝ :=
  Real.pi / 2 + a / (2 * Real.pi * (j : ℝ))

def evenDigammaCombination
    (y : ℕ → ℝ) (n m : ℕ) : ℝ :=
  (y n - y m) / (2 * Real.pi * ((n : ℝ) - m)) +
    (y n + y m) / (2 * Real.pi * ((n : ℝ) + m))

/-- Apart from the exceptional zero and first modes, Yoshida's `1/(10t²)`
digamma remainder estimate gives exactly the third `C₂/m` contribution in
(6.27). -/
theorem abs_evenDigammaCombination_le_of_remainders
    {a : ℝ} (ha : 0 < a) (y : ℕ → ℝ) {n m : ℕ}
    (hn : 2 ≤ n) (hnm : n < m)
    (hnRem : |y n - digammaAsymptoticMain a n| ≤
      (2 * a) ^ 2 / (10 * Real.pi ^ 2 * (n : ℝ) ^ 2))
    (hmRem : |y m - digammaAsymptoticMain a m| ≤
      (2 * a) ^ 2 / (10 * Real.pi ^ 2 * (m : ℝ) ^ 2)) :
    |evenDigammaCombination y n m| ≤
      (1 / 2 + (2 * a) ^ 2 / (10 * Real.pi ^ 3)) / (m : ℝ) := by
  let c : ℝ := (2 * a) ^ 2 / (10 * Real.pi ^ 2)
  let en : ℝ := y n - digammaAsymptoticMain a n
  let em : ℝ := y m - digammaAsymptoticMain a m
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) hn)
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hnm)
  have hnmlt : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hdiff : (0 : ℝ) < (m : ℝ) - n := sub_pos.mpr hnmlt
  have hsum : (0 : ℝ) < (n : ℝ) + m := by positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hen : |en| ≤ c / (n : ℝ) ^ 2 := by
    dsimp [en, c]
    convert hnRem using 1
    all_goals ring
  have hem : |em| ≤ c / (m : ℝ) ^ 2 := by
    dsimp [em, c]
    convert hmRem using 1
    all_goals ring
  have hidentity : evenDigammaCombination y n m =
      1 / (2 * ((n : ℝ) + m)) +
        (en - em) / (2 * Real.pi * ((n : ℝ) - m)) +
        (en + em) / (2 * Real.pi * ((n : ℝ) + m)) := by
    unfold evenDigammaCombination
    dsimp [en, em, digammaAsymptoticMain]
    field_simp [hnR.ne', hmR.ne', sub_ne_zero.mpr hnmlt.ne,
      (ne_of_gt hsum), Real.pi_ne_zero]
    ring
  rw [hidentity]
  calc
    |1 / (2 * ((n : ℝ) + m)) +
          (en - em) / (2 * Real.pi * ((n : ℝ) - m)) +
          (en + em) / (2 * Real.pi * ((n : ℝ) + m))| ≤
        1 / (2 * ((n : ℝ) + m)) +
          |(en - em) / (2 * Real.pi * ((n : ℝ) - m))| +
          |(en + em) / (2 * Real.pi * ((n : ℝ) + m))| := by
      have hbase : 0 ≤ 1 / (2 * ((n : ℝ) + m)) := by positivity
      calc
        |_ + _ + _| ≤ |1 / (2 * ((n : ℝ) + m))| +
            |(en - em) / (2 * Real.pi * ((n : ℝ) - m))| +
            |(en + em) / (2 * Real.pi * ((n : ℝ) + m))| := by
          exact abs_add_three _ _ _
        _ = _ := by rw [abs_of_nonneg hbase]
    _ ≤ 1 / (2 * (m : ℝ)) +
        (c / Real.pi) * digammaErrorWeight n m := by
      have hbase : 1 / (2 * ((n : ℝ) + m)) ≤ 1 / (2 * (m : ℝ)) := by
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      have hfirst :
          |(en - em) / (2 * Real.pi * ((n : ℝ) - m))| ≤
            (|en| + |em|) / (2 * Real.pi * ((m : ℝ) - n)) := by
        rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos Real.pi_pos, abs_sub_comm (n : ℝ) m,
          abs_of_pos hdiff]
        exact div_le_div_of_nonneg_right (abs_sub en em) (by positivity)
      have hsecond :
          |(en + em) / (2 * Real.pi * ((n : ℝ) + m))| ≤
            (|en| + |em|) / (2 * Real.pi * ((n : ℝ) + m)) := by
        rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos Real.pi_pos, abs_of_pos hsum]
        exact div_le_div_of_nonneg_right (abs_add_le en em) (by positivity)
      have herr : |en| + |em| ≤
          c * (1 / (n : ℝ) ^ 2 + 1 / (m : ℝ) ^ 2) := by
        calc
          |en| + |em| ≤ c / (n : ℝ) ^ 2 + c / (m : ℝ) ^ 2 :=
            add_le_add hen hem
          _ = _ := by ring
      calc
        1 / (2 * ((n : ℝ) + m)) +
            |(en - em) / (2 * Real.pi * ((n : ℝ) - m))| +
            |(en + em) / (2 * Real.pi * ((n : ℝ) + m))| ≤
          1 / (2 * (m : ℝ)) +
            (|en| + |em|) / (2 * Real.pi * ((m : ℝ) - n)) +
            (|en| + |em|) / (2 * Real.pi * ((n : ℝ) + m)) := by
          linarith
        _ ≤ 1 / (2 * (m : ℝ)) +
            (c * (1 / (n : ℝ) ^ 2 + 1 / (m : ℝ) ^ 2)) /
              (2 * Real.pi * ((m : ℝ) - n)) +
            (c * (1 / (n : ℝ) ^ 2 + 1 / (m : ℝ) ^ 2)) /
              (2 * Real.pi * ((n : ℝ) + m)) := by
          gcongr
        _ = 1 / (2 * (m : ℝ)) +
            (c / Real.pi) * digammaErrorWeight n m := by
          unfold digammaErrorWeight
          field_simp [Real.pi_ne_zero, hdiff.ne', hsum.ne']
          ring
    _ ≤ 1 / (2 * (m : ℝ)) + (c / Real.pi) * (1 / (m : ℝ)) := by
      have hcpi : 0 ≤ c / Real.pi := div_nonneg hc Real.pi_pos.le
      have h := mul_le_mul_of_nonneg_left
        (digammaErrorWeight_le_inv hn hnm) hcpi
      linarith
    _ = (1 / 2 + (2 * a) ^ 2 / (10 * Real.pi ^ 3)) / (m : ℝ) := by
      dsimp [c]
      field_simp [ne_of_gt hmR, Real.pi_ne_zero]

/-- Generic algebraic reduction of the two digamma remainders. -/
theorem abs_evenDigammaCombination_le_errorWeight
    {a c : ℝ} (y : ℕ → ℝ) {n m : ℕ}
    (hn : 0 < n) (hnm : n < m)
    (hnRem : |y n - digammaAsymptoticMain a n| ≤ c / (n : ℝ) ^ 2)
    (hmRem : |y m - digammaAsymptoticMain a m| ≤ c / (m : ℝ) ^ 2) :
    |evenDigammaCombination y n m| ≤
      1 / (2 * (m : ℝ)) + (c / Real.pi) * digammaErrorWeight n m := by
  let en : ℝ := y n - digammaAsymptoticMain a n
  let em : ℝ := y m - digammaAsymptoticMain a m
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hnm)
  have hnmlt : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hdiff : (0 : ℝ) < (m : ℝ) - n := sub_pos.mpr hnmlt
  have hsum : (0 : ℝ) < (n : ℝ) + m := by positivity
  have hen : |en| ≤ c / (n : ℝ) ^ 2 := by simpa [en] using hnRem
  have hem : |em| ≤ c / (m : ℝ) ^ 2 := by simpa [em] using hmRem
  have hidentity : evenDigammaCombination y n m =
      1 / (2 * ((n : ℝ) + m)) +
        (en - em) / (2 * Real.pi * ((n : ℝ) - m)) +
        (en + em) / (2 * Real.pi * ((n : ℝ) + m)) := by
    unfold evenDigammaCombination
    dsimp [en, em, digammaAsymptoticMain]
    field_simp [hnR.ne', hmR.ne', sub_ne_zero.mpr hnmlt.ne,
      (ne_of_gt hsum), Real.pi_ne_zero]
    ring
  rw [hidentity]
  calc
    |1 / (2 * ((n : ℝ) + m)) +
          (en - em) / (2 * Real.pi * ((n : ℝ) - m)) +
          (en + em) / (2 * Real.pi * ((n : ℝ) + m))| ≤
        1 / (2 * ((n : ℝ) + m)) +
          |(en - em) / (2 * Real.pi * ((n : ℝ) - m))| +
          |(en + em) / (2 * Real.pi * ((n : ℝ) + m))| := by
      have hbase : 0 ≤ 1 / (2 * ((n : ℝ) + m)) := by positivity
      calc
        |_ + _ + _| ≤ |1 / (2 * ((n : ℝ) + m))| +
            |(en - em) / (2 * Real.pi * ((n : ℝ) - m))| +
            |(en + em) / (2 * Real.pi * ((n : ℝ) + m))| :=
          abs_add_three _ _ _
        _ = _ := by rw [abs_of_nonneg hbase]
    _ ≤ 1 / (2 * (m : ℝ)) +
        (c / Real.pi) * digammaErrorWeight n m := by
      have hbase : 1 / (2 * ((n : ℝ) + m)) ≤ 1 / (2 * (m : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have hfirst :
          |(en - em) / (2 * Real.pi * ((n : ℝ) - m))| ≤
            (|en| + |em|) / (2 * Real.pi * ((m : ℝ) - n)) := by
        rw [abs_div, abs_mul, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos,
          abs_sub_comm (n : ℝ) m, abs_of_pos hdiff]
        exact div_le_div_of_nonneg_right (abs_sub en em) (by positivity)
      have hsecond :
          |(en + em) / (2 * Real.pi * ((n : ℝ) + m))| ≤
            (|en| + |em|) / (2 * Real.pi * ((n : ℝ) + m)) := by
        rw [abs_div, abs_mul, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos,
          abs_of_pos hsum]
        exact div_le_div_of_nonneg_right (abs_add_le en em) (by positivity)
      have herr : |en| + |em| ≤
          c * (1 / (n : ℝ) ^ 2 + 1 / (m : ℝ) ^ 2) := by
        calc
          |en| + |em| ≤ c / (n : ℝ) ^ 2 + c / (m : ℝ) ^ 2 :=
            add_le_add hen hem
          _ = _ := by ring
      calc
        1 / (2 * ((n : ℝ) + m)) +
            |(en - em) / (2 * Real.pi * ((n : ℝ) - m))| +
            |(en + em) / (2 * Real.pi * ((n : ℝ) + m))| ≤
          1 / (2 * (m : ℝ)) +
            (|en| + |em|) / (2 * Real.pi * ((m : ℝ) - n)) +
            (|en| + |em|) / (2 * Real.pi * ((n : ℝ) + m)) := by
          linarith
        _ ≤ 1 / (2 * (m : ℝ)) +
            (c * (1 / (n : ℝ) ^ 2 + 1 / (m : ℝ) ^ 2)) /
              (2 * Real.pi * ((m : ℝ) - n)) +
            (c * (1 / (n : ℝ) ^ 2 + 1 / (m : ℝ) ^ 2)) /
              (2 * Real.pi * ((n : ℝ) + m)) := by
          gcongr
        _ = 1 / (2 * (m : ℝ)) +
            (c / Real.pi) * digammaErrorWeight n m := by
          unfold digammaErrorWeight
          field_simp [Real.pi_ne_zero, hdiff.ne', hsum.ne']
          ring

/-- The first positive even frequency closes with the sharp `1/12`
remainder before the source's later `1/10` weakening. -/
theorem abs_evenDigammaCombination_one_le_of_sharp_remainders
    {a : ℝ} (ha : 0 < a) (y : ℕ → ℝ) {m : ℕ} (hm : 4 ≤ m)
    (hOne : |y 1 - digammaAsymptoticMain a 1| ≤
      (2 * a) ^ 2 / (12 * Real.pi ^ 2))
    (hmRem : |y m - digammaAsymptoticMain a m| ≤
      (2 * a) ^ 2 / (12 * Real.pi ^ 2 * (m : ℝ) ^ 2)) :
    |evenDigammaCombination y 1 m| ≤
      (1 / 2 + (2 * a) ^ 2 / (10 * Real.pi ^ 3)) / (m : ℝ) := by
  let c12 : ℝ := (2 * a) ^ 2 / (12 * Real.pi ^ 2)
  let c10 : ℝ := (2 * a) ^ 2 / (10 * Real.pi ^ 2)
  have hOne' : |y 1 - digammaAsymptoticMain a 1| ≤
      c12 / (((1 : ℕ) : ℝ) ^ 2) := by
    simpa [c12]
  have hmRem' : |y m - digammaAsymptoticMain a m| ≤ c12 / (m : ℝ) ^ 2 := by
    dsimp [c12]
    convert hmRem using 1
    all_goals ring
  have hgeneric := abs_evenDigammaCombination_le_errorWeight
    y (by norm_num : 0 < 1) (by omega : 1 < m) hOne' hmRem'
  have hweight := five_six_mul_digammaErrorWeight_one_le_inv hm
  have hc10pi : 0 ≤ c10 / Real.pi := by dsimp [c10]; positivity
  have herr : (c12 / Real.pi) * digammaErrorWeight 1 m ≤
      (c10 / Real.pi) * (1 / (m : ℝ)) := by
    have hscaled := mul_le_mul_of_nonneg_left hweight hc10pi
    convert hscaled using 1
    all_goals
      dsimp [c12, c10]
      ring
  calc
    |evenDigammaCombination y 1 m| ≤
        1 / (2 * (m : ℝ)) +
          (c12 / Real.pi) * digammaErrorWeight 1 m := hgeneric
    _ ≤ 1 / (2 * (m : ℝ)) + (c10 / Real.pi) * (1 / (m : ℝ)) :=
      by linarith
    _ = (1 / 2 + (2 * a) ^ 2 / (10 * Real.pi ^ 3)) / (m : ℝ) := by
      dsimp [c10]
      field_simp [Real.pi_ne_zero]

/-- The normalized zero-mode clause after (6.25) has ample room: the
`1/sqrt 2` factor makes the digamma contribution alone smaller than
`1/(2m)` once `m ≥ 200`. -/
theorem zero_mode_digamma_contribution_le
    (y : ℕ → ℝ) {m : ℕ} (hm : 200 ≤ m)
    (hmRem :
      |y m - digammaAsymptoticMain
          YoshidaWeightedTailBounds.yoshidaA m| ≤
        (2 * YoshidaWeightedTailBounds.yoshidaA) ^ 2 /
          (10 * Real.pi ^ 2 * (m : ℝ) ^ 2)) :
    (Real.sqrt 2)⁻¹ * |y m| / (Real.pi * (m : ℝ)) ≤
      1 / (2 * (m : ℝ)) := by
  let a : ℝ := YoshidaWeightedTailBounds.yoshidaA
  let c : ℝ := (2 * a) ^ 2 / (10 * Real.pi ^ 2)
  have ha : 0 < a := YoshidaCoercivityNumerics.yoshidaA_pos
  have haOne : a ≤ 1 := by
    dsimp [a, YoshidaWeightedTailBounds.yoshidaA]
    linarith [Real.log_two_lt_d9]
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hm)
  have hmFour : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_trans (by omega) hm)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcOne : c ≤ 1 := by
    dsimp [c]
    have hpiSq : (9 : ℝ) < Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    rw [div_le_iff₀ (by positivity : 0 < 10 * Real.pi ^ 2)]
    nlinarith [sq_nonneg (2 * a),
      mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 2 * a)
        (by linarith : 2 * a ≤ 2)]
  have hsqrt : (7 / 5 : ℝ) < Real.sqrt 2 := by
    have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hinvSqrt : (Real.sqrt 2)⁻¹ ≤ (5 / 7 : ℝ) := by
    rw [inv_le_comm₀ (Real.sqrt_pos.2 (by norm_num)) (by norm_num : (0 : ℝ) < 5 / 7)]
    norm_num
    nlinarith
  have hrem : |y m - digammaAsymptoticMain a m| ≤ c / (m : ℝ) ^ 2 := by
    dsimp [a, c]
    convert hmRem using 1
    all_goals ring
  have hmain : 0 ≤ digammaAsymptoticMain a m := by
    unfold digammaAsymptoticMain
    positivity
  have hy : |y m| ≤ digammaAsymptoticMain a m + c / (m : ℝ) ^ 2 := by
    calc
      |y m| = |(y m - digammaAsymptoticMain a m) +
          digammaAsymptoticMain a m| := by ring_nf
      _ ≤ |y m - digammaAsymptoticMain a m| +
          |digammaAsymptoticMain a m| := abs_add_le _ _
      _ = |y m - digammaAsymptoticMain a m| +
          digammaAsymptoticMain a m := by rw [abs_of_nonneg hmain]
      _ ≤ _ := by linarith
  have hbracket :
      digammaAsymptoticMain a m + c / (m : ℝ) ^ 2 ≤
        (7 / 10 : ℝ) * Real.pi := by
    unfold digammaAsymptoticMain
    have htermA : a / (2 * Real.pi * (m : ℝ)) ≤ 1 / 24 := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi * (m : ℝ))]
      nlinarith [Real.pi_gt_three]
    have hmSq : (16 : ℝ) ≤ (m : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((m : ℝ) - 4)]
    have htermC : c / (m : ℝ) ^ 2 ≤ 1 / 16 := by
      rw [div_le_iff₀ (sq_pos_of_pos hmR)]
      nlinarith
    nlinarith [Real.pi_gt_three]
  have hscaled :
      (Real.sqrt 2)⁻¹ * |y m| / Real.pi ≤ 1 / 2 := by
    have hnonneg : 0 ≤ digammaAsymptoticMain a m + c / (m : ℝ) ^ 2 :=
      add_nonneg hmain (by positivity)
    calc
      (Real.sqrt 2)⁻¹ * |y m| / Real.pi ≤
          (Real.sqrt 2)⁻¹ *
            (digammaAsymptoticMain a m + c / (m : ℝ) ^ 2) / Real.pi := by
        gcongr
      _ ≤ (5 / 7 : ℝ) * ((7 / 10 : ℝ) * Real.pi) / Real.pi := by
        gcongr
      _ = 1 / 2 := by
        field_simp [Real.pi_ne_zero]
        norm_num
  calc
    (Real.sqrt 2)⁻¹ * |y m| / (Real.pi * (m : ℝ)) =
        ((Real.sqrt 2)⁻¹ * |y m| / Real.pi) / (m : ℝ) := by ring
    _ ≤ (1 / 2) / (m : ℝ) :=
      div_le_div_of_nonneg_right hscaled hmR.le
    _ = 1 / (2 * (m : ℝ)) := by ring

def even625BaseRhs (a : ℝ) (y : ℕ → ℝ) (n m : ℕ) : ℝ :=
  (Real.exp (a / 2) - Real.exp (-a / 2)) ^ 2 *
      evenFirstKernel a n m -
    evenGeometricKernel a n m +
    evenDigammaCombination y n m

def evenDecayConstant (a : ℝ) : ℝ :=
  (2 * a / Real.pi ^ 2) *
      (Real.exp (a / 2) - Real.exp (-a / 2)) ^ 2 +
    (2 * a / Real.pi ^ 2) *
      (Real.exp (-a) / (1 - Real.exp (-4 * a))) +
    (1 / 2 + (2 * a) ^ 2 / (10 * Real.pi ^ 3))

/-- Assembly of (6.26) once the digamma component has its allocated bound. -/
theorem abs_even625BaseRhs_le_of_digamma_bound
    {a : ℝ} (ha : 0 < a) (y : ℕ → ℝ) {n m : ℕ} (hnm : n < m)
    (hdigamma : |evenDigammaCombination y n m| ≤
      (1 / 2 + (2 * a) ^ 2 / (10 * Real.pi ^ 3)) / (m : ℝ)) :
    |even625BaseRhs a y n m| ≤ evenDecayConstant a / (m : ℝ) := by
  let deltaSq : ℝ :=
    (Real.exp (a / 2) - Real.exp (-a / 2)) ^ 2
  have hdelta : 0 ≤ deltaSq := sq_nonneg _
  have hfirst :
      |deltaSq * evenFirstKernel a n m| ≤
        ((2 * a / Real.pi ^ 2) * deltaSq) / (m : ℝ) := by
    rw [abs_mul, abs_of_nonneg hdelta]
    calc
      deltaSq * |evenFirstKernel a n m| ≤
          deltaSq * ((2 * a / Real.pi ^ 2) / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left (abs_evenFirstKernel_le ha hnm) hdelta
      _ = ((2 * a / Real.pi ^ 2) * deltaSq) / (m : ℝ) := by ring
  have hgeomNonneg : 0 ≤ evenGeometricKernel a n m := by
    unfold evenGeometricKernel
    exact mul_nonneg (by positivity)
      (tsum_nonneg (evenGeometricTerm_nonneg a n m))
  have hgeom : |evenGeometricKernel a n m| ≤
      ((2 * a / Real.pi ^ 2) *
        (Real.exp (-a) / (1 - Real.exp (-4 * a)))) / (m : ℝ) := by
    rw [abs_of_nonneg hgeomNonneg]
    exact evenGeometricKernel_le ha hnm
  unfold even625BaseRhs
  change |deltaSq * evenFirstKernel a n m - evenGeometricKernel a n m +
    evenDigammaCombination y n m| ≤ _
  calc
    |deltaSq * evenFirstKernel a n m - evenGeometricKernel a n m +
        evenDigammaCombination y n m| ≤
      |deltaSq * evenFirstKernel a n m| +
        |evenGeometricKernel a n m| +
        |evenDigammaCombination y n m| := by
      simpa [abs_neg] using abs_add_three
        (deltaSq * evenFirstKernel a n m)
        (-evenGeometricKernel a n m)
        (evenDigammaCombination y n m)
    _ ≤ ((2 * a / Real.pi ^ 2) * deltaSq) / (m : ℝ) +
        ((2 * a / Real.pi ^ 2) *
          (Real.exp (-a) / (1 - Real.exp (-4 * a)))) / (m : ℝ) +
        (1 / 2 + (2 * a) ^ 2 / (10 * Real.pi ^ 3)) / (m : ℝ) :=
      add_le_add (add_le_add hfirst hgeom) hdigamma
    _ = evenDecayConstant a / (m : ℝ) := by
      dsimp [evenDecayConstant, deltaSq]
      ring

/-- Full (6.26) for the exceptional first row, conditional on the sharp
`1/12` digamma remainders. -/
theorem abs_even625BaseRhs_one_le_of_sharp_remainders
    {a : ℝ} (ha : 0 < a) (y : ℕ → ℝ) {m : ℕ} (hm : 4 ≤ m)
    (hOne : |y 1 - digammaAsymptoticMain a 1| ≤
      (2 * a) ^ 2 / (12 * Real.pi ^ 2))
    (hmRem : |y m - digammaAsymptoticMain a m| ≤
      (2 * a) ^ 2 / (12 * Real.pi ^ 2 * (m : ℝ) ^ 2)) :
    |even625BaseRhs a y 1 m| ≤ evenDecayConstant a / (m : ℝ) := by
  apply abs_even625BaseRhs_le_of_digamma_bound ha y (by omega)
  exact abs_evenDigammaCombination_one_le_of_sharp_remainders
    ha y hm hOne hmRem

def even625Normalization (n : ℕ) : ℝ :=
  if n = 0 then (Real.sqrt 2)⁻¹ else 1

def normalizedEven625Rhs
    (a : ℝ) (y : ℕ → ℝ) (n m : ℕ) : ℝ :=
  even625Normalization n * even625BaseRhs a y n m

/-- The digamma combination in the zero row reduces to a single value. -/
theorem evenDigammaCombination_zero
    (y : ℕ → ℝ) {m : ℕ} (hm : 0 < m) (hy0 : y 0 = 0) :
    evenDigammaCombination y 0 m = y m / (Real.pi * (m : ℝ)) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold evenDigammaCombination
  rw [hy0]
  norm_num
  field_simp [hmR, Real.pi_ne_zero]
  ring

/-- Full normalized (6.26) in the zero row. -/
theorem abs_normalizedEven625Rhs_zero_le
    (y : ℕ → ℝ) {m : ℕ} (hm : 200 ≤ m) (hy0 : y 0 = 0)
    (hmRem :
      |y m - digammaAsymptoticMain
          YoshidaWeightedTailBounds.yoshidaA m| ≤
        (2 * YoshidaWeightedTailBounds.yoshidaA) ^ 2 /
          (10 * Real.pi ^ 2 * (m : ℝ) ^ 2)) :
    |normalizedEven625Rhs YoshidaWeightedTailBounds.yoshidaA y 0 m| ≤
      evenDecayConstant YoshidaWeightedTailBounds.yoshidaA / (m : ℝ) := by
  let a : ℝ := YoshidaWeightedTailBounds.yoshidaA
  let deltaSq : ℝ :=
    (Real.exp (a / 2) - Real.exp (-a / 2)) ^ 2
  have ha : 0 < a := YoshidaCoercivityNumerics.yoshidaA_pos
  have hnm : 0 < m := lt_of_lt_of_le (by omega) hm
  have hdelta : 0 ≤ deltaSq := sq_nonneg _
  have hinvSqrt : 0 ≤ (Real.sqrt 2)⁻¹ := by positivity
  have hinvSqrtOne : (Real.sqrt 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (Real.sqrt_pos.2 (by norm_num))]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have hfirstRaw :
      |deltaSq * evenFirstKernel a 0 m| ≤
        ((2 * a / Real.pi ^ 2) * deltaSq) / (m : ℝ) := by
    rw [abs_mul, abs_of_nonneg hdelta]
    calc
      deltaSq * |evenFirstKernel a 0 m| ≤
          deltaSq * ((2 * a / Real.pi ^ 2) / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left (abs_evenFirstKernel_le ha hnm) hdelta
      _ = _ := by ring
  have hfirst : (Real.sqrt 2)⁻¹ *
      |deltaSq * evenFirstKernel a 0 m| ≤
        ((2 * a / Real.pi ^ 2) * deltaSq) / (m : ℝ) := by
    calc
      (Real.sqrt 2)⁻¹ * |deltaSq * evenFirstKernel a 0 m| ≤
          1 * |deltaSq * evenFirstKernel a 0 m| :=
        mul_le_mul_of_nonneg_right hinvSqrtOne (abs_nonneg _)
      _ ≤ _ := by simpa using hfirstRaw
  have hgeomNonneg : 0 ≤ evenGeometricKernel a 0 m := by
    unfold evenGeometricKernel
    exact mul_nonneg (by positivity)
      (tsum_nonneg (evenGeometricTerm_nonneg a 0 m))
  have hgeomRaw : |evenGeometricKernel a 0 m| ≤
      ((2 * a / Real.pi ^ 2) *
        (Real.exp (-a) / (1 - Real.exp (-4 * a)))) / (m : ℝ) := by
    rw [abs_of_nonneg hgeomNonneg]
    exact evenGeometricKernel_le ha hnm
  have hgeom : (Real.sqrt 2)⁻¹ * |evenGeometricKernel a 0 m| ≤
      ((2 * a / Real.pi ^ 2) *
        (Real.exp (-a) / (1 - Real.exp (-4 * a)))) / (m : ℝ) := by
    calc
      (Real.sqrt 2)⁻¹ * |evenGeometricKernel a 0 m| ≤
          1 * |evenGeometricKernel a 0 m| :=
        mul_le_mul_of_nonneg_right hinvSqrtOne (abs_nonneg _)
      _ ≤ _ := by simpa using hgeomRaw
  have hdigamma : (Real.sqrt 2)⁻¹ *
      |evenDigammaCombination y 0 m| ≤ 1 / (2 * (m : ℝ)) := by
    rw [evenDigammaCombination_zero y hnm hy0, abs_div]
    rw [abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos (by exact_mod_cast hnm : (0 : ℝ) < m)]
    simpa [div_eq_mul_inv, mul_assoc] using
      zero_mode_digamma_contribution_le y hm hmRem
  unfold normalizedEven625Rhs even625Normalization
  rw [if_pos rfl, abs_mul, abs_of_nonneg hinvSqrt]
  unfold even625BaseRhs
  change (Real.sqrt 2)⁻¹ *
    |deltaSq * evenFirstKernel a 0 m - evenGeometricKernel a 0 m +
      evenDigammaCombination y 0 m| ≤ _
  calc
    (Real.sqrt 2)⁻¹ *
        |deltaSq * evenFirstKernel a 0 m - evenGeometricKernel a 0 m +
          evenDigammaCombination y 0 m| ≤
      (Real.sqrt 2)⁻¹ * |deltaSq * evenFirstKernel a 0 m| +
        (Real.sqrt 2)⁻¹ * |evenGeometricKernel a 0 m| +
        (Real.sqrt 2)⁻¹ * |evenDigammaCombination y 0 m| := by
      have h := mul_le_mul_of_nonneg_left
        (show
          |deltaSq * evenFirstKernel a 0 m - evenGeometricKernel a 0 m +
              evenDigammaCombination y 0 m| ≤
            |deltaSq * evenFirstKernel a 0 m| +
              |evenGeometricKernel a 0 m| +
              |evenDigammaCombination y 0 m| by
          simpa [abs_neg] using abs_add_three
            (deltaSq * evenFirstKernel a 0 m)
            (-evenGeometricKernel a 0 m)
            (evenDigammaCombination y 0 m)) hinvSqrt
      nlinarith
    _ ≤ ((2 * a / Real.pi ^ 2) * deltaSq) / (m : ℝ) +
        ((2 * a / Real.pi ^ 2) *
          (Real.exp (-a) / (1 - Real.exp (-4 * a)))) / (m : ℝ) +
        1 / (2 * (m : ℝ)) := add_le_add (add_le_add hfirst hgeom) hdigamma
    _ ≤ evenDecayConstant a / (m : ℝ) := by
      unfold evenDecayConstant
      have hextra : 0 ≤ (2 * a) ^ 2 / (10 * Real.pi ^ 3) := by positivity
      rw [show
        (((2 * a / Real.pi ^ 2) *
              (Real.exp (a / 2) - Real.exp (-a / 2)) ^ 2 +
            (2 * a / Real.pi ^ 2) *
              (Real.exp (-a) / (1 - Real.exp (-4 * a))) +
            (1 / 2 + (2 * a) ^ 2 / (10 * Real.pi ^ 3))) / (m : ℝ)) =
          ((2 * a / Real.pi ^ 2) * deltaSq) / (m : ℝ) +
            ((2 * a / Real.pi ^ 2) *
              (Real.exp (-a) / (1 - Real.exp (-4 * a)))) / (m : ℝ) +
            1 / (2 * (m : ℝ)) +
            ((2 * a) ^ 2 / (10 * Real.pi ^ 3)) / (m : ℝ) by
        dsimp [deltaSq]
        ring]
      exact le_add_of_nonneg_right (div_nonneg hextra (Nat.cast_nonneg m))

/-- Actual digamma imaginary samples in Yoshida's mode normalization. -/
def yoshidaEvenDigammaImag (n : ℕ) : ℝ :=
  (Complex.digamma
    ((1 / 4 : ℝ) +
      (Real.pi * (n : ℝ) /
        (2 * YoshidaWeightedTailBounds.yoshidaA)) * Complex.I)).im

/-- Sharp imaginary-mode consequences required from the formalization of
source equation (5.11).  This interface is not proved here.  In particular,
the `1/12` field deliberately retains the sharp remainder needed by the
exceptional first row; the zero identity is the real-axis specialization. -/
structure SharpDigammaImagRemainder5_11 : Prop where
  zero : yoshidaEvenDigammaImag 0 = 0
  sharp : ∀ n : ℕ, 1 ≤ n →
    |yoshidaEvenDigammaImag n -
        digammaAsymptoticMain YoshidaWeightedTailBounds.yoshidaA n| ≤
      (2 * YoshidaWeightedTailBounds.yoshidaA) ^ 2 /
        (12 * Real.pi ^ 2 * (n : ℝ) ^ 2)

/-- The exact remaining equality between the actual clipped pairing formula
and Yoshida's printed equation (6.25).  This interface includes the
`1/sqrt 2` zero-mode normalization and is not proved by the Laplace-formula
bridge alone. -/
def ActualEvenPairingEquation6_25 : Prop :=
  ∀ (i : YoshidaEvenIndex) (k : ℕ),
    yoshidaClippedEvenLowModePairingFormula
        YoshidaWeightedTailBounds.yoshidaA i (200 + k) =
      ((((-1 : ℝ) ^ (i.1 + (200 + k))) *
        normalizedEven625Rhs YoshidaWeightedTailBounds.yoshidaA
          yoshidaEvenDigammaImag i.1 (200 + k) : ℝ) : ℂ)

/-- The normalized printed (6.25) right-hand side satisfies (6.26) on every
canonical low/high pair once the sharp digamma interface is supplied. -/
theorem abs_normalizedEven625Rhs_le_of_remainder5_11
    (hpsi : SharpDigammaImagRemainder5_11)
    {n m : ℕ} (hnm : n < m) (hm : 200 ≤ m) :
    |normalizedEven625Rhs YoshidaWeightedTailBounds.yoshidaA
        yoshidaEvenDigammaImag n m| ≤
      evenDecayConstant YoshidaWeightedTailBounds.yoshidaA / (m : ℝ) := by
  let a : ℝ := YoshidaWeightedTailBounds.yoshidaA
  have ha : 0 < a := YoshidaCoercivityNumerics.yoshidaA_pos
  have weaken (j : ℕ) (hj : 1 ≤ j) :
      |yoshidaEvenDigammaImag j - digammaAsymptoticMain a j| ≤
        (2 * a) ^ 2 / (10 * Real.pi ^ 2 * (j : ℝ) ^ 2) := by
    calc
      |yoshidaEvenDigammaImag j - digammaAsymptoticMain a j| ≤
          (2 * a) ^ 2 / (12 * Real.pi ^ 2 * (j : ℝ) ^ 2) := by
        simpa only [a] using hpsi.sharp j hj
      _ ≤ (2 * a) ^ 2 / (10 * Real.pi ^ 2 * (j : ℝ) ^ 2) := by
        have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hj)
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        nlinarith [Real.pi_pos, sq_pos_of_pos Real.pi_pos, sq_pos_of_pos hjR]
  by_cases hn0 : n = 0
  · subst n
    apply abs_normalizedEven625Rhs_zero_le yoshidaEvenDigammaImag hm hpsi.zero
    simpa only [a] using weaken m (by omega)
  by_cases hn1 : n = 1
  · subst n
    have hOne := hpsi.sharp 1 (by norm_num)
    have hmSharp := hpsi.sharp m (by omega)
    unfold normalizedEven625Rhs even625Normalization
    rw [if_neg (by norm_num : (1 : ℕ) ≠ 0), one_mul]
    apply abs_even625BaseRhs_one_le_of_sharp_remainders ha
      yoshidaEvenDigammaImag (by omega)
    · simpa only [a, Nat.cast_one, one_pow, mul_one] using hOne
    · simpa only [a] using hmSharp
  · have hnTwo : 2 ≤ n := by omega
    unfold normalizedEven625Rhs even625Normalization
    rw [if_neg hn0, one_mul]
    apply abs_even625BaseRhs_le_of_digamma_bound ha yoshidaEvenDigammaImag hnm
    exact abs_evenDigammaCombination_le_of_remainders ha
      yoshidaEvenDigammaImag hnTwo hnm
        (weaken n (by omega)) (weaken m (by omega))

/-- Final source pointwise decay (6.26) for the actual removable-safe
pairing formula, conditional on exactly the two named analytic bridges:
equation (6.25) and the sharp digamma remainder (5.11). -/
theorem even_low_high_pairing_decay_of_bridges
    (hpair : ActualEvenPairingEquation6_25)
    (hpsi : SharpDigammaImagRemainder5_11)
    (i : YoshidaEvenIndex) (k : ℕ) :
    ‖yoshidaClippedEvenLowModePairingFormula
        YoshidaWeightedTailBounds.yoshidaA i (200 + k)‖ ≤
      evenDecayConstant YoshidaWeightedTailBounds.yoshidaA /
        ((200 + k : ℕ) : ℝ) := by
  rw [hpair i k]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul]
  exact abs_normalizedEven625Rhs_le_of_remainder5_11 hpsi
    (by omega) (by omega)

/-- For every nonexceptional low mode, the explicit (6.25) right-hand side
has the full source decay (6.26), assuming only the sharp digamma-imaginary
remainder inherited from (5.11). -/
theorem abs_even625BaseRhs_le
    {a : ℝ} (ha : 0 < a) (y : ℕ → ℝ) {n m : ℕ}
    (hn : 2 ≤ n) (hnm : n < m)
    (hnRem : |y n - digammaAsymptoticMain a n| ≤
      (2 * a) ^ 2 / (10 * Real.pi ^ 2 * (n : ℝ) ^ 2))
    (hmRem : |y m - digammaAsymptoticMain a m| ≤
      (2 * a) ^ 2 / (10 * Real.pi ^ 2 * (m : ℝ) ^ 2)) :
    |even625BaseRhs a y n m| ≤ evenDecayConstant a / (m : ℝ) := by
  let deltaSq : ℝ :=
    (Real.exp (a / 2) - Real.exp (-a / 2)) ^ 2
  have hdelta : 0 ≤ deltaSq := sq_nonneg _
  have hfirst :
      |deltaSq * evenFirstKernel a n m| ≤
        ((2 * a / Real.pi ^ 2) * deltaSq) / (m : ℝ) := by
    rw [abs_mul, abs_of_nonneg hdelta]
    calc
      deltaSq * |evenFirstKernel a n m| ≤
          deltaSq * ((2 * a / Real.pi ^ 2) / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left (abs_evenFirstKernel_le ha hnm) hdelta
      _ = ((2 * a / Real.pi ^ 2) * deltaSq) / (m : ℝ) := by ring
  have hgeomNonneg : 0 ≤ evenGeometricKernel a n m := by
    unfold evenGeometricKernel
    exact mul_nonneg (by positivity)
      (tsum_nonneg (evenGeometricTerm_nonneg a n m))
  have hgeom : |evenGeometricKernel a n m| ≤
      ((2 * a / Real.pi ^ 2) *
        (Real.exp (-a) / (1 - Real.exp (-4 * a)))) / (m : ℝ) := by
    rw [abs_of_nonneg hgeomNonneg]
    exact evenGeometricKernel_le ha hnm
  have hdigamma := abs_evenDigammaCombination_le_of_remainders
    ha y hn hnm hnRem hmRem
  unfold even625BaseRhs
  change |deltaSq * evenFirstKernel a n m - evenGeometricKernel a n m +
    evenDigammaCombination y n m| ≤ _
  calc
    |deltaSq * evenFirstKernel a n m - evenGeometricKernel a n m +
        evenDigammaCombination y n m| ≤
      |deltaSq * evenFirstKernel a n m| +
        |evenGeometricKernel a n m| +
        |evenDigammaCombination y n m| := by
      simpa [abs_neg] using abs_add_three
        (deltaSq * evenFirstKernel a n m)
        (-evenGeometricKernel a n m)
        (evenDigammaCombination y n m)
    _ ≤ ((2 * a / Real.pi ^ 2) * deltaSq) / (m : ℝ) +
        ((2 * a / Real.pi ^ 2) *
          (Real.exp (-a) / (1 - Real.exp (-4 * a)))) / (m : ℝ) +
        (1 / 2 + (2 * a) ^ 2 / (10 * Real.pi ^ 3)) / (m : ℝ) :=
      add_le_add (add_le_add hfirst hgeom) hdigamma
    _ = evenDecayConstant a / (m : ℝ) := by
      dsimp [evenDecayConstant, deltaSq]
      ring

/-! ## Exact enclosure of the source decay constant -/

private theorem certificate_exp_yoshidaA :
    Real.exp YoshidaWeightedTailBounds.yoshidaA = Real.sqrt 2 := by
  rw [YoshidaWeightedTailBounds.yoshidaA, Real.exp_half,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

private theorem certificate_exp_neg_yoshidaA :
    Real.exp (-YoshidaWeightedTailBounds.yoshidaA) =
      1 / Real.sqrt 2 := by
  rw [Real.exp_neg, certificate_exp_yoshidaA]
  simp [one_div]

private theorem certificate_exp_neg_four_yoshidaA :
    Real.exp (-4 * YoshidaWeightedTailBounds.yoshidaA) = 1 / 4 := by
  rw [YoshidaWeightedTailBounds.yoshidaA]
  have harg :
      -(4 : ℝ) * (Real.log 2 / 2) =
        -(Real.log 2 + Real.log 2) := by ring
  rw [harg, Real.exp_neg, Real.exp_add,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

private theorem certificate_sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := by
  norm_num

private theorem certificate_exp_difference_sq :
    (Real.exp (YoshidaWeightedTailBounds.yoshidaA / 2) -
        Real.exp (-YoshidaWeightedTailBounds.yoshidaA / 2)) ^ 2 =
      3 / Real.sqrt 2 - 2 := by
  let a := YoshidaWeightedTailBounds.yoshidaA
  have ht0 : Real.exp (a / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have htSq : Real.exp (a / 2) ^ 2 = Real.sqrt 2 := by
    rw [pow_two, ← Real.exp_add]
    convert certificate_exp_yoshidaA using 1
    dsimp [a]
    ring
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  have hneg : Real.exp (-a / 2) = 1 / Real.exp (a / 2) := by
    rw [show -a / 2 = -(a / 2) by ring, Real.exp_neg]
    simp [one_div]
  change (Real.exp (a / 2) - Real.exp (-a / 2)) ^ 2 = _
  rw [hneg]
  have hexpand :
      (Real.exp (a / 2) - 1 / Real.exp (a / 2)) ^ 2 =
        Real.exp (a / 2) ^ 2 + 1 / Real.exp (a / 2) ^ 2 - 2 := by
    field_simp [ht0]
    ring
  rw [hexpand, htSq]
  field_simp [hs0]
  nlinarith [certificate_sqrt_two_sq]

private theorem certificate_two_a_div_pi_sq_lt :
    2 * YoshidaWeightedTailBounds.yoshidaA / Real.pi ^ 2 <
      (347 / 4500 : ℝ) := by
  rw [div_lt_iff₀ (sq_pos_of_pos Real.pi_pos)]
  calc
    2 * YoshidaWeightedTailBounds.yoshidaA < (694 / 1000 : ℝ) := by
      nlinarith [YoshidaCoercivityNumerics.yoshidaA_lt_347_div_1000]
    _ = (347 / 4500 : ℝ) * 9 := by norm_num
    _ < (347 / 4500 : ℝ) * Real.pi ^ 2 := by
      gcongr
      nlinarith [Real.pi_gt_three]

private theorem certificate_exp_difference_sq_pos :
    0 < (Real.exp (YoshidaWeightedTailBounds.yoshidaA / 2) -
      Real.exp (-YoshidaWeightedTailBounds.yoshidaA / 2)) ^ 2 := by
  apply sq_pos_of_pos
  rw [sub_pos, Real.exp_lt_exp]
  nlinarith [YoshidaCoercivityNumerics.yoshidaA_pos]

private theorem certificate_exp_difference_sq_lt :
    (Real.exp (YoshidaWeightedTailBounds.yoshidaA / 2) -
      Real.exp (-YoshidaWeightedTailBounds.yoshidaA / 2)) ^ 2 <
        (13 / 100 : ℝ) := by
  rw [certificate_exp_difference_sq]
  have h := YoshidaCoercivityNumerics.inv_sqrt_two_lt_71_div_100
  rw [div_eq_mul_inv] at h ⊢
  nlinarith

private theorem certificate_first_term_lt :
    (2 * YoshidaWeightedTailBounds.yoshidaA / Real.pi ^ 2) *
      (Real.exp (YoshidaWeightedTailBounds.yoshidaA / 2) -
        Real.exp (-YoshidaWeightedTailBounds.yoshidaA / 2)) ^ 2 <
      (3 / 250 : ℝ) := by
  calc
    _ < (347 / 4500 : ℝ) * (13 / 100 : ℝ) :=
      mul_lt_mul certificate_two_a_div_pi_sq_lt
        certificate_exp_difference_sq_lt.le
        certificate_exp_difference_sq_pos (by norm_num)
    _ < (3 / 250 : ℝ) := by norm_num

private theorem certificate_gamma_ratio_pos :
    0 < Real.exp (-YoshidaWeightedTailBounds.yoshidaA) /
      (1 - Real.exp (-4 * YoshidaWeightedTailBounds.yoshidaA)) := by
  rw [certificate_exp_neg_yoshidaA,
    certificate_exp_neg_four_yoshidaA]
  positivity

private theorem certificate_gamma_ratio_lt :
    Real.exp (-YoshidaWeightedTailBounds.yoshidaA) /
        (1 - Real.exp (-4 * YoshidaWeightedTailBounds.yoshidaA)) <
      (71 / 75 : ℝ) := by
  rw [certificate_exp_neg_yoshidaA,
    certificate_exp_neg_four_yoshidaA]
  have h := YoshidaCoercivityNumerics.inv_sqrt_two_lt_71_div_100
  rw [div_eq_mul_inv] at h ⊢
  norm_num at h ⊢
  linarith

private theorem certificate_second_term_lt :
    (2 * YoshidaWeightedTailBounds.yoshidaA / Real.pi ^ 2) *
      (Real.exp (-YoshidaWeightedTailBounds.yoshidaA) /
        (1 - Real.exp (-4 * YoshidaWeightedTailBounds.yoshidaA))) <
      (3 / 40 : ℝ) := by
  calc
    _ < (347 / 4500 : ℝ) * (71 / 75 : ℝ) :=
      mul_lt_mul certificate_two_a_div_pi_sq_lt
        certificate_gamma_ratio_lt.le certificate_gamma_ratio_pos
        (by norm_num)
    _ < (3 / 40 : ℝ) := by norm_num

private theorem certificate_last_extra_lt :
    (2 * YoshidaWeightedTailBounds.yoshidaA) ^ 2 /
        (10 * Real.pi ^ 3) < (1 / 500 : ℝ) := by
  rw [div_lt_iff₀ (mul_pos (by norm_num) (pow_pos Real.pi_pos 3))]
  have htwoA :
      2 * YoshidaWeightedTailBounds.yoshidaA < (694 / 1000 : ℝ) := by
    nlinarith [YoshidaCoercivityNumerics.yoshidaA_lt_347_div_1000]
  have htwoAnonneg : 0 ≤ 2 * YoshidaWeightedTailBounds.yoshidaA :=
    (mul_pos (by norm_num) YoshidaCoercivityNumerics.yoshidaA_pos).le
  have hsquare :
      (2 * YoshidaWeightedTailBounds.yoshidaA) ^ 2 <
        (694 / 1000 : ℝ) ^ 2 :=
    (sq_lt_sq₀ htwoAnonneg (by norm_num)).2 htwoA
  calc
    (2 * YoshidaWeightedTailBounds.yoshidaA) ^ 2 <
        (694 / 1000 : ℝ) ^ 2 := hsquare
    _ < (1 / 500 : ℝ) * (10 * 27) := by norm_num
    _ < (1 / 500 : ℝ) * (10 * Real.pi ^ 3) := by
      gcongr
      calc
        (27 : ℝ) = 3 ^ 3 := by norm_num
        _ < Real.pi ^ 3 := pow_lt_pow_left₀ Real.pi_gt_three
          (by norm_num) (by norm_num)

private theorem certificate_evenDecayConstant_pos :
    0 < evenDecayConstant YoshidaWeightedTailBounds.yoshidaA := by
  unfold evenDecayConstant
  have hfirst : 0 <
      (2 * YoshidaWeightedTailBounds.yoshidaA / Real.pi ^ 2) *
        (Real.exp (YoshidaWeightedTailBounds.yoshidaA / 2) -
          Real.exp (-YoshidaWeightedTailBounds.yoshidaA / 2)) ^ 2 :=
    mul_pos (by positivity [YoshidaCoercivityNumerics.yoshidaA_pos])
      certificate_exp_difference_sq_pos
  have hsecond : 0 <
      (2 * YoshidaWeightedTailBounds.yoshidaA / Real.pi ^ 2) *
        (Real.exp (-YoshidaWeightedTailBounds.yoshidaA) /
          (1 - Real.exp (-4 * YoshidaWeightedTailBounds.yoshidaA))) :=
    mul_pos (by positivity [YoshidaCoercivityNumerics.yoshidaA_pos])
      certificate_gamma_ratio_pos
  positivity

private theorem certificate_evenDecayConstant_lt :
    evenDecayConstant YoshidaWeightedTailBounds.yoshidaA <
      (589 / 1000 : ℝ) := by
  unfold evenDecayConstant
  nlinarith [certificate_first_term_lt, certificate_second_term_lt,
    certificate_last_extra_lt]

/-- Exact coarse enclosure of Yoshida's even decay constant. -/
theorem evenDecayConstant_yoshida_sq_le :
    evenDecayConstant YoshidaWeightedTailBounds.yoshidaA ^ 2 ≤
      (10149 / 25000 : ℝ) := by
  have hsquare :
      evenDecayConstant YoshidaWeightedTailBounds.yoshidaA ^ 2 <
        (589 / 1000 : ℝ) ^ 2 :=
    (sq_lt_sq₀ certificate_evenDecayConstant_pos.le (by norm_num)).2
      certificate_evenDecayConstant_lt
  norm_num at hsquare ⊢
  linarith

/-- Squared pointwise (6.26) in exactly the form consumed by
`YoshidaEvenTailReduction.evenLowTailCouplingEnergy_le_of_decay`. -/
theorem even_low_high_pairing_sq_decay_of_bridges
    (hpair : ActualEvenPairingEquation6_25)
    (hpsi : SharpDigammaImagRemainder5_11)
    (i : YoshidaEvenIndex) (k : ℕ) :
    ‖yoshidaClippedEvenLowModePairingFormula
        YoshidaWeightedTailBounds.yoshidaA i (200 + k)‖ ^ 2 ≤
      (10149 / 25000 : ℝ) /
        (((200 + k : ℕ) : ℝ) ^ 2) := by
  let m : ℝ := ((200 + k : ℕ) : ℝ)
  let C : ℝ := evenDecayConstant YoshidaWeightedTailBounds.yoshidaA
  have hm : 0 < m := by dsimp [m]; positivity
  have hC : 0 < C := certificate_evenDecayConstant_pos
  have hdecay := even_low_high_pairing_decay_of_bridges hpair hpsi i k
  change ‖yoshidaClippedEvenLowModePairingFormula
        YoshidaWeightedTailBounds.yoshidaA i (200 + k)‖ ≤ C / m at hdecay
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hdecay 2
  calc
    ‖yoshidaClippedEvenLowModePairingFormula
        YoshidaWeightedTailBounds.yoshidaA i (200 + k)‖ ^ 2 ≤
      (C / m) ^ 2 := hsquare
    _ = C ^ 2 / m ^ 2 := by ring
    _ ≤ (10149 / 25000 : ℝ) / m ^ 2 :=
      div_le_div_of_nonneg_right evenDecayConstant_yoshida_sq_le
        (sq_nonneg m)
    _ = (10149 / 25000 : ℝ) /
        (((200 + k : ℕ) : ℝ) ^ 2) := rfl

end

end ArithmeticHodge.Analysis.YoshidaEvenCouplingReduction
