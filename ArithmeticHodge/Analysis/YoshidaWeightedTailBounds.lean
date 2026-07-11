import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaWeightedTailBounds

/-!
# Certified Yoshida weighted-tail bounds

This module proves the two high-frequency series bounds used in Yoshida's
Section 6 substitutions.  Each proof has three kernel-checkable layers:

* comparison with a rational majorant using `piLowerR = 6283 / 2000`;
* exact finite-head evaluation over `ℚ` with `decide +kernel`;
* telescoping bounds for the remaining `n⁻²`, `n⁻³`, and `n⁻⁴` tails.

No floating-point evaluation is used as a proof oracle.
-/

theorem invSq_tail_le (K : ℕ) (hK : 0 < K) :
    (∑' k : ℕ, 1 / (((K + 1 + k : ℕ) : ℝ) ^ 2)) ≤ 1 / (K : ℝ) := by
  apply Real.tsum_le_of_sum_range_le
  · intro k
    positivity
  · intro m
    calc
      ∑ k ∈ Finset.range m, 1 / (((K + 1 + k : ℕ) : ℝ) ^ 2) ≤
          ∑ k ∈ Finset.range m,
            (1 / ((K + k : ℕ) : ℝ) - 1 / ((K + 1 + k : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hA : (0 : ℝ) < ((K + k : ℕ) : ℝ) := by
          exact_mod_cast Nat.add_pos_left hK k
        have hA1 : (0 : ℝ) < ((K + 1 + k : ℕ) : ℝ) := by positivity
        have hcast : ((K + 1 + k : ℕ) : ℝ) = ((K + k : ℕ) : ℝ) + 1 := by
          norm_num
          ring
        field_simp
        nlinarith
      _ = 1 / (K : ℝ) - 1 / ((K + m : ℕ) : ℝ) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (Finset.sum_range_sub' (fun k : ℕ ↦ 1 / ((K + k : ℕ) : ℝ)) m)
      _ ≤ 1 / (K : ℝ) := by
        have : 0 ≤ 1 / ((K + m : ℕ) : ℝ) := by positivity
        linarith

theorem invCube_tail_le (K : ℕ) (hK : 0 < K) :
    (∑' k : ℕ, 1 / (((K + k + 1 : ℕ) : ℝ) ^ 3)) ≤
      1 / (2 * (K : ℝ) ^ 2) := by
  apply Real.tsum_le_of_sum_range_le
  · intro k
    positivity
  · intro m
    calc
      ∑ k ∈ Finset.range m, 1 / (((K + k + 1 : ℕ) : ℝ) ^ 3) ≤
          ∑ k ∈ Finset.range m,
            (1 / 2 : ℝ) *
              (1 / ((K + k : ℕ) : ℝ) ^ 2 -
                1 / ((K + k + 1 : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro k hk
        have hA : (0 : ℝ) < ((K + k : ℕ) : ℝ) := by
          exact_mod_cast Nat.add_pos_left hK k
        have hA1 : (0 : ℝ) < ((K + k + 1 : ℕ) : ℝ) := by positivity
        have hcast : ((K + k + 1 : ℕ) : ℝ) = ((K + k : ℕ) : ℝ) + 1 := by
          norm_num
        field_simp
        rw [hcast]
        ring_nf
        nlinarith [sq_nonneg ((K + k : ℕ) : ℝ)]
      _ = (1 / 2 : ℝ) *
          (1 / (K : ℝ) ^ 2 - 1 / ((K + m : ℕ) : ℝ) ^ 2) := by
        rw [← Finset.mul_sum]
        exact congrArg (fun x : ℝ ↦ (1 / 2 : ℝ) * x)
          (Finset.sum_range_sub'
            (fun k : ℕ ↦ 1 / ((K + k : ℕ) : ℝ) ^ 2) m)
      _ ≤ 1 / (2 * (K : ℝ) ^ 2) := by
        have : 0 ≤ 1 / ((K + m : ℕ) : ℝ) ^ 2 := by positivity
        field_simp
        nlinarith

theorem invFourth_tail_le (K : ℕ) (hK : 0 < K) :
    (∑' k : ℕ, 1 / (((K + k + 1 : ℕ) : ℝ) ^ 4)) ≤
      1 / (2 * (K : ℝ) ^ 2 * (K + 1 : ℕ)) := by
  apply Real.tsum_le_of_sum_range_le
  · intro k
    positivity
  · intro m
    calc
      ∑ k ∈ Finset.range m, 1 / (((K + k + 1 : ℕ) : ℝ) ^ 4) ≤
          ∑ k ∈ Finset.range m,
            (1 / (2 * ((K + k : ℕ) : ℝ) ^ 2 * ((K + k + 1 : ℕ) : ℝ)) -
              1 / (2 * ((K + k + 1 : ℕ) : ℝ) ^ 2 *
                ((K + k + 2 : ℕ) : ℝ))) := by
        apply Finset.sum_le_sum
        intro k hk
        have hA : (0 : ℝ) < ((K + k : ℕ) : ℝ) := by
          exact_mod_cast Nat.add_pos_left hK k
        have hA1 : (0 : ℝ) < ((K + k + 1 : ℕ) : ℝ) := by positivity
        have hA2 : (0 : ℝ) < ((K + k + 2 : ℕ) : ℝ) := by positivity
        have hcast1 : ((K + k + 1 : ℕ) : ℝ) = ((K + k : ℕ) : ℝ) + 1 := by
          norm_num
        have hcast2 : ((K + k + 2 : ℕ) : ℝ) = ((K + k : ℕ) : ℝ) + 2 := by
          norm_num
        field_simp
        rw [hcast1, hcast2]
        ring_nf
        nlinarith [sq_nonneg ((K + k : ℕ) : ℝ),
          mul_pos hA (sq_pos_of_pos hA)]
      _ = 1 / (2 * (K : ℝ) ^ 2 * (K + 1 : ℕ)) -
          1 / (2 * ((K + m : ℕ) : ℝ) ^ 2 * ((K + m + 1 : ℕ) : ℝ)) := by
        exact Finset.sum_range_sub'
          (fun k : ℕ ↦
            1 / (2 * ((K + k : ℕ) : ℝ) ^ 2 * ((K + k + 1 : ℕ) : ℝ))) m
      _ ≤ 1 / (2 * (K : ℝ) ^ 2 * (K + 1 : ℕ)) := by
        have : 0 ≤
            1 / (2 * ((K + m : ℕ) : ℝ) ^ 2 * ((K + m + 1 : ℕ) : ℝ)) := by
          positivity
        linarith

def piLowerR : ℝ := 6283 / 2000

def weightedTermUpperR (c : ℝ) (n : ℕ) : ℝ :=
  1 / (n : ℝ) ^ 2 * (2 + c / (piLowerR * n - c)) ^ 2

def tailD (c : ℝ) (K : ℕ) : ℝ :=
  c / (piLowerR - c / (K + 1 : ℕ))

def analyticTailUpperR (c : ℝ) (K : ℕ) : ℝ :=
  4 / K + 2 * tailD c K / K ^ 2 +
    (tailD c K) ^ 2 / (2 * K ^ 2 * (K + 1 : ℕ))

theorem weightedTermUpperR_le_tailPolynomial
    {c : ℝ} {K n : ℕ} (hc : 0 ≤ c) (hK : 0 < K)
    (hn : K + 1 ≤ n)
    (hq : 0 < piLowerR - c / (K + 1 : ℕ)) :
    weightedTermUpperR c n ≤
      4 / (n : ℝ) ^ 2 +
        4 * tailD c K / (n : ℝ) ^ 3 +
        (tailD c K) ^ 2 / (n : ℝ) ^ 4 := by
  have hnPos : 0 < n := lt_of_lt_of_le (Nat.succ_pos K) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hKR : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
  have hnKR : ((K + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  have hratio : (1 : ℝ) ≤ (n : ℝ) / (K + 1 : ℕ) := by
    rw [le_div_iff₀ hKR]
    simpa using hnKR
  have hdenCompare :
      (piLowerR - c / (K + 1 : ℕ)) * n ≤
        piLowerR * n - c := by
    have hcscale : c ≤ c * ((n : ℝ) / (K + 1 : ℕ)) := by
      nlinarith
    calc
      (piLowerR - c / (K + 1 : ℕ)) * n =
          piLowerR * n - c * ((n : ℝ) / (K + 1 : ℕ)) := by ring
      _ ≤ piLowerR * n - c := sub_le_sub_left hcscale _
  have hden : 0 < piLowerR * (n : ℝ) - c :=
    (mul_pos hq hnR).trans_le hdenCompare
  have hfrac : c / (piLowerR * n - c) ≤ tailD c K / n := by
    have hsmall : c / (piLowerR * n - c) ≤
        c / ((piLowerR - c / (K + 1 : ℕ)) * n) := by
      exact div_le_div_of_nonneg_left hc (mul_pos hq hnR) hdenCompare
    apply hsmall.trans_eq
    unfold tailD
    field_simp
  have hd0 : 0 ≤ tailD c K := div_nonneg hc hq.le
  unfold weightedTermUpperR
  have hsq :
      (2 + c / (piLowerR * n - c)) ^ 2 ≤
        (2 + tailD c K / n) ^ 2 := by gcongr
  calc
    1 / (n : ℝ) ^ 2 * (2 + c / (piLowerR * n - c)) ^ 2 ≤
        1 / (n : ℝ) ^ 2 * (2 + tailD c K / n) ^ 2 := by
          gcongr
    _ = 4 / (n : ℝ) ^ 2 +
        4 * tailD c K / (n : ℝ) ^ 3 +
        (tailD c K) ^ 2 / (n : ℝ) ^ 4 := by
      field_simp
      ring

theorem summable_invPow_tail (K p : ℕ) (hp : 1 < p) :
    Summable (fun k : ℕ ↦ 1 / (((K + k + 1 : ℕ) : ℝ) ^ p)) := by
  have hs : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) ^ p)) :=
    Real.summable_one_div_nat_pow.mpr hp
  rw [← summable_nat_add_iff (f := fun n : ℕ ↦ 1 / ((n : ℝ) ^ p)) (K + 1)] at hs
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

theorem weightedUpper_tail_le_analytic
    {c : ℝ} {K : ℕ} (hc : 0 ≤ c) (hK : 0 < K)
    (hq : 0 < piLowerR - c / (K + 1 : ℕ)) :
    (∑' k : ℕ, weightedTermUpperR c (K + k + 1)) ≤
      analyticTailUpperR c K := by
  let d := tailD c K
  let s2 : ℕ → ℝ := fun k ↦ 1 / (((K + k + 1 : ℕ) : ℝ) ^ 2)
  let s3 : ℕ → ℝ := fun k ↦ 1 / (((K + k + 1 : ℕ) : ℝ) ^ 3)
  let s4 : ℕ → ℝ := fun k ↦ 1 / (((K + k + 1 : ℕ) : ℝ) ^ 4)
  let majorant : ℕ → ℝ := fun k ↦ 4 * s2 k + 4 * d * s3 k + d ^ 2 * s4 k
  have hd0 : 0 ≤ d := by
    dsimp [d]
    exact div_nonneg hc hq.le
  have hs2 : Summable s2 := by
    simpa [s2] using summable_invPow_tail K 2 (by omega)
  have hs3 : Summable s3 := by
    simpa [s3] using summable_invPow_tail K 3 (by omega)
  have hs4 : Summable s4 := by
    simpa [s4] using summable_invPow_tail K 4 (by omega)
  have hmajorant : Summable majorant :=
    ((hs2.mul_left 4).add (hs3.mul_left (4 * d))).add
      (hs4.mul_left (d ^ 2))
  have hpoint (k : ℕ) :
      weightedTermUpperR c (K + k + 1) ≤ majorant k := by
    dsimp [majorant, s2, s3, s4, d]
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      weightedTermUpperR_le_tailPolynomial hc hK
        (show K + 1 ≤ K + k + 1 by omega) hq
  have hterm0 (k : ℕ) : 0 ≤ weightedTermUpperR c (K + k + 1) := by
    unfold weightedTermUpperR
    positivity
  have hweighted : Summable (fun k : ℕ ↦ weightedTermUpperR c (K + k + 1)) :=
    hmajorant.of_nonneg_of_le hterm0 hpoint
  calc
    (∑' k : ℕ, weightedTermUpperR c (K + k + 1)) ≤
        ∑' k : ℕ, majorant k :=
      hweighted.tsum_le_tsum hpoint hmajorant
    _ = 4 * (∑' k : ℕ, s2 k) +
        4 * d * (∑' k : ℕ, s3 k) + d ^ 2 * (∑' k : ℕ, s4 k) := by
      dsimp [majorant]
      rw [((hs2.mul_left 4).add (hs3.mul_left (4 * d))).tsum_add
          (hs4.mul_left (d ^ 2)),
        (hs2.mul_left 4).tsum_add (hs3.mul_left (4 * d)),
        hs2.tsum_mul_left 4, hs3.tsum_mul_left (4 * d),
        hs4.tsum_mul_left (d ^ 2)]
    _ ≤ 4 * (1 / (K : ℝ)) +
        4 * d * (1 / (2 * (K : ℝ) ^ 2)) +
        d ^ 2 * (1 / (2 * (K : ℝ) ^ 2 * (K + 1 : ℕ))) := by
      gcongr
      · simpa [s2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          invSq_tail_le K hK
      · simpa [s3] using invCube_tail_le K hK
      · simpa [s4] using invFourth_tail_le K hK
    _ = analyticTailUpperR c K := by
      dsimp [analyticTailUpperR, d]
      ring

theorem summable_weightedUpper_tail
    {c : ℝ} {K : ℕ} (hc : 0 ≤ c) (hK : 0 < K)
    (hq : 0 < piLowerR - c / (K + 1 : ℕ)) :
    Summable (fun k : ℕ ↦ weightedTermUpperR c (K + k + 1)) := by
  let d := tailD c K
  let s2 : ℕ → ℝ := fun k ↦ 1 / (((K + k + 1 : ℕ) : ℝ) ^ 2)
  let s3 : ℕ → ℝ := fun k ↦ 1 / (((K + k + 1 : ℕ) : ℝ) ^ 3)
  let s4 : ℕ → ℝ := fun k ↦ 1 / (((K + k + 1 : ℕ) : ℝ) ^ 4)
  let majorant : ℕ → ℝ := fun k ↦ 4 * s2 k + 4 * d * s3 k + d ^ 2 * s4 k
  have hs2 : Summable s2 := by
    simpa [s2] using summable_invPow_tail K 2 (by omega)
  have hs3 : Summable s3 := by
    simpa [s3] using summable_invPow_tail K 3 (by omega)
  have hs4 : Summable s4 := by
    simpa [s4] using summable_invPow_tail K 4 (by omega)
  have hmajorant : Summable majorant :=
    ((hs2.mul_left 4).add (hs3.mul_left (4 * d))).add
      (hs4.mul_left (d ^ 2))
  apply hmajorant.of_nonneg_of_le
  · intro k
    unfold weightedTermUpperR
    positivity
  · intro k
    dsimp [majorant, s2, s3, s4, d]
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      weightedTermUpperR_le_tailPolynomial hc hK
        (show K + 1 ≤ K + k + 1 by omega) hq

def piLowerQ : ℚ := 6283 / 2000

def weightedTermUpperQ (c : ℚ) (n : ℕ) : ℚ :=
  1 / (n : ℚ) ^ 2 * (2 + c / (piLowerQ * n - c)) ^ 2

def finiteWeightedUpperQ (c : ℚ) (first count : ℕ) : ℚ :=
  ∑ k ∈ Finset.range count, weightedTermUpperQ c (first + k)

def tailDQ (c : ℚ) (K : ℕ) : ℚ :=
  c / (piLowerQ - c / (K + 1 : ℕ))

def analyticTailUpperQ (c : ℚ) (K : ℕ) : ℚ :=
  4 / K + 2 * tailDQ c K / K ^ 2 +
    (tailDQ c K) ^ 2 / (2 * K ^ 2 * (K + 1 : ℕ))

def oddCUpperQ : ℚ := 173287 / 10000
def evenCUpperQ : ℚ := 1213009 / 5000

theorem odd_rational_head_tail_certificate :
    finiteWeightedUpperQ oddCUpperQ 11 90 +
      analyticTailUpperQ oddCUpperQ 100 < 283 / 500 := by
  decide +kernel

theorem even_rational_head_tail_certificate :
    finiteWeightedUpperQ evenCUpperQ 200 201 +
      analyticTailUpperQ evenCUpperQ 400 < 53 / 2000 := by
  decide +kernel

theorem coe_weightedTermUpperQ (c : ℚ) (n : ℕ) :
    ((weightedTermUpperQ c n : ℚ) : ℝ) = weightedTermUpperR c n := by
  norm_num [weightedTermUpperQ, weightedTermUpperR, piLowerQ, piLowerR]

theorem coe_finiteWeightedUpperQ (c : ℚ) (first count : ℕ) :
    ((finiteWeightedUpperQ c first count : ℚ) : ℝ) =
      ∑ k ∈ Finset.range count, weightedTermUpperR c (first + k) := by
  simp [finiteWeightedUpperQ, coe_weightedTermUpperQ]

theorem coe_tailDQ (c : ℚ) (K : ℕ) :
    ((tailDQ c K : ℚ) : ℝ) = tailD c K := by
  norm_num [tailDQ, tailD, piLowerQ, piLowerR]

theorem coe_analyticTailUpperQ (c : ℚ) (K : ℕ) :
    ((analyticTailUpperQ c K : ℚ) : ℝ) = analyticTailUpperR c K := by
  norm_num [analyticTailUpperQ, analyticTailUpperR, coe_tailDQ]

def yoshidaA : ℝ := Real.log 2 / 2

def weightedTermR (p c : ℝ) (n : ℕ) : ℝ :=
  1 / (n : ℝ) ^ 2 * (1 + p * n / (p * n - c)) ^ 2

def weightedTail (N : ℕ) (t : ℝ) : ℝ :=
  ∑' k : ℕ, weightedTermR Real.pi (yoshidaA * t) (N + k + 1)

theorem weightedTermR_le_of_bounds
    {p c cUpper : ℝ} {n : ℕ}
    (hn : 0 < n) (hc : 0 ≤ c) (hcUpper : 0 ≤ cUpper)
    (hcc : c ≤ cUpper) (hp : piLowerR ≤ p)
    (hdenUpper : cUpper < piLowerR * n) :
    weightedTermR p c n ≤ weightedTermUpperR cUpper n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdenU : 0 < piLowerR * (n : ℝ) - cUpper := sub_pos.mpr hdenUpper
  have hpn : piLowerR * (n : ℝ) ≤ p * n := by
    exact mul_le_mul_of_nonneg_right hp hnR.le
  have hden : 0 < p * (n : ℝ) - c := by
    nlinarith
  have hcp : c * piLowerR ≤ cUpper * p := by
    calc
      c * piLowerR ≤ cUpper * piLowerR := by
        exact mul_le_mul_of_nonneg_right hcc (by norm_num [piLowerR])
      _ ≤ cUpper * p := mul_le_mul_of_nonneg_left hp hcUpper
  have hfrac : c / (p * n - c) ≤
      cUpper / (piLowerR * n - cUpper) := by
    rw [div_le_div_iff₀ hden hdenU]
    have := mul_le_mul_of_nonneg_right hcp hnR.le
    nlinarith
  have hrewrite : 1 + p * (n : ℝ) / (p * n - c) =
      2 + c / (p * n - c) := by
    field_simp
    ring
  unfold weightedTermR weightedTermUpperR
  rw [hrewrite]
  have hleft0 : 0 ≤ 2 + c / (p * n - c) := by positivity
  have hright0 : 0 ≤ 2 + cUpper / (piLowerR * n - cUpper) := by positivity
  gcongr

theorem piLowerR_le_pi : piLowerR ≤ Real.pi := by
  calc
    piLowerR = (3.1415 : ℝ) := by norm_num [piLowerR]
    _ ≤ Real.pi := Real.pi_gt_d4.le

theorem weightedTail_le_finite_add_analytic
    {N count : ℕ} {t cUpper : ℝ}
    (hN : 0 < N) (hc : 0 ≤ yoshidaA * t) (hcUpper : 0 ≤ cUpper)
    (hcc : yoshidaA * t ≤ cUpper)
    (hdenBase : cUpper < piLowerR * (N + 1 : ℕ)) :
    weightedTail N t ≤
      (∑ k ∈ Finset.range count,
        weightedTermUpperR cUpper (N + k + 1)) +
      analyticTailUpperR cUpper (N + count) := by
  let actual : ℕ → ℝ := fun k ↦
    weightedTermR Real.pi (yoshidaA * t) (N + k + 1)
  let upper : ℕ → ℝ := fun k ↦
    weightedTermUpperR cUpper (N + k + 1)
  have hq_of_le {K : ℕ} (hNK : N ≤ K) :
      0 < piLowerR - cUpper / (K + 1 : ℕ) := by
    have hcast : ((N + 1 : ℕ) : ℝ) ≤ (K + 1 : ℕ) := by exact_mod_cast Nat.add_le_add_right hNK 1
    have hpi0 : 0 ≤ piLowerR := by norm_num [piLowerR]
    have hdenK : cUpper < piLowerR * (K + 1 : ℕ) :=
      hdenBase.trans_le (mul_le_mul_of_nonneg_left hcast hpi0)
    have hKpos : (0 : ℝ) < (K + 1 : ℕ) := by positivity
    rw [sub_pos, div_lt_iff₀ hKpos]
    exact hdenK
  have hqN : 0 < piLowerR - cUpper / (N + 1 : ℕ) :=
    hq_of_le (le_refl N)
  have hupperSummable : Summable upper := by
    simpa [upper, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      summable_weightedUpper_tail hcUpper hN hqN
  have hpoint (k : ℕ) : actual k ≤ upper k := by
    dsimp [actual, upper]
    apply weightedTermR_le_of_bounds
    · omega
    · exact hc
    · exact hcUpper
    · exact hcc
    · exact piLowerR_le_pi
    · have hncast : ((N + 1 : ℕ) : ℝ) ≤ (N + k + 1 : ℕ) := by
        exact_mod_cast (show N + 1 ≤ N + k + 1 by omega)
      exact hdenBase.trans_le
        (mul_le_mul_of_nonneg_left hncast (by norm_num [piLowerR]))
  have hactual0 (k : ℕ) : 0 ≤ actual k := by
    dsimp [actual, weightedTermR]
    positivity
  have hactualSummable : Summable actual :=
    hupperSummable.of_nonneg_of_le hactual0 hpoint
  have hsplit := hactualSummable.sum_add_tsum_nat_add count
  have htailActual : Summable (fun k : ℕ ↦ actual (k + count)) :=
    (summable_nat_add_iff count).2 hactualSummable
  have hKpos : 0 < N + count := Nat.lt_add_right count hN
  have hqK : 0 < piLowerR - cUpper / (N + count + 1 : ℕ) :=
    hq_of_le (Nat.le_add_right N count)
  have htailUpper : Summable
      (fun k : ℕ ↦ weightedTermUpperR cUpper (N + count + k + 1)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      summable_weightedUpper_tail hcUpper hKpos hqK
  have htailPoint (k : ℕ) :
      actual (k + count) ≤
        weightedTermUpperR cUpper (N + count + k + 1) := by
    simpa [actual, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hpoint (k + count)
  rw [weightedTail]
  change (∑' k : ℕ, actual k) ≤ _
  rw [← hsplit]
  calc
    (∑ k ∈ Finset.range count, actual k) +
        ∑' k : ℕ, actual (k + count) ≤
      (∑ k ∈ Finset.range count, upper k) +
        ∑' k : ℕ, weightedTermUpperR cUpper (N + count + k + 1) := by
      apply add_le_add
      · exact Finset.sum_le_sum fun k hk ↦ hpoint k
      · exact htailActual.tsum_le_tsum htailPoint htailUpper
    _ ≤ (∑ k ∈ Finset.range count, upper k) +
        analyticTailUpperR cUpper (N + count) := by
      gcongr
      exact weightedUpper_tail_le_analytic hcUpper hKpos hqK
    _ = (∑ k ∈ Finset.range count,
          weightedTermUpperR cUpper (N + k + 1)) +
        analyticTailUpperR cUpper (N + count) := by
      rfl

theorem yoshidaA_mul_fifty_le_oddCUpper :
    yoshidaA * 50 ≤ ((oddCUpperQ : ℚ) : ℝ) := by
  norm_num [yoshidaA, oddCUpperQ] at ⊢
  nlinarith [Real.log_two_lt_d9]

theorem yoshidaA_mul_sevenHundred_le_evenCUpper :
    yoshidaA * 700 ≤ ((evenCUpperQ : ℚ) : ℝ) := by
  norm_num [yoshidaA, evenCUpperQ] at ⊢
  nlinarith [Real.log_two_lt_d9]

theorem odd_weightedTail_upper :
    weightedTail 10 50 ≤ (283 / 500 : ℝ) := by
  have h := weightedTail_le_finite_add_analytic
    (N := 10) (count := 90) (t := (50 : ℝ))
    (cUpper := ((oddCUpperQ : ℚ) : ℝ))
    (by norm_num)
    (by unfold yoshidaA; positivity)
    (by norm_num [oddCUpperQ])
    yoshidaA_mul_fifty_le_oddCUpper
    (by norm_num [oddCUpperQ, piLowerR])
  rw [show 10 + 90 = 100 by norm_num] at h
  have hcert :
      ((finiteWeightedUpperQ oddCUpperQ 11 90 : ℚ) : ℝ) +
          ((analyticTailUpperQ oddCUpperQ 100 : ℚ) : ℝ) <
        (283 / 500 : ℝ) := by
    have hr :
        (((finiteWeightedUpperQ oddCUpperQ 11 90 +
            analyticTailUpperQ oddCUpperQ 100 : ℚ)) : ℝ) <
          (((283 / 500 : ℚ)) : ℝ) := by
      exact_mod_cast odd_rational_head_tail_certificate
    simpa using hr
  rw [coe_finiteWeightedUpperQ, coe_analyticTailUpperQ] at hcert
  norm_num [oddCUpperQ] at hcert h
  exact h.trans hcert.le

theorem even_weightedTail_upper :
    weightedTail 199 700 ≤ (53 / 2000 : ℝ) := by
  have h := weightedTail_le_finite_add_analytic
    (N := 199) (count := 201) (t := (700 : ℝ))
    (cUpper := ((evenCUpperQ : ℚ) : ℝ))
    (by norm_num)
    (by unfold yoshidaA; positivity)
    (by norm_num [evenCUpperQ])
    yoshidaA_mul_sevenHundred_le_evenCUpper
    (by norm_num [evenCUpperQ, piLowerR])
  rw [show 199 + 201 = 400 by norm_num] at h
  have hcert :
      ((finiteWeightedUpperQ evenCUpperQ 200 201 : ℚ) : ℝ) +
          ((analyticTailUpperQ evenCUpperQ 400 : ℚ) : ℝ) <
        (53 / 2000 : ℝ) := by
    have hr :
        (((finiteWeightedUpperQ evenCUpperQ 200 201 +
            analyticTailUpperQ evenCUpperQ 400 : ℚ)) : ℝ) <
          (((53 / 2000 : ℚ)) : ℝ) := by
      exact_mod_cast even_rational_head_tail_certificate
    simpa using hr
  rw [coe_finiteWeightedUpperQ, coe_analyticTailUpperQ] at hcert
  norm_num [evenCUpperQ] at hcert h
  exact h.trans hcert.le

end ArithmeticHodge.Analysis.YoshidaWeightedTailBounds
