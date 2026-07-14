import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.CauchyKernelFiniteSumBounds

/-!
# Structural finite Cauchy-kernel bounds

The quarter-shifted kernel below is majorized by a telescoping rational
function.  This avoids evaluating any finite head term by term.
-/

/-- The rational quarter-shifted Cauchy kernel at an arbitrary height. -/
def quarterShiftedCauchyKernelAtHeight (y : ℚ) (k : ℕ) : ℚ :=
  1 / (((k : ℚ) + 1 / 4) ^ 2 + y ^ 2)

/-- A pointwise telescope valid uniformly at every rational height at least
four. -/
theorem quarterShiftedCauchyKernelAtHeight_le_telescoping
    {y : ℚ} (hy : 4 ≤ y) (k : ℕ) :
    quarterShiftedCauchyKernelAtHeight y k ≤
      (9 / 4 : ℚ) *
        (1 / ((k : ℚ) + y) - 1 / ((k : ℚ) + y + 1)) := by
  let x : ℚ := k
  have hx : 0 ≤ x := by positivity
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hxy0 : 0 < x + y := add_pos_of_nonneg_of_pos hx hy0
  have hxy10 : 0 < x + y + 1 := by positivity
  have hden0 : 0 < (x + 1 / 4) ^ 2 + y ^ 2 := by positivity
  have hprod0 : 0 < (x + y) * (x + y + 1) := mul_pos hxy0 hxy10
  have hpoly :
      (x + y) * (x + y + 1) ≤
        (9 / 4 : ℚ) * ((x + 1 / 4) ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (10 * x - (8 * y - 1 / 2)),
      sq_nonneg (y - 2)]
  change 1 / ((x + 1 / 4) ^ 2 + y ^ 2) ≤
    (9 / 4 : ℚ) * (1 / (x + y) - 1 / (x + y + 1))
  rw [show 1 / (x + y) - 1 / (x + y + 1) =
      1 / ((x + y) * (x + y + 1)) by
    field_simp
    ring]
  have hquot : 1 / ((x + 1 / 4) ^ 2 + y ^ 2) ≤
      (9 / 4 : ℚ) / ((x + y) * (x + y + 1)) := by
    apply (div_le_div_iff₀ hden0 hprod0).2
    simpa only [one_mul] using hpoly
  simpa only [div_eq_mul_inv, one_mul] using hquot

/-- The rational quarter-shifted Cauchy kernel at height `4 * n`. -/
def quarterShiftedCauchyKernel (n k : ℕ) : ℚ :=
  1 / (((k : ℚ) + 1 / 4) ^ 2 + (4 * (n : ℚ)) ^ 2)

/-- A pointwise telescoping majorant for the quarter-shifted Cauchy kernel. -/
theorem quarterShiftedCauchyKernel_le_telescoping
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    quarterShiftedCauchyKernel n k ≤
      (9 / 4 : ℚ) *
        (1 / ((k : ℚ) + 4 * n) -
          1 / ((k : ℚ) + 4 * n + 1)) := by
  have hy : 4 ≤ (4 : ℚ) * n := by
    show 4 ≤ (4 : ℚ) * n
    exact_mod_cast (show 4 ≤ 4 * n by omega)
  exact quarterShiftedCauchyKernelAtHeight_le_telescoping hy k

/-- The general telescope summed over an arbitrary finite head. -/
theorem sum_quarterShiftedCauchyKernelAtHeight_le
    {y : ℚ} (hy : 4 ≤ y) (K : ℕ) :
    (∑ k ∈ Finset.range K, quarterShiftedCauchyKernelAtHeight y k) ≤
      9 / (4 * y) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  calc
    (∑ k ∈ Finset.range K, quarterShiftedCauchyKernelAtHeight y k) ≤
        ∑ k ∈ Finset.range K, (9 / 4 : ℚ) *
          (1 / ((k : ℚ) + y) - 1 / ((k : ℚ) + y + 1)) := by
      exact Finset.sum_le_sum fun k _hk ↦
        quarterShiftedCauchyKernelAtHeight_le_telescoping hy k
    _ = (9 / 4 : ℚ) * (1 / y - 1 / ((K : ℚ) + y)) := by
      rw [← Finset.mul_sum]
      congr 1
      let f : ℕ → ℚ := fun k ↦ 1 / ((k : ℚ) + y)
      calc
        ∑ k ∈ Finset.range K,
            (1 / ((k : ℚ) + y) - 1 / ((k : ℚ) + y + 1)) =
            ∑ k ∈ Finset.range K, (f k - f (k + 1)) := by
          apply Finset.sum_congr rfl
          intro k _hk
          dsimp only [f]
          congr 2
          norm_num
          ring
        _ = f 0 - f K := Finset.sum_range_sub' f K
        _ = 1 / y - 1 / ((K : ℚ) + y) := by
          dsimp only [f]
          norm_num
    _ ≤ (9 / 4 : ℚ) * (1 / y) := by
      have hyNonneg : 0 ≤ y := le_trans (by norm_num) hy
      have hdenNonneg : 0 ≤ (K : ℚ) + y :=
        add_nonneg (by positivity) hyNonneg
      have htail : 0 ≤ 1 / ((K : ℚ) + y) :=
        one_div_nonneg.mpr hdenNonneg
      nlinarith
    _ = 9 / (4 * y) := by
      field_simp

/-- Every finite head of the quarter-shifted Cauchy kernel is `O(1 / n)`,
uniformly in the cutoff. -/
theorem sum_quarterShiftedCauchyKernel_le
    {n : ℕ} (hn : 1 ≤ n) (K : ℕ) :
    (∑ k ∈ Finset.range K, quarterShiftedCauchyKernel n k) ≤
      9 / (16 * (n : ℚ)) := by
  calc
    (∑ k ∈ Finset.range K, quarterShiftedCauchyKernel n k) ≤
        ∑ k ∈ Finset.range K, (9 / 4 : ℚ) *
          (1 / ((k : ℚ) + 4 * n) -
            1 / ((k : ℚ) + 4 * n + 1)) := by
      exact Finset.sum_le_sum fun k _hk ↦
        quarterShiftedCauchyKernel_le_telescoping hn k
    _ = (9 / 4 : ℚ) *
        (1 / (4 * (n : ℚ)) - 1 / ((K : ℚ) + 4 * n)) := by
      rw [← Finset.mul_sum]
      congr 1
      let f : ℕ → ℚ := fun k ↦ 1 / ((k : ℚ) + 4 * n)
      calc
        ∑ k ∈ Finset.range K,
            (1 / ((k : ℚ) + 4 * n) - 1 / ((k : ℚ) + 4 * n + 1)) =
            ∑ k ∈ Finset.range K, (f k - f (k + 1)) := by
          apply Finset.sum_congr rfl
          intro k _hk
          dsimp only [f]
          congr 2
          norm_num
          ring
        _ = f 0 - f K := Finset.sum_range_sub' f K
        _ = 1 / (4 * (n : ℚ)) - 1 / ((K : ℚ) + 4 * n) := by
          dsimp only [f]
          norm_num
    _ ≤ (9 / 4 : ℚ) * (1 / (4 * (n : ℚ))) := by
      have hden : 0 ≤ (K : ℚ) + 4 * n := by positivity
      have htail : 0 ≤ 1 / ((K : ℚ) + 4 * n) :=
        one_div_nonneg.mpr hden
      nlinarith
    _ = 9 / (16 * (n : ℚ)) := by
      have hnNat0 : 0 < n := Nat.zero_lt_of_lt hn
      have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hnNat0.ne'
      field_simp
      ring

/-- The quarter-shifted Cauchy kernel at the sharper half-step height
`(9 / 2) * n`. -/
def halfStepQuarterShiftedCauchyKernel (n k : ℕ) : ℚ :=
  1 / (((k : ℚ) + 1 / 4) ^ 2 + ((9 / 2 : ℚ) * n) ^ 2)

/-- The common pointwise telescope specialized to height `(9 / 2) * n`. -/
theorem halfStepQuarterShiftedCauchyKernel_le_telescoping
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    halfStepQuarterShiftedCauchyKernel n k ≤
      (9 / 4 : ℚ) *
        (1 / ((k : ℚ) + (9 / 2 : ℚ) * n) -
          1 / ((k : ℚ) + (9 / 2 : ℚ) * n + 1)) := by
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hy : (4 : ℚ) ≤ (9 / 2 : ℚ) * n := by nlinarith
  exact quarterShiftedCauchyKernelAtHeight_le_telescoping hy k

/-- Every finite head at height `(9 / 2) * n` is bounded by `1 / (2 * n)`,
uniformly in the cutoff. -/
theorem sum_halfStepQuarterShiftedCauchyKernel_le
    {n : ℕ} (hn : 1 ≤ n) (K : ℕ) :
    (∑ k ∈ Finset.range K, halfStepQuarterShiftedCauchyKernel n k) ≤
      1 / (2 * (n : ℚ)) := by
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hy : (4 : ℚ) ≤ (9 / 2 : ℚ) * n := by nlinarith
  calc
    (∑ k ∈ Finset.range K, halfStepQuarterShiftedCauchyKernel n k) =
        ∑ k ∈ Finset.range K,
          quarterShiftedCauchyKernelAtHeight ((9 / 2 : ℚ) * n) k := rfl
    _ ≤ 9 / (4 * ((9 / 2 : ℚ) * n)) :=
      sum_quarterShiftedCauchyKernelAtHeight_le hy K
    _ = 1 / (2 * (n : ℚ)) := by
      have hnNat0 : 0 < n := Nat.zero_lt_of_lt hn
      have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hnNat0.ne'
      field_simp
      ring

end ArithmeticHodge.Analysis.CauchyKernelFiniteSumBounds
