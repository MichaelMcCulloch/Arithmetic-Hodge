import Mathlib.Analysis.PSeries

set_option autoImplicit false

open Filter Real
open scoped BigOperators Topology

namespace ArithmeticHodge.Analysis.YoshidaCauchyTailBounds

noncomputable section

/-!
# Elementary Cauchy-series tail bounds

This module bounds the positive rational series

`∑' k : ℕ, y / ((x + k) ^ 2 + y ^ 2)`

without evaluating it through `arctan` or another special function.  Two
elementary potentials telescope around each summand.  Their limits give the
explicit bounds

`y / x - y ^ 3 / x ^ 3 ≤ tsum ≤ y / x + y / x ^ 2`.

Only `1 ≤ x` and `0 ≤ y` are required; in particular, the estimate also
applies when no comparison between `x` and `y` is available.
-/

/-- The nonnegative Cauchy-series summand at the shifted integer `x + k`. -/
def cauchyTailTerm (x y : ℝ) (k : ℕ) : ℝ :=
  y / ((x + k) ^ 2 + y ^ 2)

/-- Lower telescoping potential. -/
def lowerPotential (x y : ℝ) (k : ℕ) : ℝ :=
  y / (x + k) - y ^ 3 / (x + k) ^ 3

/-- Upper telescoping potential. -/
def upperPotential (x y : ℝ) (k : ℕ) : ℝ :=
  y / (x + k) + y / (x + k) ^ 2

private theorem shifted_pos {x : ℝ} (hx : 1 ≤ x) (k : ℕ) :
    0 < x + (k : ℝ) := by positivity

/-- Every Cauchy-tail summand is nonnegative. -/
theorem cauchyTailTerm_nonneg
    {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    0 ≤ cauchyTailTerm x y k := by
  unfold cauchyTailTerm
  positivity

/-- Comparison with the shifted reciprocal-square `p`-series. -/
theorem cauchyTailTerm_le_pseries
    {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    cauchyTailTerm x y k ≤
      y * ((((k + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
  have ha : 0 < x + (k : ℝ) := shifted_pos hx k
  have hk : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hka : (((k + 1 : ℕ) : ℝ)) ≤ x + (k : ℝ) := by
    push_cast
    linarith
  have hsq : (((k + 1 : ℕ) : ℝ) ^ 2) ≤ (x + (k : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ hk.le hka 2
  rw [cauchyTailTerm, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ hy
  apply inv_anti₀
  · positivity
  · exact hsq.trans (le_add_of_nonneg_right (sq_nonneg y))

/-- The Cauchy-tail series is summable whenever `1 ≤ x` and `0 ≤ y`. -/
theorem summable_cauchyTailTerm
    {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) :
    Summable (cauchyTailTerm x y) := by
  have hp : Summable (fun k : ℕ ↦
      ((((k + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
    exact (summable_nat_add_iff 1).2
      (Real.summable_nat_pow_inv.mpr (by norm_num))
  have hmajor : Summable (fun k : ℕ ↦
      y * ((((k + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := hp.mul_left y
  exact hmajor.of_nonneg_of_le
    (cauchyTailTerm_nonneg hx hy)
    (cauchyTailTerm_le_pseries hx hy)

/-- The consecutive lower-potential difference lies below each summand. -/
theorem lowerPotential_sub_succ_le
    {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    lowerPotential x y k - lowerPotential x y (k + 1) ≤
      cauchyTailTerm x y k := by
  let a : ℝ := x + k
  have ha : 0 < a := by
    dsimp only [a]
    exact shifted_pos hx k
  have ha1 : 0 < a + 1 := by positivity
  have hden : 0 < a ^ 2 + y ^ 2 := by positivity
  have hid :
      cauchyTailTerm x y k -
          (lowerPotential x y k - lowerPotential x y (k + 1)) =
        y * (a ^ 5 + 2 * a ^ 4 * y ^ 2 + 2 * a ^ 4 +
          a ^ 3 * y ^ 2 + a ^ 3 + 3 * a ^ 2 * y ^ 4 +
          3 * a * y ^ 4 + y ^ 4) /
            (a ^ 3 * (a + 1) ^ 3 * (a ^ 2 + y ^ 2)) := by
    dsimp [cauchyTailTerm, lowerPotential, a]
    push_cast
    field_simp [ha.ne', ha1.ne', hden.ne']
    ring
  rw [← sub_nonneg, hid]
  positivity

/-- Each summand lies below the consecutive upper-potential difference. -/
theorem cauchyTailTerm_le_upperPotential_sub_succ
    {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    cauchyTailTerm x y k ≤
      upperPotential x y k - upperPotential x y (k + 1) := by
  let a : ℝ := x + k
  have ha : 0 < a := by
    dsimp only [a]
    exact shifted_pos hx k
  have ha1 : 0 < a + 1 := by positivity
  have hden : 0 < a ^ 2 + y ^ 2 := by positivity
  have hid :
      (upperPotential x y k - upperPotential x y (k + 1)) -
          cauchyTailTerm x y k =
        y * (a ^ 3 + a ^ 2 * y ^ 2 + 3 * a * y ^ 2 + y ^ 2) /
          (a ^ 2 * (a + 1) ^ 2 * (a ^ 2 + y ^ 2)) := by
    dsimp [cauchyTailTerm, upperPotential, a]
    push_cast
    field_simp [ha.ne', ha1.ne', hden.ne']
    ring
  rw [← sub_nonneg, hid]
  positivity

private theorem tendsto_inv_shifted (x : ℝ) :
    Tendsto (fun k : ℕ ↦ (x + (k : ℝ))⁻¹) atTop (nhds 0) := by
  have htop : Tendsto (fun k : ℕ ↦ x + (k : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [one_div] using htop.const_div_atTop 1

private theorem tendsto_lowerPotential (x y : ℝ) :
    Tendsto (lowerPotential x y) atTop (nhds 0) := by
  have h := tendsto_inv_shifted x
  have h1 := h.const_mul y
  have h3 := (h.pow 3).const_mul (y ^ 3)
  have heq : lowerPotential x y = fun k : ℕ ↦
      y * (x + (k : ℝ))⁻¹ - y ^ 3 * ((x + (k : ℝ))⁻¹) ^ 3 := by
    funext k
    rw [lowerPotential, div_eq_mul_inv, div_eq_mul_inv, inv_pow]
  rw [heq]
  simpa using h1.sub h3

private theorem tendsto_upperPotential (x y : ℝ) :
    Tendsto (upperPotential x y) atTop (nhds 0) := by
  have h := tendsto_inv_shifted x
  have h1 := h.const_mul y
  have h2 := (h.pow 2).const_mul y
  have heq : upperPotential x y = fun k : ℕ ↦
      y * (x + (k : ℝ))⁻¹ + y * ((x + (k : ℝ))⁻¹) ^ 2 := by
    funext k
    rw [upperPotential, div_eq_mul_inv, div_eq_mul_inv, inv_pow]
  rw [heq]
  simpa using h1.add h2

/-- Elementary two-sided bound for the complete Cauchy tail.

The frequently available extra hypothesis `y ≤ x` is deliberately absent:
the telescoping identities only need positivity of the shifted denominators.
-/
theorem cauchyTail_tsum_bounds
    {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) :
    y / x - y ^ 3 / x ^ 3 ≤ ∑' k : ℕ, cauchyTailTerm x y k ∧
      (∑' k : ℕ, cauchyTailTerm x y k) ≤ y / x + y / x ^ 2 := by
  have hsum := summable_cauchyTailTerm hx hy
  have hpartialLower (N : ℕ) :
      lowerPotential x y 0 - lowerPotential x y N ≤
        ∑ k ∈ Finset.range N, cauchyTailTerm x y k := by
    rw [← Finset.sum_range_sub' (lowerPotential x y)]
    exact Finset.sum_le_sum fun k _ ↦ lowerPotential_sub_succ_le hx hy k
  have hpartialUpper (N : ℕ) :
      (∑ k ∈ Finset.range N, cauchyTailTerm x y k) ≤
        upperPotential x y 0 - upperPotential x y N := by
    rw [← Finset.sum_range_sub' (upperPotential x y)]
    exact Finset.sum_le_sum fun k _ ↦
      cauchyTailTerm_le_upperPotential_sub_succ hx hy k
  have hpartial := hsum.hasSum.tendsto_sum_nat
  have hlowerLimit : Tendsto
      (fun N : ℕ ↦ lowerPotential x y 0 - lowerPotential x y N)
      atTop (nhds (lowerPotential x y 0)) := by
    simpa using tendsto_const_nhds.sub (tendsto_lowerPotential x y)
  have hupperLimit : Tendsto
      (fun N : ℕ ↦ upperPotential x y 0 - upperPotential x y N)
      atTop (nhds (upperPotential x y 0)) := by
    simpa using tendsto_const_nhds.sub (tendsto_upperPotential x y)
  have hlower : lowerPotential x y 0 ≤ ∑' k : ℕ, cauchyTailTerm x y k :=
    le_of_tendsto_of_tendsto hlowerLimit hpartial
      (Filter.Eventually.of_forall hpartialLower)
  have hupper : (∑' k : ℕ, cauchyTailTerm x y k) ≤
      upperPotential x y 0 :=
    le_of_tendsto_of_tendsto hpartial hupperLimit
      (Filter.Eventually.of_forall hpartialUpper)
  simpa [lowerPotential, upperPotential] using And.intro hlower hupper

end

end ArithmeticHodge.Analysis.YoshidaCauchyTailBounds
