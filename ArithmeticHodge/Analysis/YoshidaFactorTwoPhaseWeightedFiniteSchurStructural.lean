import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseWeightedFiniteSchurStructural

noncomputable section

/-!
# A finite square-root-free Schur budget

The `P6/P7` border has four low--residual cells, while adjoining `P8`
creates two more.  The scalar argument does not depend on that cardinality.
This file records the finite weighted Cauchy estimate once, using
Sedrakyan's inequality rather than an expansion into pairwise squares.
-/

/-- A finite family of normalized square bounds closes under one total
weight budget.  The cell masses `X i` need not have any particular product
form; only their nonnegativity and aggregate bound are used. -/
theorem finset_schur_of_normalized_sq_bounds
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c z X : ι → ℝ) (A : ℝ)
    (hc : ∀ i ∈ s, 0 < c i)
    (hbudget : (∑ i ∈ s, c i) ≤ 1)
    (hX : ∀ i ∈ s, 0 ≤ X i)
    (hz : ∀ i ∈ s, z i ^ 2 ≤ c i * X i)
    (haggregate : (∑ i ∈ s, X i) ≤ A) :
    (∑ i ∈ s, z i) ^ 2 ≤ A := by
  by_cases hs : s.Nonempty
  · have hC : 0 < ∑ i ∈ s, c i := Finset.sum_pos hc hs
    have htitu := Finset.sq_sum_div_le_sum_sq_div s z hc
    have hweighted :
        (∑ i ∈ s, z i) ^ 2 ≤
          (∑ i ∈ s, c i) * (∑ i ∈ s, z i ^ 2 / c i) := by
      have := (div_le_iff₀ hC).1 htitu
      simpa only [mul_comm] using this
    have hrows :
        (∑ i ∈ s, z i ^ 2 / c i) ≤ ∑ i ∈ s, X i := by
      apply Finset.sum_le_sum
      intro i hi
      apply (div_le_iff₀ (hc i hi)).2
      simpa only [mul_comm] using hz i hi
    have hsumX : 0 ≤ ∑ i ∈ s, X i :=
      Finset.sum_nonneg fun i hi ↦ hX i hi
    calc
      (∑ i ∈ s, z i) ^ 2 ≤
          (∑ i ∈ s, c i) * (∑ i ∈ s, z i ^ 2 / c i) := hweighted
      _ ≤ (∑ i ∈ s, c i) * (∑ i ∈ s, X i) :=
        mul_le_mul_of_nonneg_left hrows hC.le
      _ ≤ 1 * (∑ i ∈ s, X i) :=
        mul_le_mul_of_nonneg_right hbudget hsumX
      _ = ∑ i ∈ s, X i := one_mul _
      _ ≤ A := haggregate
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simpa using haggregate

/-- The same finite Schur estimate with the actual total weight retained.
This is the form to use when the normalized cell weights sum strictly below
one and the unused fraction is needed by a second coupled family. -/
theorem finset_schur_of_normalized_sq_bounds_at_budget
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c z X : ι → ℝ) (C A : ℝ)
    (hc : ∀ i ∈ s, 0 < c i)
    (hbudget : (∑ i ∈ s, c i) ≤ C)
    (hC : 0 ≤ C)
    (hX : ∀ i ∈ s, 0 ≤ X i)
    (hz : ∀ i ∈ s, z i ^ 2 ≤ c i * X i)
    (haggregate : (∑ i ∈ s, X i) ≤ A) :
    (∑ i ∈ s, z i) ^ 2 ≤ C * A := by
  by_cases hs : s.Nonempty
  · have hsumC : 0 < ∑ i ∈ s, c i := Finset.sum_pos hc hs
    have htitu := Finset.sq_sum_div_le_sum_sq_div s z hc
    have hweighted :
        (∑ i ∈ s, z i) ^ 2 ≤
          (∑ i ∈ s, c i) * (∑ i ∈ s, z i ^ 2 / c i) := by
      have := (div_le_iff₀ hsumC).1 htitu
      simpa only [mul_comm] using this
    have hrows :
        (∑ i ∈ s, z i ^ 2 / c i) ≤ ∑ i ∈ s, X i := by
      apply Finset.sum_le_sum
      intro i hi
      apply (div_le_iff₀ (hc i hi)).2
      simpa only [mul_comm] using hz i hi
    have hsumX : 0 ≤ ∑ i ∈ s, X i :=
      Finset.sum_nonneg fun i hi ↦ hX i hi
    calc
      (∑ i ∈ s, z i) ^ 2 ≤
          (∑ i ∈ s, c i) * (∑ i ∈ s, z i ^ 2 / c i) := hweighted
      _ ≤ (∑ i ∈ s, c i) * (∑ i ∈ s, X i) :=
        mul_le_mul_of_nonneg_left hrows hsumC.le
      _ ≤ C * (∑ i ∈ s, X i) :=
        mul_le_mul_of_nonneg_right hbudget hsumX
      _ ≤ C * A := mul_le_mul_of_nonneg_left haggregate hC
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    have hA : 0 ≤ A := by simpa using haggregate
    simpa using mul_nonneg hC hA

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseWeightedFiniteSchurStructural
