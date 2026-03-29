/-
  Helper: Zero summability and stuttered enumeration for finite-order entire functions.

  Extracted to break the circular import:
  Order → ZetaProduct → Hadamard → WeierstraßProduct.

  Contains:
  1. stutteredEnum — multiplicity-aware zero enumeration via Nat.unpair
  2. finite_order_zero_summable_weighted — sorry corresponding to Order.lean:452
     (Jensen's formula + Abel summation, counting zeros with multiplicity)
-/

import ArithmeticHodge.Analysis.EntireFunction.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Nat.Pairing

open Complex

namespace ArithmeticHodge.Analysis.EntireFunction

-- ============================================================
-- Stuttered Enumeration
-- ============================================================

/-- Stuttered enumeration: given `a₀ : ℕ → ℂ` (distinct elements) and
    `mult : ℕ → ℕ` (multiplicities), builds `a : ℕ → ℂ` where `a₀ k`
    appears `mult k` times. Uses `Nat.unpair` to decode `n` into `(k, j)`;
    returns `a₀ k` if `j < mult k`, else `0` (padding). -/
noncomputable def stutteredEnum (a₀ : ℕ → ℂ) (mult : ℕ → ℕ) : ℕ → ℂ :=
  fun n => if n.unpair.2 < mult n.unpair.1 then a₀ n.unpair.1 else 0

@[simp]
theorem stutteredEnum_apply (a₀ : ℕ → ℂ) (mult : ℕ → ℕ) (n : ℕ) :
    stutteredEnum a₀ mult n =
      if n.unpair.2 < mult n.unpair.1 then a₀ n.unpair.1 else 0 := rfl

theorem stutteredEnum_pair_lt {a₀ : ℕ → ℂ} {mult : ℕ → ℕ} {k j : ℕ}
    (h : j < mult k) :
    stutteredEnum a₀ mult (Nat.pair k j) = a₀ k := by
  simp [stutteredEnum, Nat.unpair_pair, h]

theorem stutteredEnum_pair_ge {a₀ : ℕ → ℂ} {mult : ℕ → ℕ} {k j : ℕ}
    (h : mult k ≤ j) :
    stutteredEnum a₀ mult (Nat.pair k j) = 0 := by
  simp [stutteredEnum, Nat.unpair_pair, not_lt.mpr h]

/-- Nonzero entries of stutteredEnum come from nonzero entries of a₀. -/
theorem stutteredEnum_ne_zero_imp {a₀ : ℕ → ℂ} {mult : ℕ → ℕ} {n : ℕ}
    (h : stutteredEnum a₀ mult n ≠ 0) :
    n.unpair.2 < mult n.unpair.1 ∧ a₀ n.unpair.1 ≠ 0 := by
  simp only [stutteredEnum_apply] at h
  split_ifs at h with hlt
  · exact ⟨hlt, h⟩
  · exact absurd rfl h

/-- Every zero a₀(k) with positive multiplicity is covered. -/
theorem stutteredEnum_covers {a₀ : ℕ → ℂ} {mult : ℕ → ℕ} {k : ℕ}
    (hm : 0 < mult k) :
    ∃ n, stutteredEnum a₀ mult n = a₀ k :=
  ⟨Nat.pair k 0, stutteredEnum_pair_lt hm⟩

/-- If a₀ maps nonzero entries to zeros of f₁, so does stutteredEnum. -/
theorem stutteredEnum_maps_zeros {a₀ : ℕ → ℂ} {mult : ℕ → ℕ}
    {f₁ : ℂ → ℂ} (h_zeros : ∀ k, a₀ k ≠ 0 → f₁ (a₀ k) = 0)
    {n : ℕ} (hn : stutteredEnum a₀ mult n ≠ 0) :
    f₁ (stutteredEnum a₀ mult n) = 0 := by
  have ⟨hlt, hne⟩ := stutteredEnum_ne_zero_imp hn
  simp only [stutteredEnum_apply, hlt, ite_true]
  exact h_zeros _ hne

-- ============================================================
-- Summability of stuttered enumeration (combinatorial transfer)
-- ============================================================

/-- Summability of stutteredEnum from multiplicity-weighted summability.
    This is the combinatorial transfer: if Σ_k mult(k) · ‖a₀(k)‖⁻¹^s converges,
    then Σ_n ‖stutteredEnum(n)‖⁻¹^s converges.

    Proof strategy: transfer to ℕ × ℕ via Nat.pairEquiv, then use
    summable_prod_of_nonneg to decompose into inner (finite) and outer sums. -/
theorem summable_stutteredEnum_of_weighted {a₀ : ℕ → ℂ} {mult : ℕ → ℕ} {s : ℝ}
    (hs : 0 < s)
    (hw : Summable (fun k => (mult k : ℝ) * ‖a₀ k‖⁻¹ ^ s)) :
    Summable (fun n => ‖stutteredEnum a₀ mult n‖⁻¹ ^ s) := by
  -- Define the product-indexed version
  set g : ℕ × ℕ → ℝ := fun p => if p.2 < mult p.1 then ‖a₀ p.1‖⁻¹ ^ s else 0
  -- Step 1: Show the ℕ-indexed function equals g ∘ Nat.pairEquiv.symm
  have heq : ∀ n, ‖stutteredEnum a₀ mult n‖⁻¹ ^ s = g (Nat.unpair n) := by
    intro n
    simp only [stutteredEnum_apply, g]
    split_ifs with hlt
    · rfl
    · rw [norm_zero, inv_zero, Real.zero_rpow (ne_of_gt hs)]
  -- Step 2: Summability on ℕ ↔ summability on ℕ × ℕ via pairEquiv
  rw [show (fun n => ‖stutteredEnum a₀ mult n‖⁻¹ ^ s) = g ∘ Nat.pairEquiv.symm from
    funext fun n => heq n]
  rw [Nat.pairEquiv.symm.summable_iff]
  -- Step 3: Summability on ℕ × ℕ via summable_prod_of_nonneg
  have hg_nn : (0 : ℕ × ℕ → ℝ) ≤ g := by
    intro ⟨k, j⟩
    simp only [Pi.zero_apply, g]
    split_ifs
    · exact Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _
    · exact le_refl 0
  refine (summable_prod_of_nonneg hg_nn).mpr ⟨fun k => ?_, ?_⟩
  · -- Inner sum for each k: finite (only mult k terms), hence summable
    apply summable_of_ne_finset_zero (s := Finset.range (mult k))
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    exact if_neg (not_lt.mpr hj)
  · -- Outer sum: ∑' j, g(k,j) = mult(k) · ‖a₀(k)‖⁻¹^s, summable by hypothesis
    have htsum : ∀ k, ∑' j, g (k, j) = (mult k : ℝ) * ‖a₀ k‖⁻¹ ^ s := by
      intro k
      rw [tsum_eq_sum (s := Finset.range (mult k))
        (by intro j hj; simp [Finset.mem_range, not_lt] at hj; exact if_neg (not_lt.mpr hj))]
      simp only [g]
      rw [Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.mp hj))]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp_rw [htsum]
    exact hw

-- ============================================================
-- Deep sorry: multiplicity-weighted summability for finite-order functions
-- ============================================================

/-- For a finite-order entire function f with order ρ and genus p = ⌊ρ⌋,
    the multiplicity-weighted series Σ mult(z_k) · ‖z_k‖^{-(p+1)} converges
    over the nonzero zeros, where mult(z_k) = analyticOrderNatAt f z_k.

    This follows from Jensen's formula (which gives n(r) = O(r^{ρ+ε}) counting
    with multiplicity) and Abel summation. Same gap as Order.lean:452. -/
theorem finite_order_zero_summable_weighted (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) (hfin : HasFiniteOrder f)
    (a₀ : ℕ → ℂ) (ha₀ : ∀ k, a₀ k ≠ 0 → f (a₀ k) = 0)
    (mult : ℕ → ℕ) (hmult_zero : ∀ k, a₀ k = 0 → mult k = 0) :
    let p := Nat.floor (entireOrder f).toReal
    Summable (fun k => (mult k : ℝ) * ‖a₀ k‖⁻¹ ^ ((p : ℝ) + 1)) :=
  finite_order_zero_summable_aux f hf hf_ne hfin a₀ ha₀ mult hmult_zero

end ArithmeticHodge.Analysis.EntireFunction
