import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

set_option autoImplicit false

open Finset Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFiniteWindowAssemblyObstructionStructural

/-!
# No fixed local window width forces global positivity

The earlier three-cell obstruction rules out assembly from two-cell principal
blocks.  The same defect persists at every fixed width, even for one
translation-invariant equicorrelation kernel.

For a proposed local width `m`, the quadratic below has diagonal coefficient
`m - 1` and every off-diagonal coefficient `-1`.  Cauchy--Schwarz makes every
restriction to at most `m` coordinates nonnegative.  On `m + 1` coordinates,
however, the all-ones vector has value `-(m + 1)`.

Thus increasing a Fejer/local-window argument to any fixed finite order cannot
by itself prove positivity of arbitrary cell chains.  A valid Bombieri
assembly needs an unbounded-width, whole-tail, or genuinely kernel-specific
mechanism.
-/

/-- The unnormalized equicorrelation quadratic with local width `m`.

Expanding the square shows diagonal coefficient `m - 1` and ordered
off-diagonal coefficient `-1`. -/
def fixedWidthEquicorrelationValue
    (m : ℕ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (m : ℝ) * ∑ i, x i ^ 2 - (∑ i, x i) ^ 2

/-- Cauchy--Schwarz controls every restriction whose number of coordinates is
at most the chosen local width. -/
theorem fixedWidthEquicorrelationValue_nonnegative_of_card_le
    {m n : ℕ} (hnm : n ≤ m) (x : Fin n → ℝ) :
    0 ≤ fixedWidthEquicorrelationValue m x := by
  have hsquares : 0 ≤ ∑ i, x i ^ 2 := by
    exact Finset.sum_nonneg fun i _hi ↦ sq_nonneg (x i)
  have hcs :
      (∑ i, x i) ^ 2 ≤ (n : ℝ) * ∑ i, x i ^ 2 := by
    simpa only [Finset.sum_const_zero, Finset.sum_filter,
      Finset.mem_univ, if_true, Finset.card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin n))) (f := x))
  have hcast : (n : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hnm
  have hscale :
      (n : ℝ) * ∑ i, x i ^ 2 ≤
        (m : ℝ) * ∑ i, x i ^ 2 :=
    mul_le_mul_of_nonneg_right hcast hsquares
  unfold fixedWidthEquicorrelationValue
  linarith

/-- In particular, every full window of the proposed width is nonnegative. -/
theorem fixedWidthEquicorrelationValue_local_nonnegative
    (m : ℕ) (x : Fin m → ℝ) :
    0 ≤ fixedWidthEquicorrelationValue m x :=
  fixedWidthEquicorrelationValue_nonnegative_of_card_le le_rfl x

/-- The all-ones vector on the first larger window. -/
def fixedWidthEquicorrelationOnes (m : ℕ) : Fin (m + 1) → ℝ :=
  fun _i ↦ 1

/-- The first window beyond the controlled width is already strictly
negative, by the exact amount `m + 1`. -/
theorem fixedWidthEquicorrelationValue_ones :
    ∀ m : ℕ,
      fixedWidthEquicorrelationValue m
          (fixedWidthEquicorrelationOnes m) = -((m + 1 : ℕ) : ℝ) := by
  intro m
  simp [fixedWidthEquicorrelationValue,
    fixedWidthEquicorrelationOnes]
  ring

/-- For every fixed finite localization width there is a larger negative
block, although all blocks up through that width are nonnegative. -/
theorem exists_fixedWidth_local_nonnegative_global_negative
    (m : ℕ) :
    (∀ {n : ℕ}, n ≤ m → ∀ x : Fin n → ℝ,
      0 ≤ fixedWidthEquicorrelationValue m x) ∧
    ∃ x : Fin (m + 1) → ℝ,
      fixedWidthEquicorrelationValue m x < 0 := by
  constructor
  · intro n hn x
    exact fixedWidthEquicorrelationValue_nonnegative_of_card_le hn x
  · refine ⟨fixedWidthEquicorrelationOnes m, ?_⟩
    rw [fixedWidthEquicorrelationValue_ones]
    apply neg_lt_zero.mpr
    exact_mod_cast Nat.zero_lt_succ m

end ArithmeticHodge.Analysis.MultiplicativeWeilFiniteWindowAssemblyObstructionStructural
