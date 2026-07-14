import ArithmeticHodge.Analysis.SparseCongruenceCertificate

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.RobustCongruenceCertificate

noncomputable section

open SparseCongruenceCertificate
open WeightedDiagonalDominance

/-!
# Robust positive-definiteness certificates around a rational center

A well-conditioned rational congruence can turn a dense positive matrix into
a diagonally dominant one.  This theorem propagates a uniform entrywise error
through that congruence and leaves only exact weighted diagonal-dominance
inequalities to check.
-/

/-- A weighted-diagonally-dominant congruence of a nearby center certifies the
true Hermitian matrix.  The row `L¹` factors are the exact amplification of a
uniform entrywise error through `P * A * Pᵀ`. -/
theorem posDef_of_robust_congruence
    {n : Type*} [Fintype n] [DecidableEq n]
    (A P C : Matrix n n ℝ)
    (hA : A.IsHermitian) (hP : IsUnit P)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hclose : ∀ i j, |A i j - C i j| ≤ ε)
    (d w : n → ℝ) (r : n → n → ℝ)
    (hw : ∀ i, 0 < w i)
    (hr0 : ∀ i j, 0 ≤ r i j)
    (hrsymm : ∀ i j, r i j = r j i)
    (hdiag : ∀ i,
      d i ≤ (P * C * P.transpose) i i -
        ε * (∑ k, |P i k|) ^ 2)
    (hoff : ∀ i j, i ≠ j →
      |(P * C * P.transpose) i j| +
          ε * (∑ k, |P i k|) * (∑ l, |P j l|) ≤ r i j)
    (hdom : ∀ i,
      (∑ j ∈ Finset.univ.erase i, r i j * w j) < d i * w i) :
    A.PosDef := by
  let B := P * A * P.transpose
  let Bc := P * C * P.transpose
  have hBherm : B.IsHermitian := by
    dsimp only [B]
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (isHermitian_mul_mul_conjTranspose P hA)
  have herror : ∀ i j,
      |B i j - Bc i j| ≤
        ε * (∑ k, |P i k|) * (∑ l, |P j l|) := by
    intro i j
    exact congruence_sub_center_entry_abs_le P A C hε hclose i j
  have hBdiag : ∀ i, d i ≤ B i i := by
    intro i
    have herr := herror i i
    have hlower : Bc i i -
        ε * (∑ k, |P i k|) * (∑ l, |P i l|) ≤ B i i := by
      have hneg := neg_le_of_abs_le herr
      dsimp only [B, Bc] at hneg ⊢
      linarith
    have hsq :
        ε * (∑ k, |P i k|) ^ 2 =
          ε * (∑ k, |P i k|) * (∑ l, |P i l|) := by ring
    have hi := hdiag i
    rw [hsq] at hi
    exact hi.trans hlower
  have hBoff : ∀ i j, i ≠ j → |B i j| ≤ r i j := by
    intro i j hij
    have htriangle : |B i j| ≤ |B i j - Bc i j| + |Bc i j| := by
      calc
        |B i j| = |(B i j - Bc i j) + Bc i j| := by congr 1; ring
        _ ≤ |B i j - Bc i j| + |Bc i j| := abs_add_le _ _
    calc
      |B i j| ≤ |B i j - Bc i j| + |Bc i j| := htriangle
      _ ≤ ε * (∑ k, |P i k|) * (∑ l, |P j l|) + |Bc i j| :=
        add_le_add (herror i j) le_rfl
      _ = |Bc i j| +
          ε * (∑ k, |P i k|) * (∑ l, |P j l|) := by ring
      _ ≤ r i j := hoff i j hij
  have hB : B.PosDef :=
    posDef_of_weighted_entry_bounds B hBherm d w r hw hr0 hrsymm
      hBdiag hBoff hdom
  apply hP.posDef_star_right_conjugate_iff.mp
  simpa only [B, conjTranspose_eq_transpose_of_trivial] using hB

end

end ArithmeticHodge.Analysis.RobustCongruenceCertificate
