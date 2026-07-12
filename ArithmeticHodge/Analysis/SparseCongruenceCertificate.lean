import ArithmeticHodge.Analysis.WeightedDiagonalDominance
import Mathlib.LinearAlgebra.Matrix.Block

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.SparseCongruenceCertificate

abbrev SparseRow (n : Type*) := n →₀ ℚ

def matrixOfSparseRows {n : Type*} [DecidableEq n]
    (rows : n → SparseRow n) : Matrix n n ℚ :=
  fun i j ↦ rows i j

def SparseRowsLowerTriangular {n : Type*} [Preorder n]
    (rows : n → SparseRow n) : Prop :=
  ∀ i j, rows i j ≠ 0 → j ≤ i

def sparseCongruenceEntry {n : Type*} [DecidableEq n]
    (rows : n → SparseRow n) (C : Matrix n n ℚ) (i j : n) : ℚ :=
  (rows i).sum fun k pik ↦
    (rows j).sum fun l pjl ↦ pik * C k l * pjl

theorem sparseCongruenceEntry_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (rows : n → SparseRow n) (C : Matrix n n ℚ) (i j : n) :
    sparseCongruenceEntry rows C i j =
      (matrixOfSparseRows rows * C *
        (matrixOfSparseRows rows).transpose) i j := by
  classical
  calc
    sparseCongruenceEntry rows C i j =
        ∑ k, ∑ l, rows i k * C k l * rows j l := by
      simp [sparseCongruenceEntry, Finsupp.sum_fintype]
    _ = ∑ l, ∑ k, rows i k * C k l * rows j l :=
      Finset.sum_comm
    _ = (matrixOfSparseRows rows * C *
        (matrixOfSparseRows rows).transpose) i j := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, matrixOfSparseRows]
      apply Finset.sum_congr rfl
      intro l _hl
      rw [Finset.sum_mul]

theorem congruence_sub_center_entry_abs_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (P A C : Matrix n n ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ k l, |A k l - C k l| ≤ ε) (i j : n) :
    |(P * A * P.transpose) i j - (P * C * P.transpose) i j| ≤
      ε * (∑ k, |P i k|) * (∑ l, |P j l|) := by
  classical
  have hdiff :
      (P * A * P.transpose) i j - (P * C * P.transpose) i j =
        ∑ l, ∑ k, P i k * (A k l - C k l) * P j l := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _hl
    rw [← sub_mul, ← Finset.sum_sub_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  rw [hdiff]
  calc
    |∑ l, ∑ k, P i k * (A k l - C k l) * P j l| ≤
        ∑ l, |∑ k, P i k * (A k l - C k l) * P j l| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, ∑ k, |P i k * (A k l - C k l) * P j l| := by
      exact Finset.sum_le_sum fun l _hl ↦
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, ∑ k, |P i k| * ε * |P j l| := by
      apply Finset.sum_le_sum
      intro l _hl
      apply Finset.sum_le_sum
      intro k _hk
      rw [abs_mul, abs_mul]
      have hmiddle :
          |A k l - C k l| * |P i k| ≤ ε * |P i k| :=
        mul_le_mul (hclose k l) le_rfl (abs_nonneg (P i k)) hε
      have hweighted := mul_le_mul_of_nonneg_right hmiddle
        (abs_nonneg (P j l))
      simpa [mul_comm, mul_left_comm, mul_assoc] using hweighted
    _ = ∑ l, ((∑ k, |P i k|) * ε) * |P j l| := by
      apply Finset.sum_congr rfl
      intro l _hl
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = ((∑ k, |P i k|) * ε) * (∑ l, |P j l|) := by
      rw [Finset.mul_sum]
    _ = ε * (∑ k, |P i k|) * (∑ l, |P j l|) := by
      ring

theorem matrixOfSparseRows_blockTriangular
    {n : Type*} [Fintype n] [LinearOrder n]
    (rows : n → SparseRow n) (hlower : SparseRowsLowerTriangular rows) :
    (matrixOfSparseRows rows).BlockTriangular OrderDual.toDual := by
  intro i j hij
  change i < j at hij
  simp only [matrixOfSparseRows]
  by_contra hne
  exact (not_lt_of_ge (hlower i j hne)) hij

theorem det_matrixOfSparseRows
    {n : Type*} [Fintype n] [LinearOrder n]
    (rows : n → SparseRow n) (hlower : SparseRowsLowerTriangular rows) :
    (matrixOfSparseRows rows).det = ∏ i, rows i i := by
  exact Matrix.det_of_lowerTriangular _
    (matrixOfSparseRows_blockTriangular rows hlower)

theorem matrixOfSparseRows_isUnit
    {n : Type*} [Fintype n] [LinearOrder n]
    (rows : n → SparseRow n)
    (hlower : SparseRowsLowerTriangular rows)
    (hdiag : ∀ i, rows i i ≠ 0) :
    IsUnit (matrixOfSparseRows rows) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [det_matrixOfSparseRows rows hlower]
  exact isUnit_iff_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun i _hi ↦ hdiag i)

end ArithmeticHodge.Analysis.SparseCongruenceCertificate
