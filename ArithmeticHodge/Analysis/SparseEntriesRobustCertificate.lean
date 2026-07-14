import ArithmeticHodge.Analysis.RobustCongruenceCertificate
import ArithmeticHodge.Analysis.SparseEntriesCertificate
import Mathlib.LinearAlgebra.Matrix.Symmetric

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.SparseEntriesRobustCertificate

noncomputable section

open RobustCongruenceCertificate
open SparseCongruenceCertificate
open SparseEntriesCertificate

/-!
# Robust congruence certificates from pair-list sparse rows

This file specializes `posDef_of_robust_congruence` to the kernel-computable
`SparseEntries` representation.  All certificate data remain rational: the
center matrix, entrywise error, row budgets, weights, and weighted-dominance
inequality.  Only the final application casts them to the real matrices used
by `Matrix.PosDef`.
-/

/-- Rational matrix whose rows are accumulated from pair-list payloads. -/
def matrixOfSparseEntries
    {n : Type*} [DecidableEq n]
    (entries : n → SparseEntries n) : Matrix n n ℚ :=
  matrixOfSparseRows fun i ↦ rowOfEntries (entries i)

/-- Real cast of `matrixOfSparseEntries`, used as the congruence matrix. -/
def realMatrixOfSparseEntries
    {n : Type*} [Fintype n] [DecidableEq n]
    (entries : n → SparseEntries n) : Matrix n n ℝ :=
  (Rat.castHom ℝ).mapMatrix (matrixOfSparseEntries entries)

@[simp] theorem matrixOfSparseEntries_apply
    {n : Type*} [DecidableEq n]
    (entries : n → SparseEntries n) (i j : n) :
    matrixOfSparseEntries entries i j = entriesValue (entries i) j :=
  rfl

@[simp] theorem realMatrixOfSparseEntries_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (entries : n → SparseEntries n) (i j : n) :
    realMatrixOfSparseEntries entries i j =
      (entriesValue (entries i) j : ℝ) :=
  rfl

/-- The dense rational congruence entry agrees with direct pair-list
evaluation, including when a payload repeats an index. -/
theorem matrixOfSparseEntries_congruence_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (entries : n → SparseEntries n) (C : Matrix n n ℚ) (i j : n) :
    (matrixOfSparseEntries entries * C *
        (matrixOfSparseEntries entries).transpose) i j =
      entriesCongruence (entries i) (entries j) C := by
  simpa only [matrixOfSparseEntries] using
    (sparseCongruenceEntry_eq
        (fun k ↦ rowOfEntries (entries k)) C i j).symm.trans
      (sparseCongruenceEntry_rowOfEntries entries C i j)

/-- Casting the sparse congruence to `ℝ` commutes with its exact pair-list
evaluation. -/
theorem realMatrixOfSparseEntries_congruence_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (entries : n → SparseEntries n) (C : Matrix n n ℚ) (i j : n) :
    (realMatrixOfSparseEntries entries *
        (Rat.castHom ℝ).mapMatrix C *
        (realMatrixOfSparseEntries entries).transpose) i j =
      ((entriesCongruence (entries i) (entries j) C : ℚ) : ℝ) := by
  let Pq := matrixOfSparseEntries entries
  have hq :
      (Pq * C * Pq.transpose) i j =
        entriesCongruence (entries i) (entries j) C := by
    simpa only [Pq] using
      matrixOfSparseEntries_congruence_apply entries C i j
  calc
    (realMatrixOfSparseEntries entries *
        (Rat.castHom ℝ).mapMatrix C *
        (realMatrixOfSparseEntries entries).transpose) i j =
        ((Rat.castHom ℝ).mapMatrix (Pq * C * Pq.transpose)) i j := by
      simp only [Pq, realMatrixOfSparseEntries, map_mul]
      rfl
    _ = (((Pq * C * Pq.transpose) i j : ℚ) : ℝ) := rfl
    _ = ((entriesCongruence (entries i) (entries j) C : ℚ) : ℝ) :=
      congrArg (fun q : ℚ ↦ (q : ℝ)) hq

/-- Pair-list `L¹` budgets are always nonnegative. -/
theorem entriesL1_nonneg
    {n : Type*} (xs : SparseEntries n) : 0 ≤ entriesL1 xs := by
  induction xs with
  | nil => simp [entriesL1]
  | cons p xs ih =>
      rcases p with ⟨i, q⟩
      simpa only [entriesL1] using add_nonneg (abs_nonneg q) ih

/-- The real dense `L¹` norm of a cast sparse row is bounded by its exact
rational pair-list budget. -/
theorem realMatrixOfSparseEntries_row_l1_le_entriesL1
    {n : Type*} [Fintype n] [DecidableEq n]
    (entries : n → SparseEntries n) (i : n) :
    (∑ j, |realMatrixOfSparseEntries entries i j|) ≤
      ((entriesL1 (entries i) : ℚ) : ℝ) := by
  have hq := rowOfEntries_dense_l1_le_entriesL1 (entries i)
  simp only [rowOfEntries_apply] at hq
  simp only [realMatrixOfSparseEntries_apply]
  exact_mod_cast hq

/-- Lower triangularity of the accumulated pair-list rows and a nonzero
accumulated diagonal make the rational sparse matrix invertible. -/
theorem matrixOfSparseEntries_isUnit
    {n : Type*} [Fintype n] [LinearOrder n]
    (entries : n → SparseEntries n)
    (hlower : ∀ i j, entriesValue (entries i) j ≠ 0 → j ≤ i)
    (hdiag : ∀ i, entriesValue (entries i) i ≠ 0) :
    IsUnit (matrixOfSparseEntries entries) := by
  unfold matrixOfSparseEntries
  apply matrixOfSparseRows_isUnit
  · intro i j hnonzero
    exact hlower i j (by
      simpa only [rowOfEntries_apply] using hnonzero)
  · intro i
    simpa only [rowOfEntries_apply] using hdiag i

/-- A source-index check is a conservative, readily computable way to prove
the accumulated lower-triangular condition, even when duplicate entries may
cancel. -/
theorem matrixOfSparseEntries_isUnit_of_source_lower
    {n : Type*} [Fintype n] [LinearOrder n]
    (entries : n → SparseEntries n)
    (hlower : ∀ i j, j ∈ (entries i).map Prod.fst → j ≤ i)
    (hdiag : ∀ i, entriesValue (entries i) i ≠ 0) :
    IsUnit (matrixOfSparseEntries entries) := by
  apply matrixOfSparseEntries_isUnit entries _ hdiag
  intro i j hnonzero
  exact hlower i j
    (mem_map_fst_of_rowOfEntries_apply_ne_zero (by
      simpa only [rowOfEntries_apply] using hnonzero))

/-- Real invertibility follows functorially from the exact rational sparse
matrix certificate. -/
theorem realMatrixOfSparseEntries_isUnit
    {n : Type*} [Fintype n] [LinearOrder n]
    (entries : n → SparseEntries n)
    (hlower : ∀ i j, entriesValue (entries i) j ≠ 0 → j ≤ i)
    (hdiag : ∀ i, entriesValue (entries i) i ≠ 0) :
    IsUnit (realMatrixOfSparseEntries entries) := by
  exact (matrixOfSparseEntries_isUnit entries hlower hdiag).map
    (Rat.castHom ℝ).mapMatrix

theorem realMatrixOfSparseEntries_isUnit_of_source_lower
    {n : Type*} [Fintype n] [LinearOrder n]
    (entries : n → SparseEntries n)
    (hlower : ∀ i j, j ∈ (entries i).map Prod.fst → j ≤ i)
    (hdiag : ∀ i, entriesValue (entries i) i ≠ 0) :
    IsUnit (realMatrixOfSparseEntries entries) := by
  exact (matrixOfSparseEntries_isUnit_of_source_lower
    entries hlower hdiag).map (Rat.castHom ℝ).mapMatrix

/-- Symmetry of the rational center passes through pair-list congruence. -/
theorem entriesCongruence_symm_of_isSymm
    {n : Type*} [Fintype n] [DecidableEq n]
    (entries : n → SparseEntries n) (C : Matrix n n ℚ)
    (hC : C.IsSymm) (i j : n) :
    entriesCongruence (entries i) (entries j) C =
      entriesCongruence (entries j) (entries i) C := by
  let Pq := matrixOfSparseEntries entries
  have hChermitian : C.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro k l
    simpa using hC.apply k l
  have hcongruence : (Pq * C * Pq.transpose).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      isHermitian_mul_mul_conjTranspose Pq hChermitian
  calc
    entriesCongruence (entries i) (entries j) C =
        (Pq * C * Pq.transpose) i j := by
      symm
      simpa only [Pq] using
        matrixOfSparseEntries_congruence_apply entries C i j
    _ = (Pq * C * Pq.transpose) j i := by
      simpa using hcongruence.apply j i
    _ = entriesCongruence (entries j) (entries i) C := by
      simpa only [Pq] using
        matrixOfSparseEntries_congruence_apply entries C j i

/-- Robust off-diagonal radius computed entirely in `ℚ`. -/
def entriesRobustRadius
    {n : Type*} (entries : n → SparseEntries n)
    (C : Matrix n n ℚ) (epsilon : ℚ) (i j : n) : ℚ :=
  |entriesCongruence (entries i) (entries j) C| +
    epsilon * entriesL1 (entries i) * entriesL1 (entries j)

/-- Robust transformed diagonal lower bound computed entirely in `ℚ`. -/
def entriesRobustDiagonalLower
    {n : Type*} (entries : n → SparseEntries n)
    (C : Matrix n n ℚ) (epsilon : ℚ) (i : n) : ℚ :=
  entriesCongruence (entries i) (entries i) C -
    epsilon * entriesL1 (entries i) ^ 2

theorem entriesRobustRadius_nonneg
    {n : Type*} (entries : n → SparseEntries n)
    (C : Matrix n n ℚ) {epsilon : ℚ} (hepsilon : 0 ≤ epsilon)
    (i j : n) :
    0 ≤ entriesRobustRadius entries C epsilon i j := by
  unfold entriesRobustRadius
  exact add_nonneg (abs_nonneg _)
    (mul_nonneg
      (mul_nonneg hepsilon (entriesL1_nonneg (entries i)))
      (entriesL1_nonneg (entries j)))

theorem entriesRobustRadius_symm
    {n : Type*} [Fintype n] [DecidableEq n]
    (entries : n → SparseEntries n) (C : Matrix n n ℚ)
    (hC : C.IsSymm) (epsilon : ℚ) (i j : n) :
    entriesRobustRadius entries C epsilon i j =
      entriesRobustRadius entries C epsilon j i := by
  unfold entriesRobustRadius
  rw [entriesCongruence_symm_of_isSymm entries C hC i j]
  ring

/-!
## Exact rational sparse-entry robust certificate
-/

/-- An explicitly invertible pair-list congruence, a symmetric rational
center, and one exact rational weighted-dominance inequality certify the
nearby real Hermitian matrix as positive definite.

This is the order-independent core theorem.  It requires only a finite index
type with decidable equality; callers whose index has no canonical linear
order can supply any independently proved real `IsUnit` certificate. -/
theorem posDef_of_sparseEntries_robust_congruence_of_isUnit
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ)
    (entries : n → SparseEntries n)
    (C : Matrix n n ℚ) (epsilon : ℚ) (weights : n → ℚ)
    (hA : A.IsHermitian) (hC : C.IsSymm)
    (hP : IsUnit (realMatrixOfSparseEntries entries))
    (hepsilon : 0 ≤ epsilon)
    (hclose : ∀ i j,
      |A i j - (C i j : ℝ)| ≤ (epsilon : ℝ))
    (hweights : ∀ i, 0 < weights i)
    (hdominance : ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius entries C epsilon i j * weights j) <
        entriesRobustDiagonalLower entries C epsilon i * weights i) :
    A.PosDef := by
  let P : Matrix n n ℝ := realMatrixOfSparseEntries entries
  let Cr : Matrix n n ℝ := (Rat.castHom ℝ).mapMatrix C
  have hPReal : IsUnit P := by
    simpa only [P] using hP
  have hepsilonReal : (0 : ℝ) ≤ (epsilon : ℝ) := by
    exact_mod_cast hepsilon
  have hcloseReal : ∀ i j, |A i j - Cr i j| ≤ (epsilon : ℝ) := by
    intro i j
    simpa only [Cr, RingHom.mapMatrix_apply] using hclose i j
  have hcenter : ∀ i j,
      (P * Cr * P.transpose) i j =
        ((entriesCongruence (entries i) (entries j) C : ℚ) : ℝ) := by
    intro i j
    dsimp only [P, Cr]
    exact realMatrixOfSparseEntries_congruence_apply entries C i j
  have hrowL1 : ∀ i,
      (∑ j, |P i j|) ≤ ((entriesL1 (entries i) : ℚ) : ℝ) := by
    intro i
    dsimp only [P]
    exact realMatrixOfSparseEntries_row_l1_le_entriesL1 entries i
  have hweightsReal : ∀ i, (0 : ℝ) < (weights i : ℝ) := by
    intro i
    exact (Rat.cast_pos (K := ℝ)).2 (hweights i)
  have hradiusNonneg : ∀ i j,
      (0 : ℝ) ≤
        (entriesRobustRadius entries C epsilon i j : ℝ) := by
    intro i j
    exact_mod_cast entriesRobustRadius_nonneg entries C hepsilon i j
  have hradiusSymm : ∀ i j,
      (entriesRobustRadius entries C epsilon i j : ℝ) =
        (entriesRobustRadius entries C epsilon j i : ℝ) := by
    intro i j
    exact_mod_cast entriesRobustRadius_symm entries C hC epsilon i j
  have hdiagonalReal : ∀ i,
      (entriesRobustDiagonalLower entries C epsilon i : ℝ) ≤
        (P * Cr * P.transpose) i i -
          (epsilon : ℝ) * (∑ j, |P i j|) ^ 2 := by
    intro i
    have hsumNonneg : (0 : ℝ) ≤ ∑ j, |P i j| :=
      Finset.sum_nonneg fun j _hj ↦ abs_nonneg (P i j)
    have hbudgetNonneg :
        (0 : ℝ) ≤ (entriesL1 (entries i) : ℝ) := by
      exact_mod_cast entriesL1_nonneg (entries i)
    have hsquare :
        (∑ j, |P i j|) ^ 2 ≤ (entriesL1 (entries i) : ℝ) ^ 2 :=
      (sq_le_sq₀ hsumNonneg hbudgetNonneg).2 (hrowL1 i)
    have hscaled := mul_le_mul_of_nonneg_left hsquare hepsilonReal
    rw [hcenter i i]
    unfold entriesRobustDiagonalLower
    push_cast
    exact sub_le_sub_left hscaled _
  have hoffDiagonalReal : ∀ i j, i ≠ j →
      |(P * Cr * P.transpose) i j| +
          (epsilon : ℝ) * (∑ k, |P i k|) * (∑ l, |P j l|) ≤
        (entriesRobustRadius entries C epsilon i j : ℝ) := by
    intro i j _hij
    have hsumJNonneg : (0 : ℝ) ≤ ∑ l, |P j l| :=
      Finset.sum_nonneg fun l _hl ↦ abs_nonneg (P j l)
    have hbudgetINonneg :
        (0 : ℝ) ≤ (entriesL1 (entries i) : ℝ) := by
      exact_mod_cast entriesL1_nonneg (entries i)
    have hproduct :
        (∑ k, |P i k|) * (∑ l, |P j l|) ≤
          (entriesL1 (entries i) : ℝ) *
            (entriesL1 (entries j) : ℝ) :=
      mul_le_mul (hrowL1 i) (hrowL1 j) hsumJNonneg hbudgetINonneg
    have hscaled := mul_le_mul_of_nonneg_left hproduct hepsilonReal
    have hscaled' :
        (epsilon : ℝ) * (∑ k, |P i k|) * (∑ l, |P j l|) ≤
          (epsilon : ℝ) * (entriesL1 (entries i) : ℝ) *
            (entriesL1 (entries j) : ℝ) := by
      simpa only [mul_assoc] using hscaled
    rw [hcenter i j]
    unfold entriesRobustRadius
    push_cast
    exact add_le_add_right hscaled' _
  have hdominanceReal : ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          (entriesRobustRadius entries C epsilon i j : ℝ) *
            (weights j : ℝ)) <
        (entriesRobustDiagonalLower entries C epsilon i : ℝ) *
          (weights i : ℝ) := by
    intro i
    exact_mod_cast hdominance i
  exact posDef_of_robust_congruence
    A P Cr hA hPReal (epsilon : ℝ) hepsilonReal hcloseReal
    (fun i ↦ (entriesRobustDiagonalLower entries C epsilon i : ℝ))
    (fun i ↦ (weights i : ℝ))
    (fun i j ↦ (entriesRobustRadius entries C epsilon i j : ℝ))
    hweightsReal hradiusNonneg hradiusSymm hdiagonalReal
    hoffDiagonalReal hdominanceReal

/-- Rational-IsUnit adapter for the order-independent robust certificate. -/
theorem posDef_of_sparseEntries_robust_congruence_of_rational_isUnit
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ)
    (entries : n → SparseEntries n)
    (C : Matrix n n ℚ) (epsilon : ℚ) (weights : n → ℚ)
    (hA : A.IsHermitian) (hC : C.IsSymm)
    (hP : IsUnit (matrixOfSparseEntries entries))
    (hepsilon : 0 ≤ epsilon)
    (hclose : ∀ i j,
      |A i j - (C i j : ℝ)| ≤ (epsilon : ℝ))
    (hweights : ∀ i, 0 < weights i)
    (hdominance : ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius entries C epsilon i j * weights j) <
        entriesRobustDiagonalLower entries C epsilon i * weights i) :
    A.PosDef := by
  have hPReal : IsUnit (realMatrixOfSparseEntries entries) := by
    exact hP.map (Rat.castHom ℝ).mapMatrix
  exact posDef_of_sparseEntries_robust_congruence_of_isUnit
    A entries C epsilon weights hA hC hPReal hepsilon hclose
    hweights hdominance

/-- Lower-triangular convenience specialization.  A caller with a genuine
`LinearOrder` obtains the required rational and real `IsUnit` certificates
from accumulated pair-list row structure automatically.

For a raw sum such as `FactorTwoPhaseLowIndex`, either use one of the explicit
IsUnit theorems above or first install the intended even-then-odd local order. -/
theorem posDef_of_sparseEntries_robust_congruence
    {n : Type*} [Fintype n] [LinearOrder n]
    (A : Matrix n n ℝ)
    (entries : n → SparseEntries n)
    (C : Matrix n n ℚ) (epsilon : ℚ) (weights : n → ℚ)
    (hA : A.IsHermitian) (hC : C.IsSymm)
    (hlower : ∀ i j, entriesValue (entries i) j ≠ 0 → j ≤ i)
    (hdiag : ∀ i, entriesValue (entries i) i ≠ 0)
    (hepsilon : 0 ≤ epsilon)
    (hclose : ∀ i j,
      |A i j - (C i j : ℝ)| ≤ (epsilon : ℝ))
    (hweights : ∀ i, 0 < weights i)
    (hdominance : ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius entries C epsilon i j * weights j) <
        entriesRobustDiagonalLower entries C epsilon i * weights i) :
    A.PosDef := by
  exact posDef_of_sparseEntries_robust_congruence_of_rational_isUnit
    A entries C epsilon weights hA hC
    (matrixOfSparseEntries_isUnit entries hlower hdiag)
    hepsilon hclose hweights hdominance

end

end ArithmeticHodge.Analysis.SparseEntriesRobustCertificate
