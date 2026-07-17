import Mathlib.LinearAlgebra.Matrix.PosDef
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectDiskBoundaryStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixStrictDiskStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectSixSchurStructural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectDiskBoundaryStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectMatrixStructural
open YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction
open YoshidaFactorTwoPhaseIntrinsicSixStrictDiskStructural

/-!
# The direct cutoff-nine matrix as a strict six-mode Schur extension

The direct coordinate order is

`(c0,c2,c4,c1,c3,c5 | c6,c8,c7)`.

Thus the first six coordinates are exactly the phase-native quadratic proved
strictly positive in
`YoshidaFactorTwoPhaseIntrinsicSixStrictDiskStructural`.  Reindexing the
direct `Fin 9` matrix along `Fin 6 ⊕ Fin 3 ≃ Fin 9` exposes a Hermitian
block matrix

`[[A₆, B], [Bᴴ, D₃]]`.

Since `A₆` is positive definite throughout the closed phase disk, the
standard block congruence reduces positive semidefiniteness of the complete
direct matrix exactly to the final `3 × 3` Schur complement

`D₃ - Bᴴ A₆⁻¹ B`.

No static transfer and no enhanced survivor estimate enters this reduction.
-/

/-! ## The exact `6 + 3` block decomposition -/

/-- The coordinate-order equivalence
`Fin 6 ⊕ Fin 3 ≃ Fin 9`. -/
def factorTwoIntrinsicNineDirectSixThreeEquiv :
    (Fin 6 ⊕ Fin 3) ≃ Fin 9 :=
  finSumFinEquiv

/-- The direct matrix reindexed into its first six and last three
coordinates. -/
def factorTwoIntrinsicNineDirectSplitMatrix
    (a b : ℝ) : Matrix (Fin 6 ⊕ Fin 3) (Fin 6 ⊕ Fin 3) ℝ :=
  (factorTwoIntrinsicNineDirectLowMatrix a b).submatrix
    factorTwoIntrinsicNineDirectSixThreeEquiv
    factorTwoIntrinsicNineDirectSixThreeEquiv

/-- The strict phase-native six-mode leading block. -/
def factorTwoIntrinsicNineDirectCoreMatrix
    (a b : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  (factorTwoIntrinsicNineDirectSplitMatrix a b).submatrix Sum.inl Sum.inl

/-- Coupling of the first six modes to `(P₆,P₈,P₇)`. -/
def factorTwoIntrinsicNineDirectCoreSurvivorMatrix
    (a b : ℝ) : Matrix (Fin 6) (Fin 3) ℝ :=
  (factorTwoIntrinsicNineDirectSplitMatrix a b).submatrix Sum.inl Sum.inr

/-- The raw `(P₆,P₈,P₇)` diagonal block after charging the
balanced `15 / 16` low reserve. -/
def factorTwoIntrinsicNineDirectSurvivorMatrix
    (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (factorTwoIntrinsicNineDirectSplitMatrix a b).submatrix Sum.inr Sum.inr

/-- A scalar vector in the direct coordinate order, assembled from its first
six and last three coordinates. -/
def factorTwoIntrinsicNineDirectSplitVector
    (x : Fin 6 → ℝ) (z : Fin 3 → ℝ) : Fin 9 → ℝ :=
  ![x 0, x 1, x 2, x 3, x 4, x 5, z 0, z 1, z 2]

@[simp]
theorem factorTwoIntrinsicNineDirectSplitVector_comp_equiv
    (x : Fin 6 → ℝ) (z : Fin 3 → ℝ) :
    factorTwoIntrinsicNineDirectSplitVector x z ∘
        factorTwoIntrinsicNineDirectSixThreeEquiv =
      Sum.elim x z := by
  funext i
  rcases i with i | i
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl

@[simp]
theorem factorTwoIntrinsicNineDirectSumElim_comp_equiv_symm
    (x : Fin 6 → ℝ) (z : Fin 3 → ℝ) :
    Sum.elim x z ∘ factorTwoIntrinsicNineDirectSixThreeEquiv.symm =
      factorTwoIntrinsicNineDirectSplitVector x z := by
  funext i
  have h := congrFun
    (factorTwoIntrinsicNineDirectSplitVector_comp_equiv x z)
    (factorTwoIntrinsicNineDirectSixThreeEquiv.symm i)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h.symm

/-- Reindexing preserves the exact direct quadratic. -/
theorem factorTwoIntrinsicNineDirectSplitMatrix_quadratic
    (a b : ℝ) (x : Fin 6 → ℝ) (z : Fin 3 → ℝ) :
    Sum.elim x z ⬝ᵥ
        (factorTwoIntrinsicNineDirectSplitMatrix a b *ᵥ Sum.elim x z) =
      factorTwoIntrinsicNineDirectCoordinateQuadratic a b
        (factorTwoIntrinsicNineDirectSplitVector x z) := by
  let w : Fin 6 ⊕ Fin 3 → ℝ := Sum.elim x z
  let y : Fin 9 → ℝ := factorTwoIntrinsicNineDirectSplitVector x z
  have hy :
      w ∘ factorTwoIntrinsicNineDirectSixThreeEquiv.symm = y := by
    simpa only [w, y] using
      factorTwoIntrinsicNineDirectSumElim_comp_equiv_symm x z
  have hw :
      w = y ∘ factorTwoIntrinsicNineDirectSixThreeEquiv := by
    simpa only [w, y] using
      (factorTwoIntrinsicNineDirectSplitVector_comp_equiv x z).symm
  have hmul :
      factorTwoIntrinsicNineDirectSplitMatrix a b *ᵥ w =
        (factorTwoIntrinsicNineDirectLowMatrix a b *ᵥ y) ∘
          factorTwoIntrinsicNineDirectSixThreeEquiv := by
    unfold factorTwoIntrinsicNineDirectSplitMatrix
    rw [submatrix_mulVec_equiv, hy]
  change w ⬝ᵥ (factorTwoIntrinsicNineDirectSplitMatrix a b *ᵥ w) = _
  calc
    w ⬝ᵥ (factorTwoIntrinsicNineDirectSplitMatrix a b *ᵥ w) =
        (y ∘ factorTwoIntrinsicNineDirectSixThreeEquiv) ⬝ᵥ
          ((factorTwoIntrinsicNineDirectLowMatrix a b *ᵥ y) ∘
            factorTwoIntrinsicNineDirectSixThreeEquiv) := by
      rw [hmul, hw]
    _ = y ⬝ᵥ (factorTwoIntrinsicNineDirectLowMatrix a b *ᵥ y) :=
      comp_equiv_dotProduct_comp_equiv _ _ _
    _ = factorTwoIntrinsicNineDirectCoordinateQuadratic a b y :=
      factorTwoIntrinsicNineDirectLowMatrix_quadratic a b y
    _ = factorTwoIntrinsicNineDirectCoordinateQuadratic a b
        (factorTwoIntrinsicNineDirectSplitVector x z) := by rfl

/-- The reindexed direct matrix is exactly its displayed Hermitian block
decomposition. -/
theorem factorTwoIntrinsicNineDirectSplitMatrix_eq_fromBlocks
    (a b : ℝ) :
    factorTwoIntrinsicNineDirectSplitMatrix a b =
      Matrix.fromBlocks
        (factorTwoIntrinsicNineDirectCoreMatrix a b)
        (factorTwoIntrinsicNineDirectCoreSurvivorMatrix a b)
        (factorTwoIntrinsicNineDirectCoreSurvivorMatrix a b)ᴴ
        (factorTwoIntrinsicNineDirectSurvivorMatrix a b) := by
  have hHermitian :
      (factorTwoIntrinsicNineDirectSplitMatrix a b).IsHermitian := by
    have hFull :
        (factorTwoIntrinsicNineDirectLowMatrix a b).IsHermitian := by
      simpa only [Matrix.IsHermitian, conjTranspose, star_trivial] using
        factorTwoIntrinsicNineDirectLowMatrix_transpose a b
    exact hFull.submatrix factorTwoIntrinsicNineDirectSixThreeEquiv
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rfl
  · simpa only [factorTwoIntrinsicNineDirectCoreSurvivorMatrix,
      Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply,
      star_trivial, Matrix.submatrix_apply] using
      (hHermitian.apply (Sum.inr i) (Sum.inl j)).symm
  · rfl

/-! ## The leading six-mode block is positive definite -/

/-- Restricting the direct coordinate quadratic to the first six coordinates
recovers the strict six-mode phase exactly. -/
private theorem factorTwoIntrinsicNineDirectCoordinateQuadratic_core
    (a b : ℝ) (x : Fin 6 → ℝ) :
    factorTwoIntrinsicNineDirectCoordinateQuadratic a b
        (factorTwoIntrinsicNineDirectSplitVector x 0) =
      factorTwoIntrinsicSixStaticEven a (x 0) (x 1) (x 2) +
        factorTwoIntrinsicSixStaticOdd (-a) (x 3) (x 4) (x 5) +
        b * factorTwoIntrinsicSixStaticAlternating
          (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
  unfold factorTwoIntrinsicNineDirectCoordinateQuadratic
    factorTwoIntrinsicNineDirectSplitVector
    factorTwoIntrinsicNineDirectLowQuadratic
    factorTwoIntrinsicNineDirectEvenQuadratic
    factorTwoIntrinsicNineDirectOddQuadratic
    factorTwoIntrinsicNineDirectAlternating
    factorTwoIntrinsicNineP678LowReserve
  simp

/-- Exact quadratic identity for the leading six-mode block. -/
theorem factorTwoIntrinsicNineDirectCoreMatrix_quadratic
    (a b : ℝ) (x : Fin 6 → ℝ) :
    x ⬝ᵥ (factorTwoIntrinsicNineDirectCoreMatrix a b *ᵥ x) =
      factorTwoIntrinsicSixStaticEven a (x 0) (x 1) (x 2) +
        factorTwoIntrinsicSixStaticOdd (-a) (x 3) (x 4) (x 5) +
        b * factorTwoIntrinsicSixStaticAlternating
          (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
  calc
    x ⬝ᵥ (factorTwoIntrinsicNineDirectCoreMatrix a b *ᵥ x) =
        Sum.elim x 0 ⬝ᵥ
          (factorTwoIntrinsicNineDirectSplitMatrix a b *ᵥ Sum.elim x 0) := by
      rw [factorTwoIntrinsicNineDirectSplitMatrix_eq_fromBlocks]
      simp [Matrix.fromBlocks_mulVec]
    _ = factorTwoIntrinsicNineDirectCoordinateQuadratic a b
          (factorTwoIntrinsicNineDirectSplitVector x 0) :=
      factorTwoIntrinsicNineDirectSplitMatrix_quadratic a b x 0
    _ = _ := factorTwoIntrinsicNineDirectCoordinateQuadratic_core a b x

/-- The first six coordinates form a positive-definite block at every phase
in the closed unit disk. -/
theorem factorTwoIntrinsicNineDirectCoreMatrix_posDef
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (factorTwoIntrinsicNineDirectCoreMatrix a b).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · have hFull :
        (factorTwoIntrinsicNineDirectLowMatrix a b).IsHermitian := by
      simpa only [Matrix.IsHermitian, conjTranspose, star_trivial] using
        factorTwoIntrinsicNineDirectLowMatrix_transpose a b
    exact (hFull.submatrix factorTwoIntrinsicNineDirectSixThreeEquiv).submatrix
      Sum.inl
  · intro x hx
    simp only [star_trivial]
    rw [factorTwoIntrinsicNineDirectCoreMatrix_quadratic]
    apply factorTwoIntrinsicSixPhaseCoordinates_pos
      (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) a b hab
    by_contra hzero
    push_neg at hzero
    rcases hzero with ⟨h0, h1, h2, h3, h4, h5⟩
    apply hx
    funext i
    fin_cases i <;> assumption

/-! ## The exact final `3 × 3` criterion -/

/-- The final phase-native Schur complement.  This is the only matrix still
requiring a positivity estimate after the strict six-mode theorem. -/
def factorTwoIntrinsicNineDirectFinalSchurMatrix
    (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  factorTwoIntrinsicNineDirectSurvivorMatrix a b -
    (factorTwoIntrinsicNineDirectCoreSurvivorMatrix a b)ᴴ *
      (factorTwoIntrinsicNineDirectCoreMatrix a b)⁻¹ *
      factorTwoIntrinsicNineDirectCoreSurvivorMatrix a b

theorem factorTwoIntrinsicNineDirectFinalSchurMatrix_isHermitian
    (a b : ℝ) :
    (factorTwoIntrinsicNineDirectFinalSchurMatrix a b).IsHermitian := by
  have hFull :
      (factorTwoIntrinsicNineDirectLowMatrix a b).IsHermitian := by
    simpa only [Matrix.IsHermitian, conjTranspose, star_trivial] using
      factorTwoIntrinsicNineDirectLowMatrix_transpose a b
  have hSplit := hFull.submatrix factorTwoIntrinsicNineDirectSixThreeEquiv
  have hCore := hSplit.submatrix Sum.inl
  have hSurvivor := hSplit.submatrix Sum.inr
  exact hSurvivor.sub
    (isHermitian_conjTranspose_mul_mul
      (factorTwoIntrinsicNineDirectCoreSurvivorMatrix a b) hCore.inv)

/-- Pointwise exact Schur equivalence throughout the phase disk. -/
theorem factorTwoIntrinsicNineDirectLowMatrix_posSemidef_iff_finalSchur
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (factorTwoIntrinsicNineDirectLowMatrix a b).PosSemidef ↔
      (factorTwoIntrinsicNineDirectFinalSchurMatrix a b).PosSemidef := by
  have hCore := factorTwoIntrinsicNineDirectCoreMatrix_posDef a b hab
  letI := hCore.isUnit.invertible
  calc
    (factorTwoIntrinsicNineDirectLowMatrix a b).PosSemidef ↔
        (factorTwoIntrinsicNineDirectSplitMatrix a b).PosSemidef := by
      simpa only [factorTwoIntrinsicNineDirectSplitMatrix] using
        (Matrix.posSemidef_submatrix_equiv
          (M := factorTwoIntrinsicNineDirectLowMatrix a b)
          factorTwoIntrinsicNineDirectSixThreeEquiv).symm
    _ ↔ (Matrix.fromBlocks
          (factorTwoIntrinsicNineDirectCoreMatrix a b)
          (factorTwoIntrinsicNineDirectCoreSurvivorMatrix a b)
          (factorTwoIntrinsicNineDirectCoreSurvivorMatrix a b)ᴴ
          (factorTwoIntrinsicNineDirectSurvivorMatrix a b)).PosSemidef := by
      rw [factorTwoIntrinsicNineDirectSplitMatrix_eq_fromBlocks]
    _ ↔ (factorTwoIntrinsicNineDirectFinalSchurMatrix a b).PosSemidef := by
      simpa only [factorTwoIntrinsicNineDirectFinalSchurMatrix] using
        (Matrix.PosDef.fromBlocks₁₁
          (factorTwoIntrinsicNineDirectCoreSurvivorMatrix a b)
          (factorTwoIntrinsicNineDirectSurvivorMatrix a b) hCore)

/-- Scalar form of the exact remaining `3 × 3` condition. -/
theorem factorTwoIntrinsicNineDirectFinalSchurMatrix_posSemidef_of_nonneg
    (a b : ℝ)
    (h : ∀ z : Fin 3 → ℝ,
      0 ≤ z ⬝ᵥ (factorTwoIntrinsicNineDirectFinalSchurMatrix a b *ᵥ z)) :
    (factorTwoIntrinsicNineDirectFinalSchurMatrix a b).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact factorTwoIntrinsicNineDirectFinalSchurMatrix_isHermitian a b
  · intro z
    simpa only [star_trivial] using h z

/-- On the unit circle, direct `Fin 9` positive semidefiniteness is equivalent
to the final `Fin 3` Schur criterion. -/
theorem factorTwoIntrinsicNineDirect_unitCircle_posSemidef_iff_finalSchur :
    (∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      (factorTwoIntrinsicNineDirectLowMatrix a b).PosSemidef) ↔
    (∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      (factorTwoIntrinsicNineDirectFinalSchurMatrix a b).PosSemidef) := by
  constructor
  · intro h a b hab
    exact (factorTwoIntrinsicNineDirectLowMatrix_posSemidef_iff_finalSchur
      a b hab.le).mp (h a b hab)
  · intro h a b hab
    exact (factorTwoIntrinsicNineDirectLowMatrix_posSemidef_iff_finalSchur
      a b hab.le).mpr (h a b hab)

/-- A proof of the final `3 × 3` Schur condition on the circle closes the
direct matrix on the whole disk by affine boundary reduction. -/
theorem factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_finalSchur_circle
    (hcircle : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      (factorTwoIntrinsicNineDirectFinalSchurMatrix a b).PosSemidef)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (factorTwoIntrinsicNineDirectLowMatrix a b).PosSemidef := by
  apply factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_unitCircle
  · intro s t hst
    exact (factorTwoIntrinsicNineDirectLowMatrix_posSemidef_iff_finalSchur
      s t hst.le).mpr (hcircle s t hst)
  · exact hab

/-- Fully scalar version of the remaining circle criterion. -/
theorem factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_finalSchur_quadratic_circle
    (hcircle : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      ∀ z : Fin 3 → ℝ,
        0 ≤ z ⬝ᵥ (factorTwoIntrinsicNineDirectFinalSchurMatrix a b *ᵥ z))
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (factorTwoIntrinsicNineDirectLowMatrix a b).PosSemidef := by
  apply factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_finalSchur_circle
  · intro s t hst
    exact factorTwoIntrinsicNineDirectFinalSchurMatrix_posSemidef_of_nonneg
      s t (hcircle s t hst)
  · exact hab

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectSixSchurStructural
