import ArithmeticHodge.Analysis.CoerciveRieszCorrection
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis

noncomputable section

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [CompleteSpace K]

omit [CompleteSpace K] in
private theorem isCoercive_diagonal_nonneg
    (B : K →L[ℝ] K →L[ℝ] ℝ) (hB : IsCoercive B) (x : K) :
    0 ≤ B x x := by
  obtain ⟨mu, hmu, hdiag⟩ := hB
  exact (by positivity : 0 ≤ mu * ‖x‖ * ‖x‖).trans (hdiag x)

/-- Subtract the Gram matrix of the coercive Riesz representatives from a
finite low block.  This is the inverse-free Schur complement associated to
the completed tail form. -/
def coerciveBilinearCorrectedGram
    {ι : Type*} (A : Matrix ι ι ℝ) (B : K →L[ℝ] K →L[ℝ] ℝ)
    (hB : IsCoercive B) (ell : ι → StrongDual ℝ K) : Matrix ι ι ℝ :=
  fun i j ↦ A i j -
    B (coerciveRieszCorrection hB (ell i))
      (coerciveRieszCorrection hB (ell j))

/-- Symmetry of the low block and tail form passes to the corrected Gram
matrix. -/
theorem coerciveBilinearCorrectedGram_isHermitian
    {ι : Type*} (A : Matrix ι ι ℝ) (B : K →L[ℝ] K →L[ℝ] ℝ)
    (hB : IsCoercive B) (ell : ι → StrongDual ℝ K)
    (hA : A.IsHermitian) (hBsymm : ∀ x y, B x y = B y x) :
    (coerciveBilinearCorrectedGram A B hB ell).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hAij := hA.apply i j
  simp only [coerciveBilinearCorrectedGram, star_trivial] at hAij ⊢
  rw [hAij, hBsymm]

/-- Exact completion of the square for a finite low block coupled to a
symmetric coercive real bilinear tail form. -/
theorem coerciveBilinear_complete_square
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (B : K →L[ℝ] K →L[ℝ] ℝ)
    (hB : IsCoercive B) (hBsymm : ∀ x y, B x y = B y x)
    (ell : ι → StrongDual ℝ K) (c : ι → ℝ) (x : K) :
    c ⬝ᵥ (A *ᵥ c) + 2 * ∑ i, c i * ell i x + B x x =
      c ⬝ᵥ (coerciveBilinearCorrectedGram A B hB ell *ᵥ c) +
        B (x + ∑ i, c i • coerciveRieszCorrection hB (ell i))
          (x + ∑ i, c i • coerciveRieszCorrection hB (ell i)) := by
  classical
  let r : ι → K := fun i ↦ coerciveRieszCorrection hB (ell i)
  have hr (i : ι) (y : K) : B (r i) y = ell i y := by
    exact coerciveRieszCorrection_apply hB (ell i) y
  have hyr (i : ι) (y : K) : B y (r i) = ell i y := by
    rw [hBsymm, hr]
  let C : ℝ := ∑ i, ∑ j, c i * B (r i) (r j) * c j
  have hswap :
      (∑ i, c i * ∑ j, c j * ell j (r i)) =
        ∑ i, ∑ j, c i * ell i (r j) * c j := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hmatrix :
      c ⬝ᵥ ((fun i j ↦ A i j - B (r i) (r j)) *ᵥ c) =
        c ⬝ᵥ (A *ᵥ c) - C := by
    simp only [dotProduct, mulVec, Finset.mul_sum, sub_mul, mul_sub, C]
    simp_rw [Finset.sum_sub_distrib]
    ring
  have htail :
      B (x + ∑ i, c i • r i) (x + ∑ i, c i • r i) =
        B x x + 2 * ∑ i, c i * ell i x + C := by
    simp only [map_add, ContinuousLinearMap.add_apply, map_sum,
      ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hr, hyr, C]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, hswap]
    ring
  change c ⬝ᵥ (A *ᵥ c) + 2 * ∑ i, c i * ell i x + B x x =
      c ⬝ᵥ ((fun i j ↦ A i j - B (r i) (r j)) *ᵥ c) +
        B (x + ∑ i, c i • r i) (x + ∑ i, c i • r i)
  rw [hmatrix, htail]
  ring

/-- Positive semidefiniteness of the corrected finite Gram closes the full
low--tail quadratic because the residual completed square is nonnegative by
coercivity. -/
theorem coerciveBilinear_full_nonneg_of_correctedGram_posSemidef
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (B : K →L[ℝ] K →L[ℝ] ℝ)
    (hB : IsCoercive B) (hBsymm : ∀ x y, B x y = B y x)
    (ell : ι → StrongDual ℝ K)
    (hG : Matrix.PosSemidef (coerciveBilinearCorrectedGram A B hB ell))
    (c : ι → ℝ) (x : K) :
    0 ≤ c ⬝ᵥ (A *ᵥ c) + 2 * ∑ i, c i * ell i x + B x x := by
  rw [coerciveBilinear_complete_square A B hB hBsymm ell c x]
  apply add_nonneg (hG.dotProduct_mulVec_nonneg c)
  exact isCoercive_diagonal_nonneg B hB
    (x + ∑ i, c i • coerciveRieszCorrection hB (ell i))

end

end ArithmeticHodge.Analysis
