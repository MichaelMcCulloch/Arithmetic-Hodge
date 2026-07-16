import ArithmeticHodge.Analysis.CoerciveBilinearFiniteSchur

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis

noncomputable section

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [CompleteSpace K]

/-- The quadratic of the inverse-free corrected Gram is exactly the original
finite quadratic minus the energy of the aggregate coercive Riesz
representative. -/
theorem coerciveBilinearCorrectedGram_quadratic
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (B : K →L[ℝ] K →L[ℝ] ℝ)
    (hB : IsCoercive B) (ell : ι → StrongDual ℝ K)
    (c : ι → ℝ) :
    c ⬝ᵥ (coerciveBilinearCorrectedGram A B hB ell *ᵥ c) =
      c ⬝ᵥ (A *ᵥ c) -
        B (∑ i, c i • coerciveRieszCorrection hB (ell i))
          (∑ i, c i • coerciveRieszCorrection hB (ell i)) := by
  classical
  let r : ι → K := fun i ↦ coerciveRieszCorrection hB (ell i)
  let C : ℝ := ∑ i, ∑ j, c i * B (r i) (r j) * c j
  have hmatrix :
      c ⬝ᵥ ((fun i j ↦ A i j - B (r i) (r j)) *ᵥ c) =
        c ⬝ᵥ (A *ᵥ c) - C := by
    simp only [dotProduct, mulVec, Finset.mul_sum, sub_mul, mul_sub, C]
    simp_rw [Finset.sum_sub_distrib]
    ring
  have henergy :
      B (∑ i, c i • r i) (∑ i, c i • r i) = C := by
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul, C]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change c ⬝ᵥ ((fun i j ↦ A i j - B (r i) (r j)) *ᵥ c) =
    c ⬝ᵥ (A *ᵥ c) - B (∑ i, c i • r i) (∑ i, c i • r i)
  rw [hmatrix, henergy]

/-- For a symmetric coercive tail form, positive semidefiniteness of the
corrected Gram is equivalent to one aggregate energy-domination inequality.
This removes every inverse and every individual correction entry from the
remaining proof obligation. -/
theorem coerciveBilinearCorrectedGram_posSemidef_iff_energy
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (B : K →L[ℝ] K →L[ℝ] ℝ)
    (hB : IsCoercive B) (ell : ι → StrongDual ℝ K)
    (hA : A.IsHermitian) (hBsymm : ∀ x y, B x y = B y x) :
    Matrix.PosSemidef (coerciveBilinearCorrectedGram A B hB ell) ↔
      ∀ c : ι → ℝ,
        B (∑ i, c i • coerciveRieszCorrection hB (ell i))
            (∑ i, c i • coerciveRieszCorrection hB (ell i)) ≤
          c ⬝ᵥ (A *ᵥ c) := by
  constructor
  · intro hG c
    have hq := hG.dotProduct_mulVec_nonneg c
    simp only [star_trivial] at hq
    rw [coerciveBilinearCorrectedGram_quadratic] at hq
    exact sub_nonneg.mp hq
  · intro henergy
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (coerciveBilinearCorrectedGram_isHermitian A B hB ell hA hBsymm)
    intro c
    simp only [star_trivial]
    rw [coerciveBilinearCorrectedGram_quadratic]
    exact sub_nonneg.mpr (henergy c)

end

end ArithmeticHodge.Analysis
