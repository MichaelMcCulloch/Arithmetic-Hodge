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

/-- For a symmetric coercive tail form, the corrected Gram is positive
semidefinite if and only if the original coupled finite--tail quadratic is
nonnegative for every finite vector and every completed tail vector.  The
reverse implication tests the full quadratic at the negative aggregate Riesz
representative, so no density or matrix inverse is involved. -/
theorem coerciveBilinearCorrectedGram_posSemidef_iff_full_nonneg
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (B : K →L[ℝ] K →L[ℝ] ℝ)
    (hB : IsCoercive B) (ell : ι → StrongDual ℝ K)
    (hA : A.IsHermitian) (hBsymm : ∀ x y, B x y = B y x) :
    Matrix.PosSemidef (coerciveBilinearCorrectedGram A B hB ell) ↔
      ∀ (c : ι → ℝ) (x : K),
        0 ≤ c ⬝ᵥ (A *ᵥ c) + 2 * ∑ i, c i * ell i x + B x x := by
  constructor
  · intro hG c x
    exact coerciveBilinear_full_nonneg_of_correctedGram_posSemidef
      A B hB hBsymm ell hG c x
  · intro hfull
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (coerciveBilinearCorrectedGram_isHermitian A B hB ell hA hBsymm)
    intro c
    simp only [star_trivial]
    let r : K := ∑ i, c i • coerciveRieszCorrection hB (ell i)
    have h := hfull c (-r)
    rw [coerciveBilinear_complete_square A B hB hBsymm ell c (-r)] at h
    have hcancel : -r + ∑ i, c i • coerciveRieszCorrection hB (ell i) = 0 := by
      simp only [r, neg_add_cancel]
    rw [hcancel] at h
    simpa using h

omit [CompleteSpace K] in
private theorem coerciveBilinear_diagonal_nonneg
    (B : K →L[ℝ] K →L[ℝ] ℝ) (hB : IsCoercive B) (x : K) :
    0 ≤ B x x := by
  obtain ⟨mu, hmu, hdiag⟩ := hB
  exact (by positivity : 0 ≤ mu * ‖x‖ * ‖x‖).trans (hdiag x)

omit [CompleteSpace K] in
private theorem coerciveBilinear_apply_sq_le
    (B : K →L[ℝ] K →L[ℝ] ℝ) (hB : IsCoercive B)
    (hBsymm : ∀ x y, B x y = B y x) (x y : K) :
    B x y ^ 2 ≤ B x x * B y y := by
  let beta : LinearMap.BilinForm ℝ K :=
    LinearMap.mk₂ ℝ (fun u v ↦ B u v)
      (fun u v w ↦ by simp)
      (fun r u v ↦ by simp)
      (fun u v w ↦ by simp)
      (fun r u v ↦ by simp)
  exact beta.apply_sq_le_of_symm
    (fun z ↦ coerciveBilinear_diagonal_nonneg B hB z)
    ⟨hBsymm⟩ x y

/-- Exact dual characterization of an aggregate coercive Riesz energy bound.
The right side retains the complete bilinear tail energy and all correlations
among the aggregated functionals. -/
theorem coerciveBilinear_aggregateRiesz_energy_le_iff_functional_sq
    {ι : Type*} [Fintype ι]
    (B : K →L[ℝ] K →L[ℝ] ℝ) (hB : IsCoercive B)
    (hBsymm : ∀ x y, B x y = B y x)
    (ell : ι → StrongDual ℝ K) (c : ι → ℝ) (q : ℝ) :
    B (∑ i, c i • coerciveRieszCorrection hB (ell i))
        (∑ i, c i • coerciveRieszCorrection hB (ell i)) ≤ q ↔
      0 ≤ q ∧
        ∀ z : K,
          (∑ i, c i * ell i z) ^ 2 ≤ q * B z z := by
  classical
  let r : K := ∑ i, c i • coerciveRieszCorrection hB (ell i)
  have hr_nonneg : 0 ≤ B r r :=
    coerciveBilinear_diagonal_nonneg B hB r
  have hrepr (z : K) : B r z = ∑ i, c i * ell i z := by
    change B (∑ i, c i • coerciveRieszCorrection hB (ell i)) z = _
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [coerciveRieszCorrection_apply]
  constructor
  · intro hr_le
    refine ⟨hr_nonneg.trans hr_le, ?_⟩
    intro z
    rw [← hrepr]
    exact (coerciveBilinear_apply_sq_le B hB hBsymm r z).trans
      (mul_le_mul_of_nonneg_right hr_le
        (coerciveBilinear_diagonal_nonneg B hB z))
  · rintro ⟨hq_nonneg, hfunctional⟩
    have hsquare := hfunctional r
    rw [← hrepr] at hsquare
    change B r r ≤ q
    nlinarith

/-- For a symmetric coercive tail form, corrected-Gram positivity is
equivalent to one aggregate functional-square inequality against the *full*
tail energy.  Unlike rowwise norm estimates, this characterization preserves
all correlations among the finite low functionals. -/
theorem coerciveBilinearCorrectedGram_posSemidef_iff_functional_sq
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (B : K →L[ℝ] K →L[ℝ] ℝ)
    (hB : IsCoercive B) (ell : ι → StrongDual ℝ K)
    (hA : A.IsHermitian) (hBsymm : ∀ x y, B x y = B y x) :
    Matrix.PosSemidef (coerciveBilinearCorrectedGram A B hB ell) ↔
      ∀ c : ι → ℝ,
        0 ≤ c ⬝ᵥ (A *ᵥ c) ∧
          ∀ z : K,
            (∑ i, c i * ell i z) ^ 2 ≤
              (c ⬝ᵥ (A *ᵥ c)) * B z z := by
  classical
  rw [coerciveBilinearCorrectedGram_posSemidef_iff_energy
    A B hB ell hA hBsymm]
  constructor
  · intro henergy c
    exact (coerciveBilinear_aggregateRiesz_energy_le_iff_functional_sq
      B hB hBsymm ell c (c ⬝ᵥ (A *ᵥ c))).mp (henergy c)
  · intro hfunctional c
    exact (coerciveBilinear_aggregateRiesz_energy_le_iff_functional_sq
      B hB hBsymm ell c (c ⬝ᵥ (A *ᵥ c))).mpr (hfunctional c)

end

end ArithmeticHodge.Analysis
