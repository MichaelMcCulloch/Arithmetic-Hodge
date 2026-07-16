import ArithmeticHodge.Analysis.CoerciveBilinearFiniteSchur

set_option autoImplicit false

namespace ArithmeticHodge.Analysis

noncomputable section

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [CompleteSpace K]

/-- The mixed functional after moving a prescribed low-dependent vector from
the tail coordinate into each low basis vector. -/
def coerciveBilinearShearedFunctional
    {ι : Type*} (B : K →L[ℝ] K →L[ℝ] ℝ)
    (ell : ι → StrongDual ℝ K) (s : ι → K) : ι → StrongDual ℝ K :=
  fun i ↦ ell i - B (s i)

/-- The finite low matrix after the same tail shear. -/
def coerciveBilinearShearedLowMatrix
    {ι : Type*} (A : Matrix ι ι ℝ) (B : K →L[ℝ] K →L[ℝ] ℝ)
    (ell : ι → StrongDual ℝ K) (s : ι → K) : Matrix ι ι ℝ :=
  fun i j ↦ A i j - ell i (s j) - ell j (s i) + B (s i) (s j)

omit [CompleteSpace K] in
@[simp]
theorem coerciveBilinearShearedFunctional_apply
    {ι : Type*} (B : K →L[ℝ] K →L[ℝ] ℝ)
    (ell : ι → StrongDual ℝ K) (s : ι → K) (i : ι) (x : K) :
    coerciveBilinearShearedFunctional B ell s i x =
      ell i x - B (s i) x := by
  rfl

/-- A tail shear subtracts the prescribed vector from the coercive Riesz
representative.  This identity uses coercivity but not symmetry of the
bilinear form. -/
theorem coerciveRieszCorrection_shearedFunctional
    {ι : Type*} (B : K →L[ℝ] K →L[ℝ] ℝ)
    (hB : IsCoercive B) (ell : ι → StrongDual ℝ K) (s : ι → K)
    (i : ι) :
    coerciveRieszCorrection hB
        (coerciveBilinearShearedFunctional B ell s i) =
      coerciveRieszCorrection hB (ell i) - s i := by
  apply hB.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro x
  simp only [hB.continuousLinearEquivOfBilin_apply]
  rw [coerciveRieszCorrection_apply]
  change ell i x - B (s i) x = B (coerciveRieszCorrection hB (ell i) - s i) x
  simp only [map_sub, ContinuousLinearMap.sub_apply,
    coerciveRieszCorrection_apply]

/-- Exact tail-shear invariance of the inverse-free corrected Gram.  The
symmetry hypothesis identifies the second cross term with evaluation of the
corresponding Riesz functional. -/
theorem coerciveBilinearCorrectedGram_shear
    {ι : Type*} (A : Matrix ι ι ℝ) (B : K →L[ℝ] K →L[ℝ] ℝ)
    (hB : IsCoercive B) (hBsymm : ∀ x y, B x y = B y x)
    (ell : ι → StrongDual ℝ K) (s : ι → K) :
    coerciveBilinearCorrectedGram
        (coerciveBilinearShearedLowMatrix A B ell s) B hB
        (coerciveBilinearShearedFunctional B ell s) =
      coerciveBilinearCorrectedGram A B hB ell := by
  ext i j
  simp only [coerciveBilinearCorrectedGram,
    coerciveBilinearShearedLowMatrix,
    coerciveRieszCorrection_shearedFunctional]
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [coerciveRieszCorrection_apply hB (ell i) (s j),
    hBsymm (s i) (coerciveRieszCorrection hB (ell j)),
    coerciveRieszCorrection_apply hB (ell j) (s i)]
  ring

end

end ArithmeticHodge.Analysis
