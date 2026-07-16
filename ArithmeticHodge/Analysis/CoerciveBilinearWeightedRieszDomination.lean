import ArithmeticHodge.Analysis.CoerciveBilinearSchurCharacterization

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis

noncomputable section

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [CompleteSpace K]

omit [CompleteSpace K] in
private theorem coerciveBilinear_diagonal_nonneg
    (B : K →L[ℝ] K →L[ℝ] ℝ) (hB : IsCoercive B) (x : K) :
    0 ≤ B x x := by
  obtain ⟨mu, hmu, hdiag⟩ := hB
  exact (by positivity : 0 ≤ mu * ‖x‖ * ‖x‖).trans (hdiag x)

omit [CompleteSpace K] in
private theorem coerciveBilinear_sq_le
    (B : K →L[ℝ] K →L[ℝ] ℝ) (hB : IsCoercive B)
    (hBsymm : ∀ x y, B x y = B y x) (x y : K) :
    B x y ^ 2 ≤ B x x * B y y := by
  let β : LinearMap.BilinForm ℝ K :=
    LinearMap.mk₂ ℝ (fun u v ↦ B u v)
      (fun u v w ↦ by simp)
      (fun r u v ↦ by simp)
      (fun u v w ↦ by simp)
      (fun r u v ↦ by simp)
  exact β.apply_sq_le_of_symm
    (fun z ↦ coerciveBilinear_diagonal_nonneg B hB z)
    ⟨hBsymm⟩ x y

/-- Individual energy bounds for finitely many coercive Riesz representatives
combine into an aggregate energy bound when a positive diagonal reserve pays
for their weighted energy budget. -/
theorem coerciveBilinear_aggregateRiesz_energy_le_diagonalReserve
    {ι : Type*} [Fintype ι]
    (B : K →L[ℝ] K →L[ℝ] ℝ)
    (hB : IsCoercive B) (hBsymm : ∀ x y, B x y = B y x)
    (ell : ι → StrongDual ℝ K) (d gamma : ι → ℝ)
    (hd : ∀ i, 0 < d i)
    (hrow : ∀ i,
      B (coerciveRieszCorrection hB (ell i))
          (coerciveRieszCorrection hB (ell i)) ≤ gamma i)
    (hbudget : ∑ i, gamma i / d i ≤ 1)
    (c : ι → ℝ) :
    B (∑ i, c i • coerciveRieszCorrection hB (ell i))
        (∑ i, c i • coerciveRieszCorrection hB (ell i)) ≤
      ∑ i, d i * c i ^ 2 := by
  classical
  let r : ι → K := fun i ↦ coerciveRieszCorrection hB (ell i)
  let R : K := ∑ i, c i • r i
  let E : ℝ := B R R
  let D : ℝ := ∑ i, d i * c i ^ 2
  let S : ℝ := ∑ i, (ell i R) ^ 2 / d i
  have hdiag (x : K) : 0 ≤ B x x :=
    coerciveBilinear_diagonal_nonneg B hB x
  have hfunctional (i : ι) (x : K) :
      (ell i x) ^ 2 ≤ gamma i * B x x := by
    calc
      (ell i x) ^ 2 = B (r i) x ^ 2 := by
        rw [coerciveRieszCorrection_apply]
      _ ≤ B (r i) (r i) * B x x :=
        coerciveBilinear_sq_le B hB hBsymm (r i) x
      _ ≤ gamma i * B x x :=
        mul_le_mul_of_nonneg_right (hrow i) (hdiag x)
  have hE_nonneg : 0 ≤ E := hdiag R
  have hD_nonneg : 0 ≤ D := by
    dsimp only [D]
    exact Finset.sum_nonneg fun i _ ↦
      mul_nonneg (hd i).le (sq_nonneg (c i))
  have hE_repr : E = ∑ i, c i * ell i R := by
    have hBR : B R = ∑ i, c i • B (r i) := by
      dsimp only [R]
      simp only [map_sum, map_smul]
    dsimp only [E]
    rw [hBR]
    simp only [ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [show B (r i) R = ell i R by
      simpa only [r] using coerciveRieszCorrection_apply hB (ell i) R]
  have hsqrt_pos (i : ι) : 0 < Real.sqrt (d i) :=
    Real.sqrt_pos.2 (hd i)
  have hmul (i : ι) :
      (Real.sqrt (d i) * c i) *
          (ell i R / Real.sqrt (d i)) = c i * ell i R := by
    field_simp [(hsqrt_pos i).ne']
  have hleft_sq (i : ι) :
      (Real.sqrt (d i) * c i) ^ 2 = d i * c i ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hd i).le]
  have hright_sq (i : ι) :
      (ell i R / Real.sqrt (d i)) ^ 2 = (ell i R) ^ 2 / d i := by
    rw [div_pow, Real.sq_sqrt (hd i).le]
  have hweightedCauchy :
      (∑ i, c i * ell i R) ^ 2 ≤ D * S := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i ↦ Real.sqrt (d i) * c i)
      (fun i ↦ ell i R / Real.sqrt (d i))
    simp_rw [hmul, hleft_sq, hright_sq] at h
    exact h
  have hS : S ≤ E := by
    calc
      S ≤ ∑ i, (gamma i / d i) * E := by
        dsimp only [S]
        apply Finset.sum_le_sum
        intro i _
        calc
          (ell i R) ^ 2 / d i ≤ (gamma i * E) / d i :=
            div_le_div_of_nonneg_right (hfunctional i R) (hd i).le
          _ = (gamma i / d i) * E := by ring
      _ = (∑ i, gamma i / d i) * E := by
        rw [Finset.sum_mul]
      _ ≤ 1 * E := mul_le_mul_of_nonneg_right hbudget hE_nonneg
      _ = E := one_mul E
  have hE_sq : E ^ 2 ≤ D * E := by
    calc
      E ^ 2 = (∑ i, c i * ell i R) ^ 2 := by rw [hE_repr]
      _ ≤ D * S := hweightedCauchy
      _ ≤ D * E := mul_le_mul_of_nonneg_left hS hD_nonneg
  have hED : E ≤ D := by
    nlinarith
  exact hED

/-- A diagonal reserve in the finite low quadratic, together with a weighted
row-energy budget for the coercive Riesz representatives, dominates their
aggregate energy. -/
theorem coerciveBilinear_aggregateRiesz_energy_le_of_diagonalReserve
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (B : K →L[ℝ] K →L[ℝ] ℝ)
    (hB : IsCoercive B) (hBsymm : ∀ x y, B x y = B y x)
    (ell : ι → StrongDual ℝ K) (d gamma : ι → ℝ)
    (hd : ∀ i, 0 < d i)
    (hreserve : ∀ c : ι → ℝ,
      ∑ i, d i * c i ^ 2 ≤ c ⬝ᵥ (A *ᵥ c))
    (hrow : ∀ i,
      B (coerciveRieszCorrection hB (ell i))
          (coerciveRieszCorrection hB (ell i)) ≤ gamma i)
    (hbudget : ∑ i, gamma i / d i ≤ 1)
    (c : ι → ℝ) :
    B (∑ i, c i • coerciveRieszCorrection hB (ell i))
        (∑ i, c i • coerciveRieszCorrection hB (ell i)) ≤
      c ⬝ᵥ (A *ᵥ c) := by
  exact (coerciveBilinear_aggregateRiesz_energy_le_diagonalReserve
    B hB hBsymm ell d gamma hd hrow hbudget c).trans (hreserve c)

/-- The weighted diagonal-reserve criterion certifies the inverse-free
corrected Gram as positive semidefinite. -/
theorem coerciveBilinearCorrectedGram_posSemidef_of_weightedRieszEnergy
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (B : K →L[ℝ] K →L[ℝ] ℝ)
    (hB : IsCoercive B) (ell : ι → StrongDual ℝ K)
    (hA : A.IsHermitian) (hBsymm : ∀ x y, B x y = B y x)
    (d gamma : ι → ℝ) (hd : ∀ i, 0 < d i)
    (hreserve : ∀ c : ι → ℝ,
      ∑ i, d i * c i ^ 2 ≤ c ⬝ᵥ (A *ᵥ c))
    (hrow : ∀ i,
      B (coerciveRieszCorrection hB (ell i))
          (coerciveRieszCorrection hB (ell i)) ≤ gamma i)
    (hbudget : ∑ i, gamma i / d i ≤ 1) :
    Matrix.PosSemidef (coerciveBilinearCorrectedGram A B hB ell) := by
  rw [coerciveBilinearCorrectedGram_posSemidef_iff_energy
    A B hB ell hA hBsymm]
  exact coerciveBilinear_aggregateRiesz_energy_le_of_diagonalReserve
    A B hB hBsymm ell d gamma hd hreserve hrow hbudget

end

end ArithmeticHodge.Analysis
