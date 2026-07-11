import ArithmeticHodge.Analysis.HermitianLowTail
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace

namespace ArithmeticHodge.Analysis

noncomputable section

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

noncomputable def hilbertTailRieszCorrection
    (ell : StrongDual ℂ K) : K :=
  (InnerProductSpace.toDual ℂ K).symm ell

@[simp] theorem hilbertTailRieszCorrection_inner
    (ell : StrongDual ℂ K) (x : K) :
    ⟪hilbertTailRieszCorrection ell, x⟫_ℂ = ell x := by
  exact InnerProductSpace.toDual_symm_apply

@[simp] theorem norm_hilbertTailRieszCorrection
    (ell : StrongDual ℂ K) :
    ‖hilbertTailRieszCorrection ell‖ = ‖ell‖ := by
  exact (InnerProductSpace.toDual ℂ K).symm.norm_map ell

noncomputable def hilbertTailCorrectedGram
    {ι : Type*} (A : Matrix ι ι ℂ) (ell : ι → StrongDual ℂ K) :
    Matrix ι ι ℂ :=
  fun i j ↦ A i j -
    ⟪hilbertTailRieszCorrection (ell i), hilbertTailRieszCorrection (ell j)⟫_ℂ

theorem hilbertTail_complete_square
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (ell : ι → StrongDual ℂ K)
    (c : ι → ℂ) (x : K) :
    star c ⬝ᵥ (A *ᵥ c) +
          ∑ i, star (c i) * ell i x +
          ∑ i, c i * star (ell i x) + ⟪x, x⟫_ℂ =
      star c ⬝ᵥ (hilbertTailCorrectedGram A ell *ᵥ c) +
        ⟪x + ∑ i, c i • hilbertTailRieszCorrection (ell i),
          x + ∑ i, c i • hilbertTailRieszCorrection (ell i)⟫_ℂ := by
  classical
  let v : ι → K := fun i ↦ hilbertTailRieszCorrection (ell i)
  have hv (i : ι) (y : K) : ⟪v i, y⟫_ℂ = ell i y := by
    simp [v]
  have hxv (i : ι) : ⟪x, v i⟫_ℂ = star (ell i x) := by
    rw [← inner_conj_symm, hv]
    rfl
  have hswap :
      (∑ i, ∑ j, c i * (star (c j) * ell j (v i))) =
        ∑ i, ∑ j, star (c i) * (ell i (v j) * c j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring_nf
  let C : ℂ := ∑ i, ∑ j, star (c i) * ell i (v j) * c j
  have hmatrix :
      star c ⬝ᵥ ((fun i j ↦ A i j - ⟪v i, v j⟫_ℂ) *ᵥ c) =
        star c ⬝ᵥ (A *ᵥ c) - C := by
    simp only [dotProduct, mulVec, Finset.mul_sum, sub_mul, mul_sub, hv, C,
      Pi.star_apply]
    simp_rw [Finset.sum_sub_distrib]
    ring_nf
  have htail :
      ⟪x + ∑ i, c i • v i, x + ∑ i, c i • v i⟫_ℂ =
        ⟪x, x⟫_ℂ +
          ∑ i, star (c i) * ell i x +
          ∑ i, c i * star (ell i x) + C := by
    simp only [inner_add_add_self, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, hv, hxv, starRingEnd_apply, C]
    simp_rw [Finset.mul_sum]
    rw [hswap]
    ring_nf
  change star c ⬝ᵥ (A *ᵥ c) +
          ∑ i, star (c i) * ell i x +
          ∑ i, c i * star (ell i x) + ⟪x, x⟫_ℂ =
      star c ⬝ᵥ ((fun i j ↦ A i j - ⟪v i, v j⟫_ℂ) *ᵥ c) +
        ⟪x + ∑ i, c i • v i, x + ∑ i, c i • v i⟫_ℂ
  rw [hmatrix, htail]
  ring_nf

theorem hilbertTail_quadratic_re_pos
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (ell : ι → StrongDual ℂ K)
    (hG : Matrix.PosDef (hilbertTailCorrectedGram A ell))
    (c : ι → ℂ) (x : K) (hne : c ≠ 0 ∨ x ≠ 0) :
    0 < (star c ⬝ᵥ (A *ᵥ c) +
          ∑ i, star (c i) * ell i x +
          ∑ i, c i * star (ell i x) + ⟪x, x⟫_ℂ).re := by
  rw [hilbertTail_complete_square]
  rw [Complex.add_re]
  by_cases hc : c = 0
  · have hx : x ≠ 0 := by
      rcases hne with hcne | hx
      · exact (hcne hc).elim
      · exact hx
    subst c
    have hmatrix :
        star (0 : ι → ℂ) ⬝ᵥ
          (hilbertTailCorrectedGram A ell *ᵥ (0 : ι → ℂ)) = 0 := by
      simp
    have hsum :
        ∑ i, (0 : ι → ℂ) i • hilbertTailRieszCorrection (ell i) = 0 := by
      simp
    rw [hmatrix, hsum]
    simp only [Complex.zero_re, zero_add, add_zero]
    rw [inner_self_eq_norm_sq_to_K]
    change 0 < ((‖x‖ : ℂ) ^ 2).re
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_pos_of_pos (norm_pos_iff.mpr hx)
  · have htail : 0 ≤
        (⟪x + ∑ i, c i • hilbertTailRieszCorrection (ell i),
          x + ∑ i, c i • hilbertTailRieszCorrection (ell i)⟫_ℂ).re :=
      @inner_self_nonneg ℂ K _ _ _
        (x := x + ∑ i, c i • hilbertTailRieszCorrection (ell i))
    exact add_pos_of_pos_of_nonneg (hG.re_dotProduct_pos hc) htail

theorem norm_hilbertTail_correction_pairing_le
    (ell₁ ell₂ : StrongDual ℂ K) :
    ‖⟪hilbertTailRieszCorrection ell₁, hilbertTailRieszCorrection ell₂⟫_ℂ‖ ≤
      ‖ell₁‖ * ‖ell₂‖ := by
  simpa using (@norm_inner_le_norm ℂ K _ _ _
    (hilbertTailRieszCorrection ell₁) (hilbertTailRieszCorrection ell₂))

end

end ArithmeticHodge.Analysis
