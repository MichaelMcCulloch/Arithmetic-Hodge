import Mathlib.LinearAlgebra.Matrix.PosDef

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseScaledRangeCompletionStructural

noncomputable section

/-- A fraction-free completion of one scalar border of a positive-semidefinite
finite quadratic form.  The equation `A *ᵥ v = d • h` is a scaled range
certificate; no inverse of `A` is required.  In the nonsingular case one may
take `v = d A⁻¹ h`, and the scalar condition is the usual Schur-complement
budget with all denominators cleared. -/
theorem scaledRange_border_nonneg_iff
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (h v : ι → ℝ) (d Y : ℝ)
    (hA : A.PosSemidef)
    (hd : 0 < d)
    (hrange : A *ᵥ v = d • h) :
    (∀ (x : ι → ℝ) (r : ℝ),
      0 ≤ 15 * (x ⬝ᵥ (A *ᵥ x)) +
        30 * r * (h ⬝ᵥ x) + Y * r ^ 2) ↔
      15 * (h ⬝ᵥ v) ≤ d * Y := by
  classical
  have hAT : Aᵀ = A := by
    simpa only [conjTranspose, star_trivial] using hA.1.eq
  have hsymm (x y : ι → ℝ) :
      x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hAT,
      dotProduct_comm]
  have hcomplete (x : ι → ℝ) (r : ℝ) :
      d ^ 2 *
          (15 * (x ⬝ᵥ (A *ᵥ x)) +
            30 * r * (h ⬝ᵥ x) + Y * r ^ 2) =
        15 * ((d • x + r • v) ⬝ᵥ (A *ᵥ (d • x + r • v))) +
          d * (d * Y - 15 * (h ⬝ᵥ v)) * r ^ 2 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hrange]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    rw [hsymm v x, hrange, dotProduct_smul,
      dotProduct_comm v h, dotProduct_comm x h]
    simp only [smul_eq_mul]
    ring
  constructor
  · intro hall
    have htest := hall (-v) d
    have hidentity := hcomplete (-v) d
    have hzero : d • (-v) + d • v = 0 := by
      ext i
      simp
    rw [hzero, Matrix.mulVec_zero, zero_dotProduct] at hidentity
    have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
    have hd3 : 0 < d ^ 3 := pow_pos hd 3
    nlinarith
  · intro hbudget x r
    have hquadratic := hA.dotProduct_mulVec_nonneg (d • x + r • v)
    simp only [star_trivial] at hquadratic
    have hremaining :
        0 ≤ d * (d * Y - 15 * (h ⬝ᵥ v)) * r ^ 2 := by
      exact mul_nonneg
        (mul_nonneg hd.le (sub_nonneg.mpr hbudget)) (sq_nonneg r)
    have hidentity := hcomplete x r
    have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
    nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseScaledRangeCompletionStructural
