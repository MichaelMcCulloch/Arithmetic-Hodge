import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseScaledRangeCompletionStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseScaledRangePencilStructural

noncomputable section

open YoshidaFactorTwoPhaseScaledRangeCompletionStructural

/-!
# From a scaled range certificate to a scalar pencil

The cutoff-nine completion first proves a simultaneous quadratic estimate in
the nine low coordinates and one residual amplitude.  The outer low--tail
Schur handoff uses the same estimate after scaling the low coordinate vector
by an independent scalar.  This file records that lossless passage.
-/

/-- A positive-semidefinite low matrix, a scaled range witness for its mixed
linear functional, and the fraction-free Schur budget imply every scalar
low--tail pencil as soon as the tail complement retains `Y / 15`.

No inverse or positive-definiteness assumption is used. -/
theorem scaledRange_quadratic_pencil_nonneg
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (h v x : ι → ℝ) (d Y B : ℝ)
    (hA : A.PosSemidef)
    (hd : 0 < d)
    (hrange : A *ᵥ v = d • h)
    (hbudget : 15 * (h ⬝ᵥ v) ≤ d * Y)
    (htail : Y ≤ 15 * B) :
    ∀ c r : ℝ,
      0 ≤ (x ⬝ᵥ (A *ᵥ x)) * c ^ 2 +
        2 * (h ⬝ᵥ x) * c * r + B * r ^ 2 := by
  intro c r
  have hscaled :=
    (scaledRange_border_nonneg_iff A h v d Y hA hd hrange).2 hbudget
      (c • x) r
  have hlinear : h ⬝ᵥ (c • x) = c * (h ⬝ᵥ x) := by
    rw [dotProduct_smul]
    simp only [smul_eq_mul]
  have hquadratic :
      (c • x) ⬝ᵥ (A *ᵥ (c • x)) = c ^ 2 * (x ⬝ᵥ (A *ᵥ x)) := by
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  rw [hquadratic, hlinear] at hscaled
  have hremaining : 0 ≤ (15 * B - Y) * r ^ 2 :=
    mul_nonneg (sub_nonneg.mpr htail) (sq_nonneg r)
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseScaledRangePencilStructural
