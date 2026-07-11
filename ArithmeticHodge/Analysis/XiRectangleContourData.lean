import ArithmeticHodge.Analysis.XiZeroMultiplicity

/-!
# Finite xi-divisor data on rectangles

The finite xi-zero set supplies the support, multiplicity, and strict-interior
hypotheses needed by the rectangular argument principle.
-/

set_option autoImplicit false

open Complex Set

namespace ArithmeticHodge.Analysis

/-- Every point of nonzero xi order in the closed rectangle belongs to its
finite zero set. -/
theorem xi_meromorphicOrderAt_ne_zero_mem_xiZerosInRectangle
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) {s : ℂ}
    (hs : s ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper)
    (horder : meromorphicOrderAt xiFunction s ≠ 0) :
    s ∈ xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper := by
  rw [mem_xiZerosInRectangle_iff]
  refine ⟨hs, (xiZeroMultiplicity_pos_iff s).mp (Nat.pos_of_ne_zero ?_)⟩
  intro hzero
  apply horder
  rw [meromorphicOrderAt_xiFunction_eq_xiZeroMultiplicity, hzero]
  norm_num

/-- The divisor order of every listed xi zero is its natural analytic
multiplicity embedded in `WithTop ℤ`. -/
theorem xiZerosInRectangle_meromorphicOrderAt_eq_multiplicity
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) :
    ∀ rho ∈ xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper,
      meromorphicOrderAt xiFunction rho =
        ((xiZeroMultiplicity rho : ℤ) : WithTop ℤ) := by
  intro rho _
  exact meromorphicOrderAt_xiFunction_eq_xiZeroMultiplicity rho

/-- If xi has no zero on the boundary, every zero in the closed rectangle is
strictly interior. -/
theorem xiZerosInRectangle_strictInterior_of_boundary_zero_free
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ)
    (hboundary : ∀ s ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper,
      s.re = sigmaLower ∨ s.re = sigmaUpper ∨
        s.im = heightLower ∨ s.im = heightUpper →
      xiFunction s ≠ 0) :
    ∀ rho ∈ xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper,
      sigmaLower < rho.re ∧ rho.re < sigmaUpper ∧
        heightLower < rho.im ∧ rho.im < heightUpper := by
  intro rho hrho
  obtain ⟨hrho_rect, hrho_zero⟩ :=
    (mem_xiZerosInRectangle_iff
      sigmaLower sigmaUpper heightLower heightUpper rho).mp hrho
  have hre_lower_ne : rho.re ≠ sigmaLower := by
    intro hre
    exact (hboundary rho hrho_rect (Or.inl hre)) hrho_zero
  have hre_upper_ne : rho.re ≠ sigmaUpper := by
    intro hre
    exact (hboundary rho hrho_rect (Or.inr (Or.inl hre))) hrho_zero
  have him_lower_ne : rho.im ≠ heightLower := by
    intro him
    exact (hboundary rho hrho_rect (Or.inr (Or.inr (Or.inl him)))) hrho_zero
  have him_upper_ne : rho.im ≠ heightUpper := by
    intro him
    exact (hboundary rho hrho_rect (Or.inr (Or.inr (Or.inr him)))) hrho_zero
  rw [xiZeroRectangle, mem_reProdIm] at hrho_rect
  obtain ⟨⟨hre_lower, hre_upper⟩, him_lower, him_upper⟩ := hrho_rect
  exact ⟨lt_of_le_of_ne hre_lower hre_lower_ne.symm,
    lt_of_le_of_ne hre_upper hre_upper_ne,
    lt_of_le_of_ne him_lower him_lower_ne.symm,
    lt_of_le_of_ne him_upper him_upper_ne⟩

/-- Enlarging the real sides beyond the critical strip does not change the
finite xi-zero set at fixed heights. -/
theorem xiZerosInRectangle_outer_eq_critical
    {sigmaLower sigmaUpper heightLower heightUpper : ℝ}
    (hlower : sigmaLower ≤ 0) (hupper : 1 ≤ sigmaUpper) :
    xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper =
      xiZerosInRectangle 0 1 heightLower heightUpper := by
  ext z
  simp only [mem_xiZerosInRectangle_iff]
  constructor
  · rintro ⟨hzrect, hzero⟩
    have hre := xiFunction_zero_re hzero
    rw [xiZeroRectangle, mem_reProdIm] at hzrect ⊢
    exact ⟨⟨⟨hre.1.le, hre.2.le⟩, hzrect.2⟩, hzero⟩
  · rintro ⟨hzrect, hzero⟩
    rw [xiZeroRectangle, mem_reProdIm] at hzrect ⊢
    exact ⟨⟨⟨hlower.trans hzrect.1.1, hzrect.1.2.trans hupper⟩,
      hzrect.2⟩, hzero⟩

end ArithmeticHodge.Analysis
