import ArithmeticHodge.Analysis.XiZeroMultiplicity

set_option autoImplicit false

open Complex Set

namespace ArithmeticHodge.Analysis

theorem xi_meromorphicOrderAt_ne_zero_mem_xiZerosInRectangle_scratch
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

theorem xiZerosInRectangle_meromorphicOrderAt_eq_multiplicity_scratch
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) :
    ∀ rho ∈ xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper,
      meromorphicOrderAt xiFunction rho =
        ((xiZeroMultiplicity rho : ℤ) : WithTop ℤ) := by
  intro rho _
  exact meromorphicOrderAt_xiFunction_eq_xiZeroMultiplicity rho

theorem xiZerosInRectangle_strictInterior_of_boundary_zero_free_scratch
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

#print axioms xi_meromorphicOrderAt_ne_zero_mem_xiZerosInRectangle_scratch
#print axioms xiZerosInRectangle_meromorphicOrderAt_eq_multiplicity_scratch
#print axioms xiZerosInRectangle_strictInterior_of_boundary_zero_free_scratch
#check xi_meromorphicOrderAt_ne_zero_mem_xiZerosInRectangle_scratch
#check xiZerosInRectangle_meromorphicOrderAt_eq_multiplicity_scratch
#check xiZerosInRectangle_strictInterior_of_boundary_zero_free_scratch

end ArithmeticHodge.Analysis
