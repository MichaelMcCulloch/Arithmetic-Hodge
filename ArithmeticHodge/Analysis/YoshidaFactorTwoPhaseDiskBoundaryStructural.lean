import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointChannelRadius

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDiskBoundaryStructural

noncomputable section

open YoshidaFactorTwoEndpointChannelRadius

/-!
# Structural reduction from the phase disk to its boundary

For a real affine phase functional, nonnegativity on the unit circle is
equivalent to the same sharp Euclidean-radius condition as nonnegativity on
the closed disk.  This avoids any angular subdivision or sampling.
-/

theorem real_unitCircle_phase_nonneg_iff_radius (Q P J : ℝ) :
    (∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      0 ≤ Q + a * P + b * J) ↔
      0 ≤ Q ∧ P ^ 2 + J ^ 2 ≤ Q ^ 2 := by
  constructor
  · intro hcircle
    have hnot : ¬∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧
        Q + a * P + b * J < 0 := by
      rintro ⟨a, b, hab, hneg⟩
      exact (not_lt_of_ge (hcircle a b hab)) hneg
    rw [real_unitCircle_phase_exists_neg_iff_radius] at hnot
    push_neg at hnot
    exact hnot
  · rintro ⟨hQ, hradius⟩ a b hab
    exact (real_closedDisk_phase_nonneg_iff_radius Q P J).2
      ⟨hQ, hradius⟩ a b hab.le

/-- An affine scalar phase nonnegative on the unit circle is nonnegative on
the whole closed disk. -/
theorem real_closedDisk_phase_nonneg_of_unitCircle
    (Q P J : ℝ)
    (hcircle : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      0 ≤ Q + a * P + b * J) :
    ∀ a b : ℝ, a ^ 2 + b ^ 2 ≤ 1 →
      0 ≤ Q + a * P + b * J := by
  exact (real_closedDisk_phase_nonneg_iff_radius Q P J).2
    ((real_unitCircle_phase_nonneg_iff_radius Q P J).1 hcircle)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDiskBoundaryStructural
