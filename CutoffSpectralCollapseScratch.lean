import ArithmeticHodge.Spectral.CutoffHilbertSpace

open MeasureTheory

namespace ArithmeticHodge.Spectral.Cutoff

set_option autoImplicit false

/-- The current cutoff spectral pairing only samples the zero Fourier
frequency, because the placeholder cutoff Koopman group is the identity and
all of its enumerated eigenvalues are zero. -/
theorem spectralPairingOf_eq_zero_frequency_scratch
    (X : Type*) [Adelic.AdeleClassSpaceData X]
    (Λ : ℝ) (h : ℝ → ℝ) :
    spectralPairingOf X Λ h =
      Analysis.fourierCos h 0 * ∑' i, vacuumWeightOf X Λ i := by
  rw [spectralPairingOf]
  simp_rw [cutoffEigenvaluesOf_eq_zero X Λ]
  exact tsum_mul_left

/-- A translated proper-height cutoff cannot be invariant under the scaling
flow.  Thus restricting to this cutoff cannot itself produce a Koopman group
without changing the action or the boundary conditions. -/
theorem cutoffSet_not_scaling_invariant_scratch
    (X : Type*) [inst : Adelic.AdeleClassSpaceData X]
    (Λ : ℝ) :
    ∃ (t : ℝ) (x : X), x ∈ cutoffSet X Λ ∧
      inst.scalingFlow t x ∉ cutoffSet X Λ := by
  let R : ℝ := max 1 Λ
  refine ⟨R + 1, 1, ?_, ?_⟩
  · change |inst.heightFn (1 : X)| ≤ R
    rw [inst.heightFn_one, abs_zero]
    exact le_max_of_le_left zero_le_one
  · change ¬|inst.heightFn (inst.scalingFlow (R + 1) (1 : X))| ≤ R
    rw [inst.heightFn_scalingFlow, inst.heightFn_one, zero_add]
    have hR : 0 ≤ R := le_trans zero_le_one (le_max_left 1 Λ)
    rw [abs_of_nonneg (by linarith)]
    linarith

#print axioms spectralPairingOf_eq_zero_frequency_scratch
#print axioms cutoffSet_not_scaling_invariant_scratch
#print axioms spectralPairingOf_eq_zero_frequency
#print axioms cutoffSet_not_scaling_invariant

end ArithmeticHodge.Spectral.Cutoff
