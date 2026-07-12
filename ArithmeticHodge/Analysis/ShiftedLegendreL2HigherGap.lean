import ArithmeticHodge.Analysis.ShiftedLegendreL2SpectralGap
import ArithmeticHodge.Analysis.ShiftedLegendreFiniteEnergyGap

set_option autoImplicit false

open Finset Filter
open scoped BigOperators Topology

namespace ArithmeticHodge.Analysis.ShiftedLegendreL2HigherGap

open ShiftedLegendreL2Basis
open ShiftedLegendreL2SpectralGap
open ShiftedLegendreFiniteEnergyGap
open UnitIntervalLogEnergyProjection

noncomputable section

/-!
# Uniform higher-mode shifted-Legendre gaps

Removing every coefficient below `k` raises the logarithmic spectral gap to
the exact harmonic weight `2 * H_k`.  The statement controls the complete
infinite tail through Hilbert-basis convergence, not a chosen truncation.
-/

theorem harmonic_cast_mono {m n : ℕ} (hmn : m ≤ n) :
    (harmonic m : ℝ) ≤ (harmonic n : ℝ) := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih =>
      rw [harmonic_succ]
      push_cast
      exact ih.trans (le_add_of_nonneg_right (by positivity))

theorem harmonic_mul_partialNormSq_le_partialSpectralEnergy
    (F : UnitIntervalL2) (k N : ℕ)
    (hlow : ∀ n < k, shiftedLegendreHilbertBasis.repr F n = 0) :
    (2 * (harmonic k : ℝ)) * shiftedLegendrePartialNormSq F N ≤
      shiftedLegendrePartialSpectralEnergy F N := by
  rw [shiftedLegendrePartialNormSq,
    shiftedLegendrePartialSpectralEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hnk : n < k
  · rw [hlow n hnk]
    simp
  · have hkn : k ≤ n := Nat.le_of_not_gt hnk
    have hH : (2 * (harmonic k : ℝ)) ≤
        2 * (harmonic n : ℝ) := by
      nlinarith [harmonic_cast_mono hkn]
    exact mul_le_mul_of_nonneg_right hH (sq_nonneg _)

/-- Any quantity dominating all finite spectral energies controls the full
`L²` norm with the exact first surviving harmonic weight. -/
theorem harmonic_mul_norm_sq_le_of_partialSpectralEnergy_le
    (F : UnitIntervalL2) (k : ℕ)
    (hlow : ∀ n < k, shiftedLegendreHilbertBasis.repr F n = 0)
    (Q : ℝ)
    (hQ : ∀ N : ℕ, shiftedLegendrePartialSpectralEnergy F N ≤ Q) :
    (2 * (harmonic k : ℝ)) * ‖F‖ ^ 2 ≤ Q := by
  apply le_of_tendsto
    ((tendsto_shiftedLegendrePartialNormSq F).const_mul
      (2 * (harmonic k : ℝ)))
  exact Filter.Eventually.of_forall fun N ↦
    (harmonic_mul_partialNormSq_le_partialSpectralEnergy F k N hlow).trans
      (hQ N)

/-- The normalized unit-interval logarithmic energy inherits the exact
higher-mode gap. -/
theorem harmonic_mul_integral_sq_le_unitIntervalLogEnergy
    (f : unitInterval → ℝ)
    (hf : MeasureTheory.MemLp f 2)
    (henergy : MeasureTheory.Integrable
      (unitIntervalRawLogEnergyIntegrand f))
    (k : ℕ)
    (hlow : ∀ n < k,
      shiftedLegendreHilbertBasis.repr (hf.toLp f) n = 0) :
    (2 * (harmonic k : ℝ)) *
        (∫ x : unitInterval, f x ^ 2) ≤
      unitIntervalLogEnergy f := by
  rw [← norm_sq_toLp_eq_integral_sq f hf]
  exact harmonic_mul_norm_sq_le_of_partialSpectralEnergy_le
    (hf.toLp f) k hlow (unitIntervalLogEnergy f)
      (partialSpectralEnergy_le_unitIntervalLogEnergy f hf henergy)

end

end ArithmeticHodge.Analysis.ShiftedLegendreL2HigherGap
