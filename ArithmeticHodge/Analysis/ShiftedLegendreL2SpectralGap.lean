import ArithmeticHodge.Analysis.ShiftedLegendreL2Basis
import ArithmeticHodge.Analysis.ShiftedLegendreLogEigen

set_option autoImplicit false

open Finset Filter
open scoped BigOperators InnerProductSpace Topology

namespace ArithmeticHodge.Analysis.ShiftedLegendreL2SpectralGap

open ShiftedLegendreL2Basis

noncomputable section

/-!
# The complete coefficient-space shifted-Legendre gap

Finite Hilbert-basis projections converge in `L²`.  Once the constant
coefficient vanishes, every remaining logarithmic eigenvalue is at least
`2`; consequently any quadratic quantity dominating all finite spectral
energies dominates twice the full `L²` norm.  This isolates the exact bridge
that the raw singular form must supply.
-/

/-- Squared `L²` mass of the first `N` shifted-Legendre coefficients. -/
def shiftedLegendrePartialNormSq (f : UnitIntervalL2) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (shiftedLegendreHilbertBasis.repr f n) ^ 2

/-- Logarithmic spectral energy of the first `N` shifted-Legendre
coefficients. -/
def shiftedLegendrePartialSpectralEnergy
    (f : UnitIntervalL2) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (2 * (harmonic n : ℝ)) *
      (shiftedLegendreHilbertBasis.repr f n) ^ 2

/-- The finite Hilbert-basis projection through degrees `< N`. -/
def shiftedLegendrePartialProjection
    (f : UnitIntervalL2) (N : ℕ) : UnitIntervalL2 :=
  ∑ n ∈ Finset.range N,
    shiftedLegendreHilbertBasis.repr f n •
      shiftedLegendreHilbertBasis n

theorem norm_sq_shiftedLegendrePartialProjection
    (f : UnitIntervalL2) (N : ℕ) :
    ‖shiftedLegendrePartialProjection f N‖ ^ 2 =
      shiftedLegendrePartialNormSq f N := by
  have hinner := shiftedLegendreHilbertBasis.orthonormal.inner_sum
    (fun n ↦ shiftedLegendreHilbertBasis.repr f n)
    (fun n ↦ shiftedLegendreHilbertBasis.repr f n)
    (Finset.range N)
  rw [real_inner_self_eq_norm_sq] at hinner
  simpa only [shiftedLegendrePartialProjection,
    shiftedLegendrePartialNormSq, RCLike.star_def, RCLike.conj_to_real,
    map_id, id_eq, pow_two] using hinner

theorem tendsto_shiftedLegendrePartialProjection
    (f : UnitIntervalL2) :
    Tendsto (shiftedLegendrePartialProjection f) atTop (nhds f) := by
  exact shiftedLegendreHilbertBasis.hasSum_repr f |>.tendsto_sum_nat

theorem tendsto_shiftedLegendrePartialNormSq
    (f : UnitIntervalL2) :
    Tendsto (shiftedLegendrePartialNormSq f) atTop (nhds (‖f‖ ^ 2)) := by
  have hnorm : Tendsto
      (fun N ↦ ‖shiftedLegendrePartialProjection f N‖)
      atTop (nhds ‖f‖) :=
    tendsto_norm.comp (tendsto_shiftedLegendrePartialProjection f)
  have hsquare := hnorm.pow 2
  simpa only [norm_sq_shiftedLegendrePartialProjection] using hsquare

private theorem one_le_harmonic_cast_of_pos
    {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) ≤ (harmonic n : ℝ) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hnzero : n = 0
      · subst n
        norm_num [harmonic]
      · have hprev : (1 : ℝ) ≤ (harmonic n : ℝ) :=
          ih (Nat.pos_of_ne_zero hnzero)
        rw [harmonic_succ]
        push_cast
        exact hprev.trans (le_add_of_nonneg_right (by positivity))

theorem two_mul_partialNormSq_le_partialSpectralEnergy
    (f : UnitIntervalL2)
    (hzero : shiftedLegendreHilbertBasis.repr f 0 = 0)
    (N : ℕ) :
    2 * shiftedLegendrePartialNormSq f N ≤
      shiftedLegendrePartialSpectralEnergy f N := by
  rw [shiftedLegendrePartialNormSq,
    shiftedLegendrePartialSpectralEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hnzero : n = 0
  · subst n
    simp [hzero]
  · have hH : (1 : ℝ) ≤ (harmonic n : ℝ) :=
      one_le_harmonic_cast_of_pos (Nat.pos_of_ne_zero hnzero)
    have hlambda : (2 : ℝ) ≤ 2 * (harmonic n : ℝ) := by
      linarith
    exact mul_le_mul_of_nonneg_right hlambda (sq_nonneg _)

/-- A bound for every finite logarithmic spectral energy controls the full
zero-mode-free `L²` norm. -/
theorem two_mul_norm_sq_le_of_partialSpectralEnergy_le
    (f : UnitIntervalL2)
    (hzero : shiftedLegendreHilbertBasis.repr f 0 = 0)
    (Q : ℝ)
    (hQ : ∀ N : ℕ, shiftedLegendrePartialSpectralEnergy f N ≤ Q) :
    2 * ‖f‖ ^ 2 ≤ Q := by
  apply le_of_tendsto
    ((tendsto_shiftedLegendrePartialNormSq f).const_mul 2)
  exact Filter.Eventually.of_forall fun N ↦
    (two_mul_partialNormSq_le_partialSpectralEnergy f hzero N).trans (hQ N)

end

end ArithmeticHodge.Analysis.ShiftedLegendreL2SpectralGap
