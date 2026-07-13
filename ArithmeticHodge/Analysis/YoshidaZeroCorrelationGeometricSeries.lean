import ArithmeticHodge.Analysis.YoshidaShiftedGeometricSeries
import ArithmeticHodge.Analysis.YoshidaStructuralKernelIntegrability

set_option autoImplicit false

open Filter MeasureTheory Real Set Topology

namespace ArithmeticHodge.Analysis.YoshidaZeroCorrelationGeometricSeries

noncomputable section

open YoshidaRenormalizedGeometricKernel
open YoshidaShiftedGeometricSeries
open YoshidaStructuralKernelIntegrability

/-!
# Structural geometric summation for a zero-trace correlation

When `C 0 = 0`, the harmonic counterterms disappear and the full odd
geometric series is the integral of `oddKernel * C`.  Differentiability gives
the removable factor `C(u) = u D(u)` needed for dominated convergence.
-/

theorem exists_continuous_removable_slope
    (C : ℝ → ℝ) (hC : ContDiff ℝ 1 C) :
    ∃ D : ℝ → ℝ, Continuous D ∧
      ∀ u : ℝ, C u = C 0 + u * D u := by
  let Q : ℝ → ℝ := fun u ↦ (C u - C 0) / u
  let D : ℝ → ℝ := Function.update Q 0 (deriv C 0)
  have hderiv : HasDerivAt C (deriv C 0) 0 :=
    (hC.differentiable (by norm_num) 0).hasDerivAt
  have hQzero : Tendsto Q (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (deriv C 0)) := by
    have h := hderiv.tendsto_slope_zero
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    dsimp only [Q]
    simp only [zero_add, smul_eq_mul, div_eq_inv_mul]
  have hD : Continuous D := by
    rw [continuous_iff_continuousAt]
    intro u
    by_cases hu : u = 0
    · subst u
      rw [show D = Function.update Q 0 (deriv C 0) by rfl,
        continuousAt_update_same]
      exact hQzero
    · rw [show D = Function.update Q 0 (deriv C 0) by rfl,
        continuousAt_update_of_ne hu]
      exact ((hC.continuous.continuousAt.sub continuousAt_const).div
        continuousAt_id hu)
  refine ⟨D, hD, ?_⟩
  intro u
  by_cases hu : u = 0
  · subst u
    simp
  · rw [show D u = Q u by simp [D, hu]]
    dsimp only [Q]
    field_simp [hu]
    ring

theorem zeroCorrelation_geometricSeries_hasSum
    {L : ℝ} (hL : 0 < L) (C : ℝ → ℝ)
    (hC : ContDiff ℝ 1 C) (hC0 : C 0 = 0) :
    HasSum (geometricIntegralTerm L C)
      (∫ u : ℝ in 0..L, oddKernel u * C u) := by
  obtain ⟨D, hD, hrem⟩ := exists_continuous_removable_slope C hC
  have hinterchange : PairedIntegralInterchange L 0 C := by
    apply pairedIntegralInterchange_of_removable hL hC.continuous
    · intro u _hu
      rw [← hC0]
      exact hrem u
    · exact removableMajorantLimit_intervalIntegrable hD 0 L
  have hstable : IntervalIntegrable
      (stableGeometricIntegrand 0 C) volume 0 L := by
    apply stableGeometricIntegrand_intervalIntegrable_of_removable
      hD 0 L
    intro u
    rw [← hC0]
    exact hrem u
  have href : IntervalIntegrable referenceRegularized volume 0 L :=
    referenceRegularized_intervalIntegrable L
  have hren := renormalizedSeries_hasSum_stable
    hL hC.continuous hinterchange hstable href
  convert hren using 1
  · funext k
    rw [renormalizedTerm_eq_geometricIntegralTerm]
    simp
  · simp only [stableGeometricIntegrand, zero_div, sub_zero, mul_zero,
      add_zero]

theorem zeroCorrelation_shifted_halfGeometric_hasSum
    {L : ℝ} (hL : 0 < L) (C : ℝ → ℝ)
    (hC : ContDiff ℝ 1 C) (hC0 : C 0 = 0) :
    HasSum (fun k : ℕ ↦ (1 / 2 : ℝ) *
        geometricIntegralTerm L C (k + 1))
      ((1 / 2 : ℝ) *
        ((∫ u : ℝ in 0..L, oddKernel u * C u) -
          geometricIntegralTerm L C 0)) := by
  have hfull := zeroCorrelation_geometricSeries_hasSum hL C hC hC0
  have htail : HasSum
      (fun k : ℕ ↦ geometricIntegralTerm L C (k + 1))
      ((∫ u : ℝ in 0..L, oddKernel u * C u) -
        geometricIntegralTerm L C 0) := by
    simpa only [Finset.sum_range_one] using
      (hasSum_nat_add_iff' 1).2 hfull
  exact htail.mul_left (1 / 2 : ℝ)

end

end ArithmeticHodge.Analysis.YoshidaZeroCorrelationGeometricSeries
