import ArithmeticHodge.Adelic.ClassSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ArithmeticHodge.Adelic

set_option autoImplicit false

theorem no_AdeleClassSpaceData_scratch
    (X : Type*) [inst : AdeleClassSpaceData X] : False := by
  let A : Set X := {x | |inst.heightFn x| ≤ 1}
  let f : X → ℂ := A.indicator (fun _ ↦ 1)
  have hA_meas : MeasurableSet A :=
    inst.heightFn_measurable.norm measurableSet_Iic
  have hA_compact : IsCompact A := inst.heightFn_compact 1
  have hA_finite : inst.haarMeasure A < ⊤ := by
    haveI := inst.isHaar
    exact hA_compact.measure_lt_top
  have hf : Integrable f inst.haarMeasure := by
    change Integrable (A.indicator (fun _ ↦ (1 : ℂ))) inst.haarMeasure
    rw [integrable_indicator_iff hA_meas]
    exact integrableOn_const (C := (1 : ℂ)) hA_finite.ne
  obtain ⟨c, hc, hvolume⟩ := inst.heightFn_volume_growth
  have hA_pos : 0 < inst.haarMeasure A := by
    have hle : ENNReal.ofReal c ≤ inst.haarMeasure A := by
      simpa [A] using hvolume 1 le_rfl
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hc) hle
  have hcorr_zero : ∀ t : ℝ, 2 < t →
      ∫ x, f (inst.scalingFlow t x) * starRingEnd ℂ (f x) ∂inst.haarMeasure = 0 := by
    intro t ht
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ A
      · have hflow_not : inst.scalingFlow t x ∉ A := by
          intro hflow
          have hx_lower : -1 ≤ inst.heightFn x := (abs_le.mp hx).1
          have hflow_upper : inst.heightFn (inst.scalingFlow t x) ≤ 1 :=
            (abs_le.mp hflow).2
          rw [inst.heightFn_scalingFlow] at hflow_upper
          linarith
        change (if inst.scalingFlow t x ∈ A then 1 else 0) *
          starRingEnd ℂ (if x ∈ A then 1 else 0) = 0
        simp [hflow_not, hx]
      · change (if inst.scalingFlow t x ∈ A then 1 else 0) *
          starRingEnd ℂ (if x ∈ A then 1 else 0) = 0
        simp [hx]
  have htend_zero : Tendsto
      (fun t ↦ ∫ x, f (inst.scalingFlow t x) * starRingEnd ℂ (f x)
        ∂inst.haarMeasure) atTop (nhds 0) := by
    exact tendsto_atTop_of_eventually_const (i₀ := 3) fun t ht ↦
      hcorr_zero t (by linarith)
  have hmix := inst.scalingFlow_mixing f f hf hf
  have htarget_zero :
      (∫ x, f x ∂inst.haarMeasure) *
          starRingEnd ℂ (∫ x, f x ∂inst.haarMeasure) = 0 :=
    (tendsto_nhds_unique htend_zero hmix).symm
  have hintegral : ∫ x, f x ∂inst.haarMeasure =
      (inst.haarMeasure.real A : ℂ) := by
    simp [f, hA_meas]
    change ((inst.haarMeasure.real A : ℂ) * (1 : ℂ)) =
      (inst.haarMeasure.real A : ℂ)
    ring
  have hreal_pos : 0 < inst.haarMeasure.real A := by
    exact ENNReal.toReal_pos hA_pos.ne' hA_finite.ne
  rw [hintegral] at htarget_zero
  norm_num at htarget_zero
  exact hreal_pos.ne' htarget_zero

#print axioms no_AdeleClassSpaceData_scratch

end ArithmeticHodge.Adelic
