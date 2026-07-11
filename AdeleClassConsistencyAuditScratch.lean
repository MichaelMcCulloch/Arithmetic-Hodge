import ArithmeticHodge.Adelic.ClassSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ArithmeticHodge.Adelic

set_option autoImplicit false

/-- A positive finite height window whose translates eventually separate is
incompatible with a product-of-unnormalized-means correlation limit.  No Haar,
topological, invariance, flow-law, or continuity assumptions are used. -/
theorem translated_window_product_mixing_inconsistent_scratch
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (σ : ℝ → X → X) (height : X → ℝ)
    (hheight : Measurable height)
    (hfinite : μ {x | |height x| ≤ 1} < ⊤)
    (hpos : 0 < μ {x | |height x| ≤ 1})
    (htranslate : ∀ t x, height (σ t x) = height x + t)
    (hmixing : ∀ (f g : X → ℂ), Integrable f μ → Integrable g μ →
      Tendsto
        (fun t => ∫ x, f (σ t x) * starRingEnd ℂ (g x) ∂μ)
        atTop
        (nhds ((∫ x, f x ∂μ) * starRingEnd ℂ (∫ x, g x ∂μ)))) :
    False := by
  let A : Set X := {x | |height x| ≤ 1}
  let f : X → ℂ := A.indicator (fun _ ↦ 1)
  have hA_meas : MeasurableSet A := hheight.norm measurableSet_Iic
  have hf : Integrable f μ := by
    change Integrable (A.indicator (fun _ ↦ (1 : ℂ))) μ
    rw [integrable_indicator_iff hA_meas]
    exact integrableOn_const (C := (1 : ℂ)) hfinite.ne
  have hcorr_zero : ∀ t : ℝ, 2 < t →
      ∫ x, f (σ t x) * starRingEnd ℂ (f x) ∂μ = 0 := by
    intro t ht
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ A
      · have hflow_not : σ t x ∉ A := by
          intro hflow
          have hx_lower : -1 ≤ height x := (abs_le.mp hx).1
          have hflow_upper : height (σ t x) ≤ 1 := (abs_le.mp hflow).2
          rw [htranslate] at hflow_upper
          linarith
        change (if σ t x ∈ A then 1 else 0) *
          starRingEnd ℂ (if x ∈ A then 1 else 0) = 0
        simp [hflow_not, hx]
      · change (if σ t x ∈ A then 1 else 0) *
          starRingEnd ℂ (if x ∈ A then 1 else 0) = 0
        simp [hx]
  have htend_zero : Tendsto
      (fun t ↦ ∫ x, f (σ t x) * starRingEnd ℂ (f x) ∂μ)
      atTop (nhds 0) := by
    exact tendsto_atTop_of_eventually_const (i₀ := 3) fun t ht ↦
      hcorr_zero t (by linarith)
  have hmix := hmixing f f hf hf
  have htarget_zero :
      (∫ x, f x ∂μ) * starRingEnd ℂ (∫ x, f x ∂μ) = 0 :=
    (tendsto_nhds_unique htend_zero hmix).symm
  have hintegral : ∫ x, f x ∂μ = (μ.real A : ℂ) := by
    simp [f, hA_meas]
    change ((μ.real A : ℂ) * (1 : ℂ)) = (μ.real A : ℂ)
    ring
  have hreal_pos : 0 < μ.real A :=
    ENNReal.toReal_pos hpos.ne' hfinite.ne
  rw [hintegral] at htarget_zero
  norm_num at htarget_zero
  exact hreal_pos.ne' htarget_zero

/-- The current class supplies the generic contradiction using exactly:
`heightFn_measurable`, `isHaar` plus `heightFn_compact` for local finiteness,
`heightFn_volume_growth` for positive mass, `heightFn_scalingFlow` for
separation, and `scalingFlow_mixing` for the conflicting limit. -/
theorem no_AdeleClassSpaceData_consistency_audit_scratch
    (X : Type*) [inst : AdeleClassSpaceData X] : False := by
  apply translated_window_product_mixing_inconsistent_scratch
    (μ := inst.haarMeasure)
    (σ := fun t x => inst.scalingFlow t x)
    (height := inst.heightFn)
  · exact inst.heightFn_measurable
  · haveI := inst.isHaar
    exact (inst.heightFn_compact 1).measure_lt_top
  · obtain ⟨c, hc, hvolume⟩ := inst.heightFn_volume_growth
    have hle : ENNReal.ofReal c ≤
        inst.haarMeasure {x : X | |inst.heightFn x| ≤ 1} := by
      simpa using hvolume 1 le_rfl
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hc) hle
  · exact inst.heightFn_scalingFlow
  · intro f g hf hg
    exact inst.scalingFlow_mixing f g hf hg

theorem AdeleClassSpaceData_isEmpty_consistency_audit_scratch
    (X : Type*) : IsEmpty (AdeleClassSpaceData X) := by
  constructor
  intro inst
  letI : AdeleClassSpaceData X := inst
  exact no_AdeleClassSpaceData_consistency_audit_scratch X

#print axioms translated_window_product_mixing_inconsistent_scratch
#print axioms no_AdeleClassSpaceData_consistency_audit_scratch
#print axioms AdeleClassSpaceData_isEmpty_consistency_audit_scratch

end ArithmeticHodge.Adelic
