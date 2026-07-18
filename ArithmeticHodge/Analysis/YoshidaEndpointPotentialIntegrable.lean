import ArithmeticHodge.Analysis.YoshidaEndpointPotentialBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointPotentialIntegrable

open YoshidaEndpointPotentialBound

noncomputable section

/-- The logarithmic endpoint potential is integrable against the square of
every continuous centered profile. -/
theorem intervalIntegrable_endpointPotential_mul_sq
    (w : ℝ → ℝ) (hw : Continuous w) :
    IntervalIntegrable
      (fun x ↦ yoshidaEndpointPotential x * w x ^ 2) volume (-1) 1 := by
  have hlog : IntervalIntegrable Real.log volume 0 2 :=
    intervalIntegral.intervalIntegrable_log'
  have hminusBase : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 - x)) volume (-1) 1 := by
    convert (hlog.comp_sub_left 1).symm using 1 <;> norm_num
  have hplusBase : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 + x)) volume (-1) 1 := by
    convert hlog.comp_add_left 1 using 1 <;> norm_num
  have hwSq : Continuous (fun x : ℝ ↦ w x ^ 2) := hw.pow 2
  have hminus : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 - x) * w x ^ 2) volume (-1) 1 :=
    by simpa only [mul_comm] using
      hminusBase.continuousOn_mul hwSq.continuousOn
  have hplus : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 + x) * w x ^ 2) volume (-1) 1 :=
    by simpa only [mul_comm] using
      hplusBase.continuousOn_mul hwSq.continuousOn
  have hform : IntervalIntegrable
      (fun x : ℝ ↦ -(1 / 2 : ℝ) *
        (Real.log (1 - x) * w x ^ 2 + Real.log (1 + x) * w x ^ 2))
      volume (-1) 1 :=
    (hminus.add hplus).const_mul (-(1 / 2 : ℝ))
  have heq :
      (fun x : ℝ ↦ -(1 / 2 : ℝ) *
        (Real.log (1 - x) * w x ^ 2 + Real.log (1 + x) * w x ^ 2)) =ᵐ[volume]
      (fun x ↦ yoshidaEndpointPotential x * w x ^ 2) := by
    filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-1 : ℝ)] with x hx1 hxneg1
    have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    have hadd : 1 + x ≠ 0 := by
      intro hzero
      apply hxneg1
      linarith
    unfold yoshidaEndpointPotential
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
      Real.log_mul hsub hadd]
    ring
  exact hform.congr_ae
    (heq.filter_mono (ae_mono Measure.restrict_le_self))

/-- The logarithmic endpoint potential is integrable against every
continuous centered profile.  This is the polarization consequence of the
square-weight theorem. -/
theorem intervalIntegrable_endpointPotential_mul
    (u : ℝ → ℝ) (hu : Continuous u) :
    IntervalIntegrable
      (fun x ↦ yoshidaEndpointPotential x * u x) volume (-1) 1 := by
  have hplus := intervalIntegrable_endpointPotential_mul_sq
    (fun x ↦ u x + 1) (hu.add continuous_const)
  have huSq := intervalIntegrable_endpointPotential_mul_sq u hu
  have hone := intervalIntegrable_endpointPotential_mul_sq
    (fun _ : ℝ ↦ 1) continuous_const
  have hcomb := ((hplus.sub huSq).sub hone).const_mul (1 / 2 : ℝ)
  apply hcomb.congr
  intro x _hx
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointPotentialIntegrable
