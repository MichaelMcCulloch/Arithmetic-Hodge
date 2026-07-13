import ArithmeticHodge.Analysis.YoshidaEndpointEvenStructuralReduction
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialExactLowMode
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialIntegrable

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenLowPotential

open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialExactLowMode
open YoshidaEndpointPotentialIntegrable

noncomputable section

/-- Exact endpoint-potential mass of the constant centered mode. -/
theorem integral_endpointPotential_one :
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x) =
      2 - 2 * Real.log 2 := by
  let q : ℝ → ℝ := yoshidaEndpointPotential
  let r : ℝ → ℝ := fun x ↦ -(1 / 2 : ℝ) *
    (Real.log (1 - x) + Real.log (1 + x))
  have hpoint : ∀ᵐ x : ℝ ∂volume, q x = r x := by
    filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-1 : ℝ)] with x hx1 hxneg1
    have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    have hadd : 1 + x ≠ 0 := by
      intro hzero
      apply hxneg1
      linarith
    dsimp only [q, r, yoshidaEndpointPotential]
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
      Real.log_mul hsub hadd]
    ring
  have hlog : IntervalIntegrable Real.log volume 0 2 :=
    intervalIntegral.intervalIntegrable_log'
  have hminus : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 - x)) volume (-1) 1 := by
    convert (hlog.comp_sub_left 1).symm using 1 <;> norm_num
  have hplus : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 + x)) volume (-1) 1 := by
    convert hlog.comp_add_left 1 using 1 <;> norm_num
  have hminusVal :
      (∫ x : ℝ in -1..1, Real.log (1 - x)) =
        2 * Real.log 2 - 2 := by
    rw [intervalIntegral.integral_comp_sub_left,
      integral_log]
    norm_num
  have hplusVal :
      (∫ x : ℝ in -1..1, Real.log (1 + x)) =
        2 * Real.log 2 - 2 := by
    rw [intervalIntegral.integral_comp_add_left,
      integral_log]
    norm_num
  calc
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x) =
        ∫ x : ℝ in -1..1, r x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hpoint] with x hx _hxI
      simpa only [q] using hx
    _ = -(1 / 2 : ℝ) *
        ((∫ x : ℝ in -1..1, Real.log (1 - x)) +
          ∫ x : ℝ in -1..1, Real.log (1 + x)) := by
      dsimp only [r]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add hminus hplus]
    _ = 2 - 2 * Real.log 2 := by
      rw [hminusVal, hplusVal]
      ring

/-- Exact potential cross between the centered constant and `P₂` modes. -/
theorem integral_endpointPotential_mul_centeredEvenP2 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredEvenP2 x) = 1 / 3 := by
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredEvenP2 x) =
      fun x ↦ (3 / 2 : ℝ) *
          (yoshidaEndpointPotential x * x ^ 2) -
        (1 / 2 : ℝ) * yoshidaEndpointPotential x by
    funext x
    unfold centeredEvenP2
    ring]
  have hV : IntervalIntegrable yoshidaEndpointPotential volume (-1) 1 := by
    simpa only [one_pow, mul_one] using
      intervalIntegrable_endpointPotential_mul_sq
        (fun _ : ℝ ↦ 1) continuous_const
  have hVx2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq (fun x : ℝ ↦ x) continuous_id
  rw [intervalIntegral.integral_sub (hVx2.const_mul (3 / 2 : ℝ))
      (hV.const_mul (1 / 2 : ℝ)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_endpointPotential_mul_sq,
    integral_endpointPotential_one]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenLowPotential
