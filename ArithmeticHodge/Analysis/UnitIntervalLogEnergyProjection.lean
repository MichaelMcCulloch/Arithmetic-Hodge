import ArithmeticHodge.Analysis.ShiftedLogKernelCrossEnergy
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false

open MeasureTheory Polynomial
open scoped unitInterval

namespace ArithmeticHodge.Analysis.UnitIntervalLogEnergyProjection

open ShiftedLegendreLogKernel
open ShiftedLogKernelCrossEnergy

noncomputable section

/-!
# Residual positivity for the unit-interval logarithmic form

The raw singular energy of a finite-energy function dominates the polynomial
energy of any polynomial satisfying the exact projection pairing.  The proof
expands the nonnegative energy of the residual and uses the structural cross
identity; it does not assume continuity of the singular form in `L²`.
-/

/-- Raw logarithmic energy density on the unit square. -/
def unitIntervalRawLogEnergyIntegrand
    (f : unitInterval → ℝ) (z : unitInterval × unitInterval) : ℝ :=
  (f z.1 - f z.2) ^ 2 / |(z.1 : ℝ) - (z.2 : ℝ)|

/-- Half of the raw double energy, normalized to agree with
`integral p * shiftedLogKernel p` on polynomials. -/
def unitIntervalLogEnergy (f : unitInterval → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ z : unitInterval × unitInterval,
    unitIntervalRawLogEnergyIntegrand f z

private theorem integrable_polynomial_eval (p : ℝ[X]) :
    Integrable (fun x : unitInterval ↦ p.eval (x : ℝ)) := by
  exact (p.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integrable_unitIntervalRawLogEnergyIntegrand_polynomial
    (p : ℝ[X]) :
    Integrable (unitIntervalRawLogEnergyIntegrand
      (fun x : unitInterval ↦ p.eval (x : ℝ))) := by
  have hcross := integrable_sub_mul_unitIntervalRawPolynomialLogKernel
    (fun x : unitInterval ↦ p.eval (x : ℝ))
      (integrable_polynomial_eval p) p
  apply hcross.congr
  filter_upwards [] with z
  unfold unitIntervalRawLogEnergyIntegrand
    unitIntervalRawPolynomialLogKernel
  ring

theorem integral_unitIntervalRawLogEnergyIntegrand_polynomial
    (p : ℝ[X]) :
    (∫ z : unitInterval × unitInterval,
      unitIntervalRawLogEnergyIntegrand
        (fun x : unitInterval ↦ p.eval (x : ℝ)) z) =
      2 * ∫ x : unitInterval,
        p.eval (x : ℝ) * (shiftedLogKernel p).eval (x : ℝ) := by
  calc
    _ = ∫ z : unitInterval × unitInterval,
        (p.eval (z.1 : ℝ) - p.eval (z.2 : ℝ)) *
          unitIntervalRawPolynomialLogKernel p z := by
      apply integral_congr_ae
      filter_upwards [] with z
      unfold unitIntervalRawLogEnergyIntegrand
        unitIntervalRawPolynomialLogKernel
      ring
    _ = _ := integral_sub_mul_unitIntervalRawPolynomialLogKernel_eq
      (fun x : unitInterval ↦ p.eval (x : ℝ))
        (integrable_polynomial_eval p) p

/-- Residual positivity: an exact polynomial projection pairing is bounded
by the full finite logarithmic energy. -/
theorem polynomial_pairing_le_unitIntervalLogEnergy
    (f : unitInterval → ℝ) (hf : Integrable f)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand f))
    (p : ℝ[X])
    (hprojection :
      (∫ x : unitInterval,
        f x * (shiftedLogKernel p).eval (x : ℝ)) =
      ∫ x : unitInterval,
        p.eval (x : ℝ) * (shiftedLogKernel p).eval (x : ℝ)) :
    (∫ x : unitInterval,
      p.eval (x : ℝ) * (shiftedLogKernel p).eval (x : ℝ)) ≤
        unitIntervalLogEnergy f := by
  let pf : unitInterval → ℝ := fun x ↦ p.eval (x : ℝ)
  let cross : unitInterval × unitInterval → ℝ := fun z ↦
    (f z.1 - f z.2) * unitIntervalRawPolynomialLogKernel p z
  let residual : unitInterval → ℝ := fun x ↦ f x - pf x
  have hpolyEnergy : Integrable
      (unitIntervalRawLogEnergyIntegrand pf) := by
    simpa only [pf] using
      integrable_unitIntervalRawLogEnergyIntegrand_polynomial p
  have hcross : Integrable cross := by
    simpa only [cross] using
      integrable_sub_mul_unitIntervalRawPolynomialLogKernel f hf p
  have hcombo : Integrable (fun z : unitInterval × unitInterval ↦
      unitIntervalRawLogEnergyIntegrand f z +
        unitIntervalRawLogEnergyIntegrand pf z - 2 * cross z) :=
    (henergy.add hpolyEnergy).sub (hcross.const_mul 2)
  have hresidual : Integrable
      (unitIntervalRawLogEnergyIntegrand residual) := by
    apply hcombo.congr
    filter_upwards [] with z
    dsimp only [residual, pf, cross]
    unfold unitIntervalRawLogEnergyIntegrand
      unitIntervalRawPolynomialLogKernel
    ring
  have hresidual_nonneg :
      0 ≤ ∫ z : unitInterval × unitInterval,
        unitIntervalRawLogEnergyIntegrand residual z := by
    apply integral_nonneg
    intro z
    exact div_nonneg (sq_nonneg _) (abs_nonneg _)
  have hresidual_expand :
      (∫ z : unitInterval × unitInterval,
        unitIntervalRawLogEnergyIntegrand residual z) =
      (∫ z : unitInterval × unitInterval,
        unitIntervalRawLogEnergyIntegrand f z) +
      (∫ z : unitInterval × unitInterval,
        unitIntervalRawLogEnergyIntegrand pf z) -
      2 * ∫ z : unitInterval × unitInterval, cross z := by
    calc
      _ = ∫ z : unitInterval × unitInterval,
          unitIntervalRawLogEnergyIntegrand f z +
            unitIntervalRawLogEnergyIntegrand pf z - 2 * cross z := by
        apply integral_congr_ae
        filter_upwards [] with z
        dsimp only [residual, pf, cross]
        unfold unitIntervalRawLogEnergyIntegrand
          unitIntervalRawPolynomialLogKernel
        ring
      _ = (∫ z : unitInterval × unitInterval,
            unitIntervalRawLogEnergyIntegrand f z +
              unitIntervalRawLogEnergyIntegrand pf z) -
          ∫ z : unitInterval × unitInterval, 2 * cross z := by
        exact integral_sub (henergy.add hpolyEnergy) (hcross.const_mul 2)
      _ = ((∫ z : unitInterval × unitInterval,
              unitIntervalRawLogEnergyIntegrand f z) +
            ∫ z : unitInterval × unitInterval,
              unitIntervalRawLogEnergyIntegrand pf z) -
          ∫ z : unitInterval × unitInterval, 2 * cross z := by
        rw [integral_add henergy hpolyEnergy]
      _ = _ := by rw [integral_const_mul]
  have hpolyIdentity :
      (∫ z : unitInterval × unitInterval,
        unitIntervalRawLogEnergyIntegrand pf z) =
      2 * ∫ x : unitInterval,
        p.eval (x : ℝ) * (shiftedLogKernel p).eval (x : ℝ) := by
    simpa only [pf] using
      integral_unitIntervalRawLogEnergyIntegrand_polynomial p
  have hcrossIdentity :
      (∫ z : unitInterval × unitInterval, cross z) =
      2 * ∫ x : unitInterval,
        f x * (shiftedLogKernel p).eval (x : ℝ) := by
    simpa only [cross] using
      integral_sub_mul_unitIntervalRawPolynomialLogKernel_eq f hf p
  rw [hresidual_expand, hpolyIdentity, hcrossIdentity,
    hprojection] at hresidual_nonneg
  unfold unitIntervalLogEnergy
  linarith

end

end ArithmeticHodge.Analysis.UnitIntervalLogEnergyProjection
