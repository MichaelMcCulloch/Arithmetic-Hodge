import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellParityStructural
import ArithmeticHodge.Analysis.YoshidaEndpointRegularCorrelation

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellWidthPerturbationStructural

noncomputable section

open CenteredEndpointCorrelation
open MultiplicativeWeilFourCellRealRescaleStructural
open MultiplicativeWeilFourCellSingleProfileStructural
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPolarScaling
open YoshidaEndpointRegularCorrelation
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaRegularKernelBound

/-!
# The exact width perturbation in the four-cell endpoint form

The standard clean endpoint quadratic lives at halfwidth
`yoshidaEndpointA = log 2 / 2`, while the complete four-cell profile has
halfwidth `5 * log 2 / 8`.  This file keeps the change of regular kernel,
polar moments, scalar mass, and the retained prime-two pairing in one signed
quadratic perturbation.
-/

/-- The clean quadratic is exactly the arbitrary-width physical quadratic at
the standard endpoint halfwidth. -/
theorem centeredClippedPhysicalQuadratic_endpointA_eq_clean
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredClippedPhysicalQuadratic yoshidaEndpointA w =
      yoshidaEndpointOddCleanQuadratic w := by
  have hregular :=
    re_yoshidaEndpointRegularQuadratic_eq_correlation w hw
  have hpolar :=
    two_mul_endpointA_sq_mul_polarMoments_eq w hw
  have hA : yoshidaEndpointA ≠ 0 := yoshidaEndpointA_pos.ne'
  have hpolar' :
      2 * yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            Real.exp (-yoshidaEndpointA * x / 2) * w x) *
          (∫ x : ℝ in -1..1,
            Real.exp (yoshidaEndpointA * x / 2) * w x) =
        yoshidaEndpointHyperbolicQuadratic (fun x ↦ (w x : ℂ)) := by
    apply (mul_left_cancel₀ hA)
    calc
      yoshidaEndpointA *
            (2 * yoshidaEndpointA *
              (∫ x : ℝ in -1..1,
                Real.exp (-yoshidaEndpointA * x / 2) * w x) *
              (∫ x : ℝ in -1..1,
                Real.exp (yoshidaEndpointA * x / 2) * w x)) =
          2 * yoshidaEndpointA ^ 2 *
            (∫ x : ℝ in -1..1,
              Real.exp (-yoshidaEndpointA * x / 2) * w x) *
            (∫ x : ℝ in -1..1,
              Real.exp (yoshidaEndpointA * x / 2) * w x) := by ring
      _ = yoshidaEndpointA *
          yoshidaEndpointHyperbolicQuadratic (fun x ↦ (w x : ℂ)) := hpolar
  have htwoA : 2 * yoshidaEndpointA = Real.log 2 := by
    unfold yoshidaEndpointA
    ring
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hscalar :
      Real.log (2 * yoshidaEndpointA) +
          Real.eulerMascheroniConstant + Real.log Real.pi =
        yoshidaEndpointScalarMassLoss := by
    rw [htwoA]
    unfold yoshidaEndpointScalarMassLoss
    rw [Real.log_mul Real.pi_ne_zero hlogTwo]
    ring
  unfold centeredClippedPhysicalQuadratic
  unfold yoshidaEndpointOddCleanQuadratic
  dsimp only
  rw [hregular, hpolar', hscalar]
  ring

/-- The complete signed change from the clean endpoint width to the
four-cell width, including the retained prime-two endpoint pairing. -/
def fourCellWidthPrimePerturbation (w : ℝ → ℝ) : ℝ :=
  centeredClippedPhysicalQuadratic (5 * Real.log 2 / 8) w -
    centeredClippedPhysicalQuadratic yoshidaEndpointA w -
    Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w

/-- Exact clean-plus-perturbation decomposition of the normalized four-cell
bracket.  No term has been estimated independently. -/
theorem fourCell_centeredPhysical_sub_pairing_eq_clean_add_perturbation
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredClippedPhysicalQuadratic (5 * Real.log 2 / 8) w -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w =
      yoshidaEndpointOddCleanQuadratic w +
        fourCellWidthPrimePerturbation w := by
  rw [← centeredClippedPhysicalQuadratic_endpointA_eq_clean w hw]
  unfold fourCellWidthPrimePerturbation
  ring

/-- The scalar loss created by enlarging the endpoint halfwidth from
`log 2 / 2` to `5 * log 2 / 8` is exactly `log (5 / 4)`. -/
theorem fourCellScalarWidthShift_eq :
    Real.log (2 * (5 * Real.log 2 / 8)) -
        Real.log (2 * yoshidaEndpointA) =
      Real.log (5 / 4 : ℝ) := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [show 2 * (5 * Real.log 2 / 8) =
      (5 / 4 : ℝ) * Real.log 2 by ring]
  rw [show 2 * yoshidaEndpointA = Real.log 2 by
    unfold yoshidaEndpointA
    ring]
  rw [Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) hlogTwo]
  ring

/-- Definition-level expansion of the perturbation.  It records the exact
scalar, regular-kernel, polar, and prime channels that a coupled Schur bound
must control. -/
theorem fourCellWidthPrimePerturbation_eq
    (w : ℝ → ℝ) :
    fourCellWidthPrimePerturbation w =
      -Real.log (5 / 4 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) -
      2 * (5 * Real.log 2 / 8) *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) *
            centeredEndpointCorrelation w t) +
      2 * yoshidaEndpointA *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (yoshidaEndpointA * t) *
            centeredEndpointCorrelation w t) +
      2 * (5 * Real.log 2 / 8) *
        (∫ x : ℝ in -1..1,
          Real.exp (-(5 * Real.log 2 / 8) * x / 2) * w x) *
        (∫ x : ℝ in -1..1,
          Real.exp ((5 * Real.log 2 / 8) * x / 2) * w x) -
      2 * yoshidaEndpointA *
        (∫ x : ℝ in -1..1,
          Real.exp (-yoshidaEndpointA * x / 2) * w x) *
        (∫ x : ℝ in -1..1,
          Real.exp (yoshidaEndpointA * x / 2) * w x) -
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  rw [← fourCellScalarWidthShift_eq]
  unfold fourCellWidthPrimePerturbation
  unfold centeredClippedPhysicalQuadratic
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellWidthPerturbationStructural
