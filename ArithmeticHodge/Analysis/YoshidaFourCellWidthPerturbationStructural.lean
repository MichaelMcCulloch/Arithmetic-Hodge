import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellParityStructural
import ArithmeticHodge.Analysis.YoshidaEndpointRegularCorrelation
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCoercivity

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
open YoshidaFactorTwoPhaseSymmetricCoercivity
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

/-- The two real exponential moments form exactly one even hyperbolic square
minus one odd hyperbolic square. -/
theorem centeredPolarMoments_mul_eq_cosh_sq_sub_sinh_sq
    (w : ℝ → ℝ) (hw : Continuous w) (a : ℝ) :
    (∫ x : ℝ in -1..1, Real.exp (-a * x / 2) * w x) *
        (∫ x : ℝ in -1..1, Real.exp (a * x / 2) * w x) =
      centeredCoshMoment w (a / 2) ^ 2 -
        centeredSinhMoment w (a / 2) ^ 2 := by
  have hcosh : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh ((a / 2) * x) * w x) volume (-1) 1 :=
    (by fun_prop : Continuous
      (fun x : ℝ ↦ Real.cosh ((a / 2) * x) * w x)).intervalIntegrable _ _
  have hsinh : IntervalIntegrable
      (fun x : ℝ ↦ Real.sinh ((a / 2) * x) * w x) volume (-1) 1 :=
    (by fun_prop : Continuous
      (fun x : ℝ ↦ Real.sinh ((a / 2) * x) * w x)).intervalIntegrable _ _
  have hminus :
      (∫ x : ℝ in -1..1, Real.exp (-a * x / 2) * w x) =
        centeredCoshMoment w (a / 2) -
          centeredSinhMoment w (a / 2) := by
    rw [show (fun x : ℝ ↦ Real.exp (-a * x / 2) * w x) =
        fun x ↦ Real.cosh ((a / 2) * x) * w x -
          Real.sinh ((a / 2) * x) * w x by
      funext x
      rw [show -a * x / 2 = -((a / 2) * x) by ring,
        ← Real.cosh_sub_sinh]
      ring]
    rw [intervalIntegral.integral_sub hcosh hsinh]
    rfl
  have hplus :
      (∫ x : ℝ in -1..1, Real.exp (a * x / 2) * w x) =
        centeredCoshMoment w (a / 2) +
          centeredSinhMoment w (a / 2) := by
    rw [show (fun x : ℝ ↦ Real.exp (a * x / 2) * w x) =
        fun x ↦ Real.cosh ((a / 2) * x) * w x +
          Real.sinh ((a / 2) * x) * w x by
      funext x
      rw [show a * x / 2 = (a / 2) * x by ring,
        ← Real.cosh_add_sinh]
      ring]
    rw [intervalIntegral.integral_add hcosh hsinh]
    rfl
  rw [hminus, hplus]
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

/-- Rank-square normal form of the exact perturbation.  This is the form used
by the parity-sector Schur problem. -/
theorem fourCellWidthPrimePerturbation_eq_rankSquares
    (w : ℝ → ℝ) (hw : Continuous w) :
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
        (centeredCoshMoment w ((5 * Real.log 2 / 8) / 2) ^ 2 -
          centeredSinhMoment w ((5 * Real.log 2 / 8) / 2) ^ 2) -
      2 * yoshidaEndpointA *
        (centeredCoshMoment w (yoshidaEndpointA / 2) ^ 2 -
          centeredSinhMoment w (yoshidaEndpointA / 2) ^ 2) -
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  rw [fourCellWidthPrimePerturbation_eq]
  have hwide := centeredPolarMoments_mul_eq_cosh_sq_sub_sinh_sq
    w hw (5 * Real.log 2 / 8)
  have hclean := centeredPolarMoments_mul_eq_cosh_sq_sub_sinh_sq
    w hw yoshidaEndpointA
  linear_combination
    2 * (5 * Real.log 2 / 8) * hwide -
      2 * yoshidaEndpointA * hclean

/-- On an even profile the polar change is the difference of two positive
cosh ranks, and the prime loss is the matched endpoint fold. -/
theorem fourCellWidthPrimePerturbation_eq_evenRanks
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
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
        centeredCoshMoment w ((5 * Real.log 2 / 8) / 2) ^ 2 -
      2 * yoshidaEndpointA *
        centeredCoshMoment w (yoshidaEndpointA / 2) ^ 2 -
      Real.sqrt 2 * Real.log 2 * endpointFoldedCorrelation w (2 / 5) := by
  rw [fourCellWidthPrimePerturbation_eq_rankSquares w hw,
    centeredSinhMoment_eq_zero_of_even heven,
    centeredSinhMoment_eq_zero_of_even heven,
    fourCellEndpointPairing_eq_centeredEndpointCorrelation,
    show (8 / 5 : ℝ) = 2 - 2 / 5 by norm_num,
    centeredCorrelation_two_sub_eq_endpointFolded_of_even heven]
  ring

/-- On an odd profile the polar change is the opposite difference of sinh
ranks, while the prime channel is the antimatched endpoint fold. -/
theorem fourCellWidthPrimePerturbation_eq_oddRanks
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    fourCellWidthPrimePerturbation w =
      -Real.log (5 / 4 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) -
      2 * (5 * Real.log 2 / 8) *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) *
            centeredEndpointCorrelation w t) +
      2 * yoshidaEndpointA *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (yoshidaEndpointA * t) *
            centeredEndpointCorrelation w t) -
      2 * (5 * Real.log 2 / 8) *
        centeredSinhMoment w ((5 * Real.log 2 / 8) / 2) ^ 2 +
      2 * yoshidaEndpointA *
        centeredSinhMoment w (yoshidaEndpointA / 2) ^ 2 +
      Real.sqrt 2 * Real.log 2 * endpointFoldedCorrelation w (2 / 5) := by
  rw [fourCellWidthPrimePerturbation_eq_rankSquares w hw,
    centeredCoshMoment_eq_zero_of_odd hodd,
    centeredCoshMoment_eq_zero_of_odd hodd,
    fourCellEndpointPairing_eq_centeredEndpointCorrelation,
    show (8 / 5 : ℝ) = 2 - 2 / 5 by norm_num,
    centeredCorrelation_two_sub_eq_neg_endpointFolded_of_odd hodd]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellWidthPerturbationStructural
