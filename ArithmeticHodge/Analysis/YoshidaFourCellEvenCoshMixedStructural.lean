import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLowSchur
import ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshRegularStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenCoshMixedStructural

noncomputable section

open CenteredEndpointCorrelation
open MultiplicativeWeilFourCellRealRescaleStructural
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaRegularKernelBound

/-!
# The fixed mixed row of the even wide-cosh split

The low part of the canonical wide-cosh decomposition is constant.  On the
zero-cosh residual, the positive polar rank has no mixed term.  Consequently
the complete low--tail entry is a scalar multiple of one fixed linear row:
potential minus scalar mass, regular-kernel row, and the retained prime row.

This is an exact identity.  In particular, it reduces the remaining even
Schur determinant to a single Riesz-row estimate rather than a family
depending on the original profile.
-/

/-- The exact complete-bracket row against the constant profile, after the
wide positive-cosh coordinate of the second argument has been killed. -/
def fourCellEvenZeroCoshConstantRow (v : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * v x) -
    (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in -1..1, v x) -
    2 * fourCellOperatorHalfWidth *
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          factorTwoCenteredCorrelationBilinear (fun _ : ℝ ↦ 1) v t) -
    Real.sqrt 2 * Real.log 2 *
      factorTwoCenteredCorrelationBilinear
        (fun _ : ℝ ↦ 1) v (8 / 5)

private theorem centeredRawLogEnergy_const_add
    (v : ℝ → ℝ) (c : ℝ) :
    centeredRawLogEnergy (fun x ↦ c + v x) = centeredRawLogEnergy v := by
  unfold centeredRawLogEnergy
  apply intervalIntegral.integral_congr
  intro x _hx
  apply intervalIntegral.integral_congr
  intro y _hy
  ring

private theorem centeredRawLogEnergy_const (c : ℝ) :
    centeredRawLogEnergy (fun _ : ℝ ↦ c) = 0 := by
  unfold centeredRawLogEnergy
  norm_num

private theorem intervalIntegrable_fourCellKernel_mul_continuous
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t : ℝ ↦
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t)
      volume 0 2 := by
  apply intervalIntegrable_boundedLag_mul_continuous
      (fun t : ℝ ↦
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t)) C
      (measurable_yoshidaRegularKernel.comp
        (measurable_const.mul measurable_id)) hC (1 / 4)
  intro t ht
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
    mul_nonneg ha0 ht.1
  have harg4 : fourCellOperatorHalfWidth * t ≤
      5 * Real.log 2 / 4 := by
    calc
      fourCellOperatorHalfWidth * t ≤
          fourCellOperatorHalfWidth * 2 :=
        mul_le_mul_of_nonneg_left ht.2 ha0
      _ = 5 * Real.log 2 / 4 := by
        unfold fourCellOperatorHalfWidth
        ring
  have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg4
  have hk4 := yoshidaRegularKernel_le_quarter harg0
  rw [abs_of_nonneg hk0]
  exact hk4

private theorem fourCellPositiveCoshMoment_const
    (c lambda : ℝ) :
    fourCellPositiveCoshMoment (fun _ : ℝ ↦ c) lambda =
      c * fourCellPositiveCoshMoment (fun _ : ℝ ↦ 1) lambda := by
  unfold fourCellPositiveCoshMoment
  rw [show (fun x : ℝ ↦ Real.cosh (lambda * x) * c) =
      fun x ↦ c * (Real.cosh (lambda * x) * 1) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]

private theorem fourCellPositiveCoshMoment_const_add
    (v : ℝ → ℝ) (hv : Continuous v) (c lambda : ℝ) :
    fourCellPositiveCoshMoment (fun x ↦ c + v x) lambda =
      c * fourCellPositiveCoshMoment (fun _ : ℝ ↦ 1) lambda +
        fourCellPositiveCoshMoment v lambda := by
  have hconst : IntervalIntegrable
      (fun x : ℝ ↦ c * (Real.cosh (lambda * x) * 1))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hvInt : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (lambda * x) * v x)
      volume 0 1 := by
    exact ((Real.continuous_cosh.comp
      (continuous_const.mul continuous_id)).mul hv).intervalIntegrable _ _
  unfold fourCellPositiveCoshMoment
  rw [show (fun x : ℝ ↦ Real.cosh (lambda * x) * (c + v x)) =
      fun x ↦ c * (Real.cosh (lambda * x) * 1) +
        Real.cosh (lambda * x) * v x by
    funext x
    ring,
    intervalIntegral.integral_add hconst hvInt,
    intervalIntegral.integral_const_mul]

private theorem factorTwoCenteredCorrelationBilinear_const_left
    (v : ℝ → ℝ) (c t : ℝ) :
    factorTwoCenteredCorrelationBilinear (fun _ : ℝ ↦ c) v t =
      c * factorTwoCenteredCorrelationBilinear (fun _ : ℝ ↦ 1) v t := by
  have hc : (fun _ : ℝ ↦ c) = c • (fun _ : ℝ ↦ (1 : ℝ)) := by
    funext x
    simp
  rw [hc]
  simpa only [one_smul, mul_one] using
    factorTwoCenteredCorrelationBilinear_smul_smul
      c 1 (fun _ : ℝ ↦ 1) v t

private theorem fourCellRegularCorrelation_const_add
    (v : ℝ → ℝ) (hv : Continuous v) (c : ℝ) :
    (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation (fun x ↦ c + v x) t) =
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation (fun _ : ℝ ↦ c) t) +
        2 * c * (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear
              (fun _ : ℝ ↦ 1) v t) +
        ∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation v t := by
  have hconstC : Continuous
      (centeredEndpointCorrelation (fun _ : ℝ ↦ c)) :=
    continuous_centeredEndpointCorrelation_of_continuous
      (fun _ : ℝ ↦ c) continuous_const
  have hvC : Continuous (centeredEndpointCorrelation v) :=
    continuous_centeredEndpointCorrelation_of_continuous v hv
  have hB : Continuous
      (factorTwoCenteredCorrelationBilinear (fun _ : ℝ ↦ 1) v) := by
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation
      (fun _ : ℝ ↦ 1) v continuous_const hv).add
        (continuous_factorTwoCenteredCrossCorrelation
          v (fun _ : ℝ ↦ 1) hv continuous_const)).div_const 2
  have hconstInt := intervalIntegrable_fourCellKernel_mul_continuous
    (centeredEndpointCorrelation (fun _ : ℝ ↦ c)) hconstC
  have hBInt := intervalIntegrable_fourCellKernel_mul_continuous
    (factorTwoCenteredCorrelationBilinear (fun _ : ℝ ↦ 1) v) hB
  have hvInt := intervalIntegrable_fourCellKernel_mul_continuous
    (centeredEndpointCorrelation v) hvC
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation (fun x ↦ c + v x) t) =
      fun t ↦
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation (fun _ : ℝ ↦ c) t +
          ((2 * c) *
              (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
                factorTwoCenteredCorrelationBilinear
                  (fun _ : ℝ ↦ 1) v t) +
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation v t) by
    funext t
    change yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation ((fun _ : ℝ ↦ c) + v) t = _
    rw [centeredEndpointCorrelation_add
      (fun _ : ℝ ↦ c) v continuous_const hv t,
      factorTwoCenteredCorrelationBilinear_const_left]
    ring,
    intervalIntegral.integral_add hconstInt
      ((hBInt.const_mul (2 * c)).add hvInt),
    intervalIntegral.integral_add (hBInt.const_mul (2 * c)) hvInt,
    intervalIntegral.integral_const_mul]
  ring

private theorem fourCellBracket_const_add_eq
    (v : ℝ → ℝ) (hv : Continuous v) (heven : Function.Even v)
    (hzero : fourCellPositiveCoshMoment v
      (fourCellOperatorHalfWidth / 2) = 0) (c : ℝ) :
    centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
          (fun x ↦ c + v x) -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing (fun x ↦ c + v x) =
      (centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
          (fun _ : ℝ ↦ c) -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing (fun _ : ℝ ↦ c)) +
      2 * c * fourCellEvenZeroCoshConstantRow v +
      (centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth v -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing v) := by
  have hpotential := integral_endpointPotential_add_sq
    (fun _ : ℝ ↦ c) v continuous_const hv
  have hmass := integral_add_sq (fun _ : ℝ ↦ c) v
    continuous_const hv
  have hpotentialCross :
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * c * v x) =
        c * ∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * v x := by
    rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x * c * v x) =
        fun x ↦ c * (yoshidaEndpointPotential x * v x) by
      funext x
      ring,
      intervalIntegral.integral_const_mul]
  have hmassCross : (∫ x : ℝ in -1..1, c * v x) =
      c * ∫ x : ℝ in -1..1, v x := by
    exact intervalIntegral.integral_const_mul c v
  have hregular := fourCellRegularCorrelation_const_add v hv c
  have hconstEven : Function.Even (fun _ : ℝ ↦ c) := by
    intro x
    rfl
  have haddEven : Function.Even (fun x ↦ c + v x) := by
    intro x
    change c + v (-x) = c + v x
    rw [heven x]
  have hpolarAdd := physicalPolarProduct_eq_positiveCoshSquare_of_even
    (fun x ↦ c + v x) (continuous_const.add hv) haddEven
      fourCellOperatorHalfWidth
  have hpolarConst := physicalPolarProduct_eq_positiveCoshSquare_of_even
    (fun _ : ℝ ↦ c) continuous_const hconstEven
      fourCellOperatorHalfWidth
  have hpolarV := physicalPolarProduct_eq_positiveCoshSquare_of_even
    v hv heven fourCellOperatorHalfWidth
  have hCadd := fourCellPositiveCoshMoment_const_add v hv c
    (fourCellOperatorHalfWidth / 2)
  have hCconst := fourCellPositiveCoshMoment_const c
    (fourCellOperatorHalfWidth / 2)
  have hprimeAdd :
      centeredEndpointCorrelation (fun x ↦ c + v x) (8 / 5) =
        centeredEndpointCorrelation (fun _ : ℝ ↦ c) (8 / 5) +
          2 * factorTwoCenteredCorrelationBilinear
            (fun _ : ℝ ↦ c) v (8 / 5) +
          centeredEndpointCorrelation v (8 / 5) := by
    simpa only [Pi.add_apply] using centeredEndpointCorrelation_add
      (fun _ : ℝ ↦ c) v continuous_const hv (8 / 5)
  have hprimeScale := factorTwoCenteredCorrelationBilinear_const_left
    v c (8 / 5)
  rw [fourCellEndpointPairing_eq_centeredEndpointCorrelation,
    fourCellEndpointPairing_eq_centeredEndpointCorrelation,
    fourCellEndpointPairing_eq_centeredEndpointCorrelation]
  unfold centeredClippedPhysicalQuadratic
  rw [centeredRawLogEnergy_const_add,
    centeredRawLogEnergy_const, hpotential, hpotentialCross,
    hmass, hmassCross, hregular, hpolarAdd, hpolarConst, hpolarV,
    hCadd, hCconst, hzero, hprimeAdd, hprimeScale]
  unfold fourCellEvenZeroCoshConstantRow
  ring

private theorem centeredEndpointCorrelation_const_scale
    (c t : ℝ) :
    centeredEndpointCorrelation (fun _ : ℝ ↦ c) t =
      c ^ 2 * centeredEndpointCorrelation (fun _ : ℝ ↦ 1) t := by
  have hc : (fun _ : ℝ ↦ c) = c • (fun _ : ℝ ↦ (1 : ℝ)) := by
    funext x
    simp
  calc
    centeredEndpointCorrelation (fun _ : ℝ ↦ c) t =
        factorTwoCenteredCorrelationBilinear
          (fun _ : ℝ ↦ c) (fun _ : ℝ ↦ c) t :=
      (factorTwoCenteredCorrelationBilinear_self
        (fun _ : ℝ ↦ c) t).symm
    _ = c * c * factorTwoCenteredCorrelationBilinear
          (fun _ : ℝ ↦ 1) (fun _ : ℝ ↦ 1) t := by
      rw [hc, factorTwoCenteredCorrelationBilinear_smul_smul]
    _ = c ^ 2 * centeredEndpointCorrelation (fun _ : ℝ ↦ 1) t := by
      rw [factorTwoCenteredCorrelationBilinear_self]
      ring

/-- The complete four-cell diagonal is exactly homogeneous on the constant
line.  This keeps the canonical cosh pivot normalized without changing its
Schur determinant. -/
private theorem fourCell_evenBracket_const_eq_one_mul_sq (c : ℝ) :
    centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
          (fun _ : ℝ ↦ c) -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing (fun _ : ℝ ↦ c) =
      c ^ 2 *
        (centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
              (fun _ : ℝ ↦ 1) -
          Real.sqrt 2 * Real.log 2 *
            fourCellEndpointPairing (fun _ : ℝ ↦ 1)) := by
  have hpotential :
      (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * (fun _ : ℝ ↦ c) x ^ 2) =
        c ^ 2 * ∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * (fun _ : ℝ ↦ 1) x ^ 2 := by
    rw [show (fun x : ℝ ↦
        yoshidaEndpointPotential x * (fun _ : ℝ ↦ c) x ^ 2) =
      fun x ↦ c ^ 2 *
        (yoshidaEndpointPotential x * (fun _ : ℝ ↦ 1) x ^ 2) by
      funext x
      ring,
      intervalIntegral.integral_const_mul]
  have hmass :
      (∫ x : ℝ in -1..1, (fun _ : ℝ ↦ c) x ^ 2) =
        c ^ 2 * ∫ x : ℝ in -1..1, (fun _ : ℝ ↦ 1) x ^ 2 := by
    rw [show (fun x : ℝ ↦ (fun _ : ℝ ↦ c) x ^ 2) =
      fun x ↦ c ^ 2 * (fun _ : ℝ ↦ 1) x ^ 2 by
      funext x
      ring,
      intervalIntegral.integral_const_mul]
  have hregular :
      (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation (fun _ : ℝ ↦ c) t) =
        c ^ 2 * ∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation (fun _ : ℝ ↦ 1) t := by
    rw [show (fun t : ℝ ↦
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation (fun _ : ℝ ↦ c) t) =
      fun t ↦ c ^ 2 *
        (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation (fun _ : ℝ ↦ 1) t) by
      funext t
      rw [centeredEndpointCorrelation_const_scale]
      ring,
      intervalIntegral.integral_const_mul]
  have hminus :
      (∫ x : ℝ in -1..1,
          Real.exp (-fourCellOperatorHalfWidth * x / 2) *
            (fun _ : ℝ ↦ c) x) =
        c * ∫ x : ℝ in -1..1,
          Real.exp (-fourCellOperatorHalfWidth * x / 2) *
            (fun _ : ℝ ↦ 1) x := by
    rw [show (fun x : ℝ ↦
        Real.exp (-fourCellOperatorHalfWidth * x / 2) *
          (fun _ : ℝ ↦ c) x) =
      fun x ↦ c *
        (Real.exp (-fourCellOperatorHalfWidth * x / 2) *
          (fun _ : ℝ ↦ 1) x) by
      funext x
      ring,
      intervalIntegral.integral_const_mul]
  have hplus :
      (∫ x : ℝ in -1..1,
          Real.exp (fourCellOperatorHalfWidth * x / 2) *
            (fun _ : ℝ ↦ c) x) =
        c * ∫ x : ℝ in -1..1,
          Real.exp (fourCellOperatorHalfWidth * x / 2) *
            (fun _ : ℝ ↦ 1) x := by
    rw [show (fun x : ℝ ↦
        Real.exp (fourCellOperatorHalfWidth * x / 2) *
          (fun _ : ℝ ↦ c) x) =
      fun x ↦ c *
        (Real.exp (fourCellOperatorHalfWidth * x / 2) *
          (fun _ : ℝ ↦ 1) x) by
      funext x
      ring,
      intervalIntegral.integral_const_mul]
  have hpair : fourCellEndpointPairing (fun _ : ℝ ↦ c) =
      c ^ 2 * fourCellEndpointPairing (fun _ : ℝ ↦ 1) := by
    unfold fourCellEndpointPairing
    rw [show (fun x : ℝ ↦
        (fun _ : ℝ ↦ c) x * (fun _ : ℝ ↦ c) (x - 8 / 5)) =
      fun x ↦ c ^ 2 *
        ((fun _ : ℝ ↦ 1) x * (fun _ : ℝ ↦ 1) (x - 8 / 5)) by
      funext x
      ring,
      intervalIntegral.integral_const_mul]
  unfold centeredClippedPhysicalQuadratic
  rw [centeredRawLogEnergy_const c, centeredRawLogEnergy_const 1,
    hpotential, hmass, hregular, hminus, hplus, hpair]
  ring

/-- Exact homogeneity of the complete constant/zero-cosh mixed entry. -/
theorem fourCellExactBracketPolarization_const_zeroCosh
    (v : ℝ → ℝ) (hv : Continuous v) (heven : Function.Even v)
    (hzero : fourCellPositiveCoshMoment v
      (fourCellOperatorHalfWidth / 2) = 0) (c : ℝ) :
    fourCellExactBracketPolarization (fun _ : ℝ ↦ c) v =
      c * fourCellEvenZeroCoshConstantRow v := by
  have hadd := fourCell_evenBracket_add_eq_low_add_mixed_add_tail
    (fun _ : ℝ ↦ c) v continuous_const hv
  have hdirect := fourCellBracket_const_add_eq v hv heven hzero c
  change centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
          ((fun _ : ℝ ↦ c) + v) -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing ((fun _ : ℝ ↦ c) + v) = _ at hadd
  have hfun : ((fun _ : ℝ ↦ c) + v) = fun x ↦ c + v x := by
    rfl
  rw [hfun] at hadd
  linarith

/-- The canonical low--tail determinant is now one fixed row inequality.
The original profile occurs only through its scalar wide-cosh coordinate. -/
theorem canonicalCoshSchur_of_constantRow
    (w : ℝ → ℝ) (hw : Continuous w) (hweven : Function.Even w)
    (hrow : fourCellEvenZeroCoshConstantRow
          (fourCellEvenCoshResidual w fourCellEvenCoshUnit) ^ 2 ≤
      (centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
            (fun _ : ℝ ↦ 1) -
          Real.sqrt 2 * Real.log 2 *
            fourCellEndpointPairing (fun _ : ℝ ↦ 1)) *
        fourCellEvenPolarFreeOperator
          (fourCellEvenCoshResidual w fourCellEvenCoshUnit)) :
    fourCellExactBracketPolarization
          (fourCellEvenCoshLow w fourCellEvenCoshUnit)
          (fourCellEvenCoshResidual w fourCellEvenCoshUnit) ^ 2 ≤
      (centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
            (fourCellEvenCoshLow w fourCellEvenCoshUnit) -
          Real.sqrt 2 * Real.log 2 *
            fourCellEndpointPairing
              (fourCellEvenCoshLow w fourCellEvenCoshUnit)) *
        fourCellEvenPolarFreeOperator
          (fourCellEvenCoshResidual w fourCellEvenCoshUnit) := by
  let v : ℝ → ℝ := fourCellEvenCoshResidual w fourCellEvenCoshUnit
  let c : ℝ := fourCellPositiveCoshMoment w
    (fourCellOperatorHalfWidth / 2) * (fourCellEvenCoshMass)⁻¹
  have hv : Continuous v :=
    fourCellEvenCoshResidual_continuous w fourCellEvenCoshUnit
      hw fourCellEvenCoshUnit_continuous
  have hveven : Function.Even v :=
    fourCellEvenCoshResidual_even w fourCellEvenCoshUnit
      hweven fourCellEvenCoshUnit_even
  have hvzero : fourCellPositiveCoshMoment v
      (fourCellOperatorHalfWidth / 2) = 0 :=
    fourCellPositiveCoshMoment_residual_eq_zero
      w fourCellEvenCoshUnit hw fourCellEvenCoshUnit_continuous
        fourCellPositiveCoshMoment_unit
  have hlow : fourCellEvenCoshLow w fourCellEvenCoshUnit =
      fun _ : ℝ ↦ c := by
    funext x
    unfold fourCellEvenCoshLow fourCellEvenCoshUnit
    rfl
  have hmix := fourCellExactBracketPolarization_const_zeroCosh
    v hv hveven hvzero c
  have hdiag := fourCell_evenBracket_const_eq_one_mul_sq c
  rw [hlow, hmix, hdiag]
  dsimp only [v] at hrow ⊢
  nlinarith [sq_nonneg c]

/-- The sharpened homogeneous constant pivot replaces the transcendental
constant diagonal by the rational reserve `13 / 80`.  Consequently one
fixed row inequality already contains both zero-cosh tail nonnegativity and
the canonical low--tail determinant. -/
theorem fourCell_evenBracket_nonnegative_of_rationalConstantRow
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hweven : Function.Even w)
    (hrow : fourCellEvenZeroCoshConstantRow
          (fourCellEvenCoshResidual w fourCellEvenCoshUnit) ^ 2 ≤
      (13 / 80 : ℝ) *
        fourCellEvenPolarFreeOperator
          (fourCellEvenCoshResidual w fourCellEvenCoshUnit)) :
    0 ≤ centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  let v : ℝ → ℝ := fourCellEvenCoshResidual w fourCellEvenCoshUnit
  have hrow' : fourCellEvenZeroCoshConstantRow v ^ 2 ≤
      (13 / 80 : ℝ) * fourCellEvenPolarFreeOperator v := by
    simpa only [v] using hrow
  have htail : 0 ≤ fourCellEvenPolarFreeOperator v := by
    have hsquare : 0 ≤ fourCellEvenZeroCoshConstantRow v ^ 2 := sq_nonneg _
    have hscaled : 0 ≤
        (13 / 80 : ℝ) * fourCellEvenPolarFreeOperator v := by
      exact hsquare.trans hrow'
    nlinarith
  have hpivot : (13 / 80 : ℝ) ≤
      centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
          (fun _ : ℝ ↦ 1) -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing (fun _ : ℝ ↦ 1) :=
    thirteen_div_eighty_lt_fourCell_evenBracket_one.le
  have hscaled := mul_le_mul_of_nonneg_right hpivot htail
  have hrowExact : fourCellEvenZeroCoshConstantRow v ^ 2 ≤
      (centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth
            (fun _ : ℝ ↦ 1) -
          Real.sqrt 2 * Real.log 2 *
            fourCellEndpointPairing (fun _ : ℝ ↦ 1)) *
        fourCellEvenPolarFreeOperator v := by
    exact hrow'.trans hscaled
  have hdet := canonicalCoshSchur_of_constantRow
    w hw.continuous hweven (by simpa only [v] using hrowExact)
  exact fourCell_evenBracket_nonnegative_of_canonicalCoshSchur
    w hw hweven (by simpa only [v] using htail) hdet

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenCoshMixedStructural
