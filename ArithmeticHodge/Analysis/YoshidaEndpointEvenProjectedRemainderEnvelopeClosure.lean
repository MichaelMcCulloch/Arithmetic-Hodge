import ArithmeticHodge.Analysis.YoshidaEndpointEvenP2LogEnergy
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedBaseIntegrable
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedMatrixClosure
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeTrueGram
import ArithmeticHodge.Analysis.YoshidaEndpointScalarStructuralUpper

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeClosure

open YoshidaEndpointEvenP2LogEnergy
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenProjectedBaseIntegrable
open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenProjectedDualIntegral
open YoshidaEndpointEvenProjectedGapMoments
open YoshidaEndpointEvenProjectedMatrixClosure
open YoshidaEndpointEvenProjectedRemainderEnvelopeCoefficients
open YoshidaEndpointEvenProjectedRemainderEnvelopeGram
open YoshidaEndpointEvenProjectedRemainderEnvelopeTrueGram
open YoshidaEndpointEvenProjectedRemainderIntegrable
open YoshidaEndpointEvenProjectedRemainderMoments
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScalarStructuralUpper
open YoshidaEndpointPotentialBound
open UnitIntervalLogEnergyAffine

noncomputable section

private theorem intervalIntegrable_fixedProjectedShiftedRemainder_local
    (c b : ℝ) :
    IntervalIntegrable (fixedProjectedShiftedRemainder c b) volume (-1) 1 := by
  have hR0 : IntervalIntegrable
      (yoshidaEndpointEvenRegularRepresenter centeredEvenP0) volume (-1) 1 := by
    simpa using intervalIntegrable_regularRepresenter_mul centeredEvenP0
      (fun _ : ℝ ↦ 1) (by unfold centeredEvenP0; fun_prop) continuous_const
  have hR2 : IntervalIntegrable
      (yoshidaEndpointEvenRegularRepresenter centeredEvenP2) volume (-1) 1 := by
    simpa using intervalIntegrable_regularRepresenter_mul centeredEvenP2
      (fun _ : ℝ ↦ 1) (by unfold centeredEvenP2; fun_prop) continuous_const
  have hregular : IntervalIntegrable
      (fun x ↦ (-yoshidaEndpointA) *
        (c * yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x +
          b * yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x))
      volume (-1) 1 :=
    ((hR0.const_mul c).add (hR2.const_mul b)).const_mul (-yoshidaEndpointA)
  have hcontinuous : Continuous (fun x : ℝ ↦
      2 * yoshidaEndpointA *
          (c * yoshidaEndpointCoshMoment centeredEvenP0 +
            b * yoshidaEndpointCoshMoment centeredEvenP2) *
          Real.cosh (yoshidaEndpointA * x / 2) -
        fixedProjectionPolynomial c b x -
        (41 / 60 : ℝ) * fixedEvenLowProfile c b x) := by
    unfold fixedProjectionPolynomial fixedEvenLowProfile centeredEvenP0 centeredEvenP2
    fun_prop
  apply (hregular.add (hcontinuous.intervalIntegrable (-1) 1)).congr
  intro x _hx
  unfold fixedProjectedShiftedRemainder fixedProjectedBoundedRemainder
  ring

private theorem exactLowGram00_expansion :
    yoshidaEndpointEvenLowGram00 =
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x) -
        2 * yoshidaEndpointScalarMassLoss -
        yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x) +
        2 * yoshidaEndpointA *
          yoshidaEndpointCoshMoment centeredEvenP0 ^ 2 := by
  have hreg := yoshidaEndpointRegularRealBilinear_eq_integral_representer
    centeredEvenP0 centeredEvenP0 (by unfold centeredEvenP0; fun_prop)
      (by unfold centeredEvenP0; fun_prop)
  have hsinh := yoshidaEndpointSinhMoment_eq_zero_of_even centeredEvenP0
    (by intro x; rfl)
  unfold yoshidaEndpointEvenLowGram00 yoshidaEndpointEvenCleanBilinear
  rw [centeredRawLogBilinear_centeredEvenP0_eq_zero centeredEvenP0,
    hreg, hsinh]
  unfold centeredEvenP0
  norm_num
  ring

private theorem exactLowGram02_expansion :
    yoshidaEndpointEvenLowGram02 =
      (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * centeredEvenP2 x) -
        yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x *
              centeredEvenP2 x) +
        2 * yoshidaEndpointA *
          yoshidaEndpointCoshMoment centeredEvenP0 *
            yoshidaEndpointCoshMoment centeredEvenP2 := by
  have hreg := yoshidaEndpointRegularRealBilinear_eq_integral_representer
    centeredEvenP0 centeredEvenP2 (by unfold centeredEvenP0; fun_prop)
      (by unfold centeredEvenP2; fun_prop)
  have hsinh0 := yoshidaEndpointSinhMoment_eq_zero_of_even centeredEvenP0
    (by intro x; rfl)
  have hsinh2 := yoshidaEndpointSinhMoment_eq_zero_of_even centeredEvenP2
    (by intro x; unfold centeredEvenP2; ring)
  unfold yoshidaEndpointEvenLowGram02 yoshidaEndpointEvenCleanBilinear
  rw [centeredRawLogBilinear_centeredEvenP0_eq_zero centeredEvenP2,
    hreg, hsinh0, hsinh2, integral_centeredEvenP0_mul_p2]
  unfold centeredEvenP0
  norm_num
  ring

private theorem exactLowGram22_expansion :
    yoshidaEndpointEvenLowGram22 =
      (3 / 5 : ℝ) +
        (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * centeredEvenP2 x ^ 2) -
        (2 / 5 : ℝ) * yoshidaEndpointScalarMassLoss -
        yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x *
              centeredEvenP2 x) +
        2 * yoshidaEndpointA *
          yoshidaEndpointCoshMoment centeredEvenP2 ^ 2 := by
  have hreg := yoshidaEndpointRegularRealBilinear_eq_integral_representer
    centeredEvenP2 centeredEvenP2 (by unfold centeredEvenP2; fun_prop)
      (by unfold centeredEvenP2; fun_prop)
  have hsinh := yoshidaEndpointSinhMoment_eq_zero_of_even centeredEvenP2
    (by intro x; unfold centeredEvenP2; ring)
  have hraw : centeredRawLogBilinear centeredEvenP2 centeredEvenP2 =
      centeredRawLogEnergy centeredEvenP2 := by
    unfold centeredRawLogBilinear centeredRawLogEnergy
    apply intervalIntegral.integral_congr
    intro x _hx
    apply intervalIntegral.integral_congr
    intro y _hy
    ring
  unfold yoshidaEndpointEvenLowGram22 yoshidaEndpointEvenCleanBilinear
  rw [hraw, centeredRawLogEnergy_centeredEvenP2, hreg, hsinh]
  rw [show (fun x : ℝ ↦ centeredEvenP2 x * centeredEvenP2 x) =
      fun x ↦ centeredEvenP2 x ^ 2 by
    funext x
    ring,
    integral_centeredEvenP2_sq]
  norm_num
  ring

private theorem intervalIntegrable_shifted0 :
    IntervalIntegrable fixedProjectedShiftedRemainder0 volume (-1) 1 := by
  unfold fixedProjectedShiftedRemainder0
  exact intervalIntegrable_fixedProjectedShiftedRemainder_local 1 0

private theorem intervalIntegrable_shifted2 :
    IntervalIntegrable fixedProjectedShiftedRemainder2 volume (-1) 1 := by
  unfold fixedProjectedShiftedRemainder2
  exact intervalIntegrable_fixedProjectedShiftedRemainder_local 0 1

private theorem fixedProjectedDualBaseGram00_expansion :
    fixedProjectedDualBaseGram00 =
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x) +
        2 * (∫ x : ℝ in -1..1, fixedProjectedShiftedRemainder0 x) +
        41 / 30 := by
  have hV : IntervalIntegrable yoshidaEndpointPotential volume (-1) 1 := by
    simpa only [centeredEvenP0, mul_one] using
      intervalIntegrable_endpointPotential_mul centeredEvenP0 centeredEvenP0
        (by unfold centeredEvenP0; fun_prop) (by unfold centeredEvenP0; fun_prop)
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ (41 / 60 : ℝ))
      volume (-1) 1 := continuous_const.intervalIntegrable (-1) 1
  unfold fixedProjectedDualBaseGram00
  rw [show (fun x : ℝ ↦ fixedProjectedDualBaseIntegrand 1 0 x) =
      fun x ↦ (yoshidaEndpointPotential x +
        2 * fixedProjectedShiftedRemainder0 x) + 41 / 60 by
    funext x
    unfold fixedProjectedDualBaseIntegrand fixedProjectedShiftedRemainder0
      fixedProjectedShiftedRemainder fixedEvenLowProfile
    unfold centeredEvenP0
    ring]
  rw [intervalIntegral.integral_add
      (hV.add (intervalIntegrable_shifted0.const_mul 2)) hconst,
    intervalIntegral.integral_add hV
      (intervalIntegrable_shifted0.const_mul 2),
    intervalIntegral.integral_const_mul]
  norm_num

private theorem fixedProjectedDualBaseGram02_expansion :
    fixedProjectedDualBaseGram02 =
      (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * centeredEvenP2 x) +
        (∫ x : ℝ in -1..1, fixedProjectedShiftedRemainder2 x) +
        ∫ x : ℝ in -1..1,
          centeredEvenP2 x * fixedProjectedShiftedRemainder0 x := by
  have hV : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * centeredEvenP2 x)
      volume (-1) 1 := by
    simpa only [centeredEvenP0, mul_one] using
      intervalIntegrable_endpointPotential_mul centeredEvenP0 centeredEvenP2
        (by unfold centeredEvenP0; fun_prop) (by unfold centeredEvenP2; fun_prop)
  have hP2D0 : IntervalIntegrable
      (fun x : ℝ ↦ centeredEvenP2 x * fixedProjectedShiftedRemainder0 x)
      volume (-1) 1 := by
    apply (intervalIntegrable_shifted0.mul_continuousOn
      (by unfold centeredEvenP2; fun_prop : Continuous centeredEvenP2).continuousOn).congr
    intro x _hx
    ring
  have hP2 : IntervalIntegrable centeredEvenP2 volume (-1) 1 :=
    (by unfold centeredEvenP2; fun_prop : Continuous centeredEvenP2)
      |>.intervalIntegrable (-1) 1
  unfold fixedProjectedDualBaseGram02
  rw [show (fun x : ℝ ↦ fixedProjectedDualBaseCrossIntegrand x) =
      fun x ↦ ((yoshidaEndpointPotential x * centeredEvenP2 x +
        fixedProjectedShiftedRemainder2 x) +
        centeredEvenP2 x * fixedProjectedShiftedRemainder0 x) +
        (41 / 60 : ℝ) * centeredEvenP2 x by
    funext x
    unfold fixedProjectedDualBaseCrossIntegrand fixedProjectedDualBaseIntegrand
      fixedProjectedShiftedRemainder0 fixedProjectedShiftedRemainder2
      fixedProjectedShiftedRemainder fixedProjectedBoundedRemainder
      fixedProjectionPolynomial fixedEvenLowProfile centeredEvenP0
    ring]
  rw [intervalIntegral.integral_add
      ((hV.add intervalIntegrable_shifted2).add hP2D0)
      (hP2.const_mul (41 / 60 : ℝ)),
    intervalIntegral.integral_add (hV.add intervalIntegrable_shifted2) hP2D0,
    intervalIntegral.integral_add hV intervalIntegrable_shifted2,
    intervalIntegral.integral_const_mul]
  have hP2zero : (∫ x : ℝ in -1..1, centeredEvenP2 x) = 0 := by
    simpa only [centeredEvenP0, one_mul] using integral_centeredEvenP0_mul_p2
  rw [hP2zero]
  ring

private theorem fixedProjectedDualBaseGram22_expansion :
    fixedProjectedDualBaseGram22 =
      (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * centeredEvenP2 x ^ 2) +
        2 * (∫ x : ℝ in -1..1,
          centeredEvenP2 x * fixedProjectedShiftedRemainder2 x) +
        41 / 150 := by
  have hV : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * centeredEvenP2 x ^ 2)
      volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul centeredEvenP2 centeredEvenP2
      (by unfold centeredEvenP2; fun_prop) (by unfold centeredEvenP2; fun_prop)).congr
    intro x _hx
    ring
  have hP2D2 : IntervalIntegrable
      (fun x : ℝ ↦ centeredEvenP2 x * fixedProjectedShiftedRemainder2 x)
      volume (-1) 1 := by
    apply (intervalIntegrable_shifted2.mul_continuousOn
      (by unfold centeredEvenP2; fun_prop : Continuous centeredEvenP2).continuousOn).congr
    intro x _hx
    ring
  have hP2sq : IntervalIntegrable (fun x : ℝ ↦ centeredEvenP2 x ^ 2)
      volume (-1) 1 :=
    (by unfold centeredEvenP2; fun_prop : Continuous fun x : ℝ ↦ centeredEvenP2 x ^ 2)
      |>.intervalIntegrable (-1) 1
  unfold fixedProjectedDualBaseGram22
  rw [show (fun x : ℝ ↦ fixedProjectedDualBaseIntegrand 0 1 x) =
      fun x ↦ (yoshidaEndpointPotential x * centeredEvenP2 x ^ 2 +
        2 * (centeredEvenP2 x * fixedProjectedShiftedRemainder2 x)) +
        (41 / 60 : ℝ) * centeredEvenP2 x ^ 2 by
    funext x
    unfold fixedProjectedDualBaseIntegrand fixedProjectedShiftedRemainder2
      fixedProjectedShiftedRemainder fixedEvenLowProfile centeredEvenP0
    ring]
  rw [intervalIntegral.integral_add (hV.add (hP2D2.const_mul 2))
      (hP2sq.const_mul (41 / 60 : ℝ)),
    intervalIntegral.integral_add hV (hP2D2.const_mul 2),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_centeredEvenP2_sq]
  norm_num

private theorem integral_fixedProjectionPolynomial_10 :
    (∫ x : ℝ in -1..1, fixedProjectionPolynomial 1 0 x) = 73 / 24 := by
  have h0 : IntervalIntegrable centeredEvenP0 volume (-1) 1 :=
    (by unfold centeredEvenP0; fun_prop : Continuous centeredEvenP0)
      |>.intervalIntegrable (-1) 1
  have h2 : IntervalIntegrable centeredEvenP2 volume (-1) 1 :=
    (by unfold centeredEvenP2; fun_prop : Continuous centeredEvenP2)
      |>.intervalIntegrable (-1) 1
  rw [show (fun x : ℝ ↦ fixedProjectionPolynomial 1 0 x) =
      fun x ↦ (73 / 48 : ℝ) * centeredEvenP0 x +
        (35 / 48 : ℝ) * centeredEvenP2 x by
    funext x
    unfold fixedProjectionPolynomial
    ring,
    intervalIntegral.integral_add (h0.const_mul (73 / 48 : ℝ))
      (h2.const_mul (35 / 48 : ℝ)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hp0 : (∫ x : ℝ in -1..1, centeredEvenP0 x) = 2 := by
    simpa only [centeredEvenP0, one_pow] using integral_centeredEvenP0_sq
  have hp2 : (∫ x : ℝ in -1..1, centeredEvenP2 x) = 0 := by
    simpa only [centeredEvenP0, one_mul] using integral_centeredEvenP0_mul_p2
  rw [hp0, hp2]
  norm_num

private theorem integral_fixedProjectionPolynomial_01 :
    (∫ x : ℝ in -1..1, fixedProjectionPolynomial 0 1 x) = 7 / 24 := by
  have h0 : IntervalIntegrable centeredEvenP0 volume (-1) 1 :=
    (by unfold centeredEvenP0; fun_prop : Continuous centeredEvenP0)
      |>.intervalIntegrable (-1) 1
  have h2 : IntervalIntegrable centeredEvenP2 volume (-1) 1 :=
    (by unfold centeredEvenP2; fun_prop : Continuous centeredEvenP2)
      |>.intervalIntegrable (-1) 1
  rw [show (fun x : ℝ ↦ fixedProjectionPolynomial 0 1 x) =
      fun x ↦ (7 / 48 : ℝ) * centeredEvenP0 x +
        (1 / 2 : ℝ) * centeredEvenP2 x by
    funext x
    unfold fixedProjectionPolynomial
    ring,
    intervalIntegral.integral_add (h0.const_mul (7 / 48 : ℝ))
      (h2.const_mul (1 / 2 : ℝ)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hp0 : (∫ x : ℝ in -1..1, centeredEvenP0 x) = 2 := by
    simpa only [centeredEvenP0, one_pow] using integral_centeredEvenP0_sq
  have hp2 : (∫ x : ℝ in -1..1, centeredEvenP2 x) = 0 := by
    simpa only [centeredEvenP0, one_mul] using integral_centeredEvenP0_mul_p2
  rw [hp0, hp2]
  norm_num

private theorem integral_p2_mul_fixedProjectionPolynomial_10 :
    (∫ x : ℝ in -1..1,
      centeredEvenP2 x * fixedProjectionPolynomial 1 0 x) = 7 / 24 := by
  have h02 : IntervalIntegrable
      (fun x : ℝ ↦ centeredEvenP0 x * centeredEvenP2 x) volume (-1) 1 :=
    (by unfold centeredEvenP0 centeredEvenP2; fun_prop : Continuous
      (fun x : ℝ ↦ centeredEvenP0 x * centeredEvenP2 x))
      |>.intervalIntegrable (-1) 1
  have h22 : IntervalIntegrable (fun x : ℝ ↦ centeredEvenP2 x ^ 2)
      volume (-1) 1 :=
    (by unfold centeredEvenP2; fun_prop : Continuous
      (fun x : ℝ ↦ centeredEvenP2 x ^ 2)) |>.intervalIntegrable (-1) 1
  rw [show (fun x : ℝ ↦ centeredEvenP2 x * fixedProjectionPolynomial 1 0 x) =
      fun x ↦ (73 / 48 : ℝ) *
          (centeredEvenP0 x * centeredEvenP2 x) +
        (35 / 48 : ℝ) * centeredEvenP2 x ^ 2 by
    funext x
    unfold fixedProjectionPolynomial
    ring,
    intervalIntegral.integral_add (h02.const_mul (73 / 48 : ℝ))
      (h22.const_mul (35 / 48 : ℝ)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_centeredEvenP0_mul_p2, integral_centeredEvenP2_sq]
  norm_num

private theorem integral_p2_mul_fixedProjectionPolynomial_01 :
    (∫ x : ℝ in -1..1,
      centeredEvenP2 x * fixedProjectionPolynomial 0 1 x) = 1 / 5 := by
  have h02 : IntervalIntegrable
      (fun x : ℝ ↦ centeredEvenP0 x * centeredEvenP2 x) volume (-1) 1 :=
    (by unfold centeredEvenP0 centeredEvenP2; fun_prop : Continuous
      (fun x : ℝ ↦ centeredEvenP0 x * centeredEvenP2 x))
      |>.intervalIntegrable (-1) 1
  have h22 : IntervalIntegrable (fun x : ℝ ↦ centeredEvenP2 x ^ 2)
      volume (-1) 1 :=
    (by unfold centeredEvenP2; fun_prop : Continuous
      (fun x : ℝ ↦ centeredEvenP2 x ^ 2)) |>.intervalIntegrable (-1) 1
  rw [show (fun x : ℝ ↦ centeredEvenP2 x * fixedProjectionPolynomial 0 1 x) =
      fun x ↦ (7 / 48 : ℝ) *
          (centeredEvenP0 x * centeredEvenP2 x) +
        (1 / 2 : ℝ) * centeredEvenP2 x ^ 2 by
    funext x
    unfold fixedProjectionPolynomial
    ring,
    intervalIntegral.integral_add (h02.const_mul (7 / 48 : ℝ))
      (h22.const_mul (1 / 2 : ℝ)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_centeredEvenP0_mul_p2, integral_centeredEvenP2_sq]
  norm_num

private theorem integral_shifted0_expansion :
    (∫ x : ℝ in -1..1, fixedProjectedShiftedRemainder0 x) =
      -yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x) +
        2 * yoshidaEndpointA *
          yoshidaEndpointCoshMoment centeredEvenP0 ^ 2 -
        73 / 24 - 41 / 30 := by
  have hR0 : IntervalIntegrable
      (yoshidaEndpointEvenRegularRepresenter centeredEvenP0) volume (-1) 1 := by
    simpa using intervalIntegrable_regularRepresenter_mul centeredEvenP0
      (fun _ : ℝ ↦ 1) (by unfold centeredEvenP0; fun_prop) continuous_const
  have hCosh : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2)) volume (-1) 1 :=
    (by fun_prop : Continuous fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2))
      |>.intervalIntegrable (-1) 1
  have hProj : IntervalIntegrable (fixedProjectionPolynomial 1 0)
      volume (-1) 1 :=
    (by unfold fixedProjectionPolynomial centeredEvenP0 centeredEvenP2; fun_prop :
      Continuous (fixedProjectionPolynomial 1 0)) |>.intervalIntegrable (-1) 1
  have hP0 : IntervalIntegrable centeredEvenP0 volume (-1) 1 :=
    (by unfold centeredEvenP0; fun_prop : Continuous centeredEvenP0)
      |>.intervalIntegrable (-1) 1
  rw [show (fun x : ℝ ↦ fixedProjectedShiftedRemainder0 x) =
      fun x ↦ (((-yoshidaEndpointA) *
          yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x +
        (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP0) *
          Real.cosh (yoshidaEndpointA * x / 2)) -
        fixedProjectionPolynomial 1 0 x) -
        (41 / 60 : ℝ) * centeredEvenP0 x by
    funext x
    unfold fixedProjectedShiftedRemainder0 fixedProjectedShiftedRemainder
      fixedProjectedBoundedRemainder fixedEvenLowProfile
    ring]
  rw [intervalIntegral.integral_sub
      (((hR0.const_mul (-yoshidaEndpointA)).add
        (hCosh.const_mul
          (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP0))).sub
        hProj) (hP0.const_mul (41 / 60 : ℝ)),
    intervalIntegral.integral_sub
      ((hR0.const_mul (-yoshidaEndpointA)).add
        (hCosh.const_mul
          (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP0)))
      hProj,
    intervalIntegral.integral_add (hR0.const_mul (-yoshidaEndpointA))
      (hCosh.const_mul
        (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP0)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_fixedProjectionPolynomial_10]
  have hC0 : (∫ x : ℝ in -1..1,
      Real.cosh (yoshidaEndpointA * x / 2)) =
      yoshidaEndpointCoshMoment centeredEvenP0 := by
    unfold yoshidaEndpointCoshMoment centeredEvenP0
    simp only [mul_one]
  have hP0int : (∫ x : ℝ in -1..1, centeredEvenP0 x) = 2 := by
    simpa only [centeredEvenP0, one_pow] using integral_centeredEvenP0_sq
  rw [hC0, hP0int]
  ring

private theorem regularRepresenter_cross_integrals_eq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x) =
      ∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x *
          centeredEvenP2 x := by
  have h02 := yoshidaEndpointRegularRealBilinear_eq_integral_representer
    centeredEvenP0 centeredEvenP2 (by unfold centeredEvenP0; fun_prop)
      (by unfold centeredEvenP2; fun_prop)
  have h20 := yoshidaEndpointRegularRealBilinear_eq_integral_representer
    centeredEvenP2 centeredEvenP0 (by unfold centeredEvenP2; fun_prop)
      (by unfold centeredEvenP0; fun_prop)
  have h20' :
      (yoshidaEndpointRegularRealBilinear centeredEvenP0 centeredEvenP2 +
        yoshidaEndpointRegularRealBilinear centeredEvenP2 centeredEvenP0).re =
          2 * (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x) := by
    rw [add_comm]
    simpa only [centeredEvenP0, mul_one] using h20
  linarith [h02, h20']

private theorem integral_shifted2_expansion :
    (∫ x : ℝ in -1..1, fixedProjectedShiftedRemainder2 x) =
      -yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x *
              centeredEvenP2 x) +
        2 * yoshidaEndpointA *
          yoshidaEndpointCoshMoment centeredEvenP0 *
            yoshidaEndpointCoshMoment centeredEvenP2 -
        7 / 24 := by
  have hR2 : IntervalIntegrable
      (yoshidaEndpointEvenRegularRepresenter centeredEvenP2) volume (-1) 1 := by
    simpa using intervalIntegrable_regularRepresenter_mul centeredEvenP2
      (fun _ : ℝ ↦ 1) (by unfold centeredEvenP2; fun_prop) continuous_const
  have hCosh : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2)) volume (-1) 1 :=
    (by fun_prop : Continuous fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2))
      |>.intervalIntegrable (-1) 1
  have hProj : IntervalIntegrable (fixedProjectionPolynomial 0 1)
      volume (-1) 1 :=
    (by unfold fixedProjectionPolynomial centeredEvenP0 centeredEvenP2; fun_prop :
      Continuous (fixedProjectionPolynomial 0 1)) |>.intervalIntegrable (-1) 1
  have hP2 : IntervalIntegrable centeredEvenP2 volume (-1) 1 :=
    (by unfold centeredEvenP2; fun_prop : Continuous centeredEvenP2)
      |>.intervalIntegrable (-1) 1
  rw [show (fun x : ℝ ↦ fixedProjectedShiftedRemainder2 x) =
      fun x ↦ (((-yoshidaEndpointA) *
          yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x +
        (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP2) *
          Real.cosh (yoshidaEndpointA * x / 2)) -
        fixedProjectionPolynomial 0 1 x) -
        (41 / 60 : ℝ) * centeredEvenP2 x by
    funext x
    unfold fixedProjectedShiftedRemainder2 fixedProjectedShiftedRemainder
      fixedProjectedBoundedRemainder fixedEvenLowProfile
    ring]
  rw [intervalIntegral.integral_sub
      (((hR2.const_mul (-yoshidaEndpointA)).add
        (hCosh.const_mul
          (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP2))).sub
        hProj) (hP2.const_mul (41 / 60 : ℝ)),
    intervalIntegral.integral_sub
      ((hR2.const_mul (-yoshidaEndpointA)).add
        (hCosh.const_mul
          (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP2)))
      hProj,
    intervalIntegral.integral_add (hR2.const_mul (-yoshidaEndpointA))
      (hCosh.const_mul
        (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP2)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_fixedProjectionPolynomial_01,
    regularRepresenter_cross_integrals_eq]
  have hC0 : (∫ x : ℝ in -1..1,
      Real.cosh (yoshidaEndpointA * x / 2)) =
      yoshidaEndpointCoshMoment centeredEvenP0 := by
    unfold yoshidaEndpointCoshMoment centeredEvenP0
    simp only [mul_one]
  have hP2zero : (∫ x : ℝ in -1..1, centeredEvenP2 x) = 0 := by
    simpa only [centeredEvenP0, one_mul] using integral_centeredEvenP0_mul_p2
  rw [hC0, hP2zero]
  ring

private theorem integral_p2_mul_shifted0_expansion :
    (∫ x : ℝ in -1..1,
      centeredEvenP2 x * fixedProjectedShiftedRemainder0 x) =
      -yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x *
              centeredEvenP2 x) +
        2 * yoshidaEndpointA *
          yoshidaEndpointCoshMoment centeredEvenP0 *
            yoshidaEndpointCoshMoment centeredEvenP2 -
        7 / 24 := by
  have hR02 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x *
        centeredEvenP2 x) volume (-1) 1 :=
    intervalIntegrable_regularRepresenter_mul centeredEvenP0 centeredEvenP2
      (by unfold centeredEvenP0; fun_prop) (by unfold centeredEvenP2; fun_prop)
  have hCoshP2 : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * centeredEvenP2 x)
      volume (-1) 1 :=
    (by unfold centeredEvenP2; fun_prop : Continuous fun x : ℝ ↦
      Real.cosh (yoshidaEndpointA * x / 2) * centeredEvenP2 x)
      |>.intervalIntegrable (-1) 1
  have hProj : IntervalIntegrable
      (fun x : ℝ ↦ centeredEvenP2 x * fixedProjectionPolynomial 1 0 x)
      volume (-1) 1 :=
    (by unfold fixedProjectionPolynomial centeredEvenP0 centeredEvenP2; fun_prop :
      Continuous fun x : ℝ ↦ centeredEvenP2 x * fixedProjectionPolynomial 1 0 x)
      |>.intervalIntegrable (-1) 1
  have h02 : IntervalIntegrable
      (fun x : ℝ ↦ centeredEvenP0 x * centeredEvenP2 x) volume (-1) 1 :=
    (by unfold centeredEvenP0 centeredEvenP2; fun_prop : Continuous fun x : ℝ ↦
      centeredEvenP0 x * centeredEvenP2 x) |>.intervalIntegrable (-1) 1
  rw [show (fun x : ℝ ↦
      centeredEvenP2 x * fixedProjectedShiftedRemainder0 x) =
      fun x ↦ (((-yoshidaEndpointA) *
          (yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x *
            centeredEvenP2 x) +
        (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP0) *
          (Real.cosh (yoshidaEndpointA * x / 2) * centeredEvenP2 x)) -
        centeredEvenP2 x * fixedProjectionPolynomial 1 0 x) -
        (41 / 60 : ℝ) * (centeredEvenP0 x * centeredEvenP2 x) by
    funext x
    unfold fixedProjectedShiftedRemainder0 fixedProjectedShiftedRemainder
      fixedProjectedBoundedRemainder fixedEvenLowProfile
    ring]
  rw [intervalIntegral.integral_sub
      (((hR02.const_mul (-yoshidaEndpointA)).add
        (hCoshP2.const_mul
          (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP0))).sub
        hProj) (h02.const_mul (41 / 60 : ℝ)),
    intervalIntegral.integral_sub
      ((hR02.const_mul (-yoshidaEndpointA)).add
        (hCoshP2.const_mul
          (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP0)))
      hProj,
    intervalIntegral.integral_add (hR02.const_mul (-yoshidaEndpointA))
      (hCoshP2.const_mul
        (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP0)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_p2_mul_fixedProjectionPolynomial_10,
    integral_centeredEvenP0_mul_p2]
  have hC2 : (∫ x : ℝ in -1..1,
      Real.cosh (yoshidaEndpointA * x / 2) * centeredEvenP2 x) =
      yoshidaEndpointCoshMoment centeredEvenP2 := by
    unfold yoshidaEndpointCoshMoment
    rfl
  rw [hC2]
  ring

private theorem integral_p2_mul_shifted2_expansion :
    (∫ x : ℝ in -1..1,
      centeredEvenP2 x * fixedProjectedShiftedRemainder2 x) =
      -yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x *
              centeredEvenP2 x) +
        2 * yoshidaEndpointA *
          yoshidaEndpointCoshMoment centeredEvenP2 ^ 2 -
        1 / 5 - 41 / 150 := by
  have hR22 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x *
        centeredEvenP2 x) volume (-1) 1 :=
    intervalIntegrable_regularRepresenter_mul centeredEvenP2 centeredEvenP2
      (by unfold centeredEvenP2; fun_prop) (by unfold centeredEvenP2; fun_prop)
  have hCoshP2 : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * centeredEvenP2 x)
      volume (-1) 1 :=
    (by unfold centeredEvenP2; fun_prop : Continuous fun x : ℝ ↦
      Real.cosh (yoshidaEndpointA * x / 2) * centeredEvenP2 x)
      |>.intervalIntegrable (-1) 1
  have hProj : IntervalIntegrable
      (fun x : ℝ ↦ centeredEvenP2 x * fixedProjectionPolynomial 0 1 x)
      volume (-1) 1 :=
    (by unfold fixedProjectionPolynomial centeredEvenP0 centeredEvenP2; fun_prop :
      Continuous fun x : ℝ ↦ centeredEvenP2 x * fixedProjectionPolynomial 0 1 x)
      |>.intervalIntegrable (-1) 1
  have h22 : IntervalIntegrable (fun x : ℝ ↦ centeredEvenP2 x ^ 2)
      volume (-1) 1 :=
    (by unfold centeredEvenP2; fun_prop : Continuous fun x : ℝ ↦
      centeredEvenP2 x ^ 2) |>.intervalIntegrable (-1) 1
  rw [show (fun x : ℝ ↦
      centeredEvenP2 x * fixedProjectedShiftedRemainder2 x) =
      fun x ↦ (((-yoshidaEndpointA) *
          (yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x *
            centeredEvenP2 x) +
        (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP2) *
          (Real.cosh (yoshidaEndpointA * x / 2) * centeredEvenP2 x)) -
        centeredEvenP2 x * fixedProjectionPolynomial 0 1 x) -
        (41 / 60 : ℝ) * centeredEvenP2 x ^ 2 by
    funext x
    unfold fixedProjectedShiftedRemainder2 fixedProjectedShiftedRemainder
      fixedProjectedBoundedRemainder fixedEvenLowProfile centeredEvenP0
    ring]
  rw [intervalIntegral.integral_sub
      (((hR22.const_mul (-yoshidaEndpointA)).add
        (hCoshP2.const_mul
          (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP2))).sub
        hProj) (h22.const_mul (41 / 60 : ℝ)),
    intervalIntegral.integral_sub
      ((hR22.const_mul (-yoshidaEndpointA)).add
        (hCoshP2.const_mul
          (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP2)))
      hProj,
    intervalIntegral.integral_add (hR22.const_mul (-yoshidaEndpointA))
      (hCoshP2.const_mul
        (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP2)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_p2_mul_fixedProjectionPolynomial_01,
    integral_centeredEvenP2_sq]
  have hC2 : (∫ x : ℝ in -1..1,
      Real.cosh (yoshidaEndpointA * x / 2) * centeredEvenP2 x) =
      yoshidaEndpointCoshMoment centeredEvenP2 := by
    unfold yoshidaEndpointCoshMoment
    rfl
  rw [hC2]
  ring

/-- Exact constant-coordinate gap identity. -/
theorem fixedProjectedGapGram00_exact :
    fixedProjectedGapGram00 =
      (73 / 24 : ℝ) - 2 * yoshidaEndpointScalarMassLoss -
        ∫ x : ℝ in -1..1, fixedProjectedShiftedRemainder0 x := by
  have hD := integral_shifted0_expansion
  unfold fixedProjectedGapGram00
  rw [exactLowGram00_expansion, fixedProjectedDualBaseGram00_expansion]
  linarith

/-- Exact mixed-coordinate gap identity. -/
theorem fixedProjectedGapGram02_exact :
    fixedProjectedGapGram02 =
      (7 / 24 : ℝ) -
        ((∫ x : ℝ in -1..1, fixedProjectedShiftedRemainder2 x) +
          ∫ x : ℝ in -1..1,
            centeredEvenP2 x * fixedProjectedShiftedRemainder0 x) / 2 := by
  have hD2 := integral_shifted2_expansion
  have hP2D0 := integral_p2_mul_shifted0_expansion
  unfold fixedProjectedGapGram02
  rw [exactLowGram02_expansion, fixedProjectedDualBaseGram02_expansion]
  linarith

/-- Exact degree-two-coordinate gap identity. -/
theorem fixedProjectedGapGram22_exact :
    fixedProjectedGapGram22 =
      (4 / 5 : ℝ) - (2 / 5 : ℝ) * yoshidaEndpointScalarMassLoss -
        ∫ x : ℝ in -1..1,
          centeredEvenP2 x * fixedProjectedShiftedRemainder2 x := by
  have hD := integral_p2_mul_shifted2_expansion
  unfold fixedProjectedGapGram22
  rw [exactLowGram22_expansion, fixedProjectedDualBaseGram22_expansion]
  linarith

private def elementaryEvenMoment (n : ℕ) : ℝ := 2 / (2 * (n : ℝ) + 1)

private theorem integral_evenPolynomial
    (N : ℕ) (c : ℕ → ℝ) :
    (∫ x : ℝ in -1..1,
      ∑ n ∈ Finset.range N, c n * x ^ (2 * n)) =
      ∑ n ∈ Finset.range N, c n * elementaryEvenMoment n := by
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n _hn
    rw [intervalIntegral.integral_const_mul, integral_pow]
    unfold elementaryEvenMoment
    norm_num [pow_mul]
  · intro n _hn
    exact ((continuous_id.pow (2 * n)).const_mul (c n)).intervalIntegrable (-1) 1

private theorem integral_centeredEnvelopePolynomial0 :
    (∫ x : ℝ in -1..1, centeredEnvelopePolynomial0 x) =
      -(1458306257 / 750000000 : ℝ) := by
  let c : ℕ → ℝ
    | 0 => -123253709 / 200000000
    | 1 => -213563519 / 200000000
    | 2 => 3507 / 200000000
    | 3 => 91 / 200000000
    | _ => 0
  calc
    (∫ x : ℝ in -1..1, centeredEnvelopePolynomial0 x) =
        ∫ x : ℝ in -1..1,
          ∑ n ∈ Finset.range 4, c n * x ^ (2 * n) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      simp [c, centeredEnvelopePolynomial0, Finset.sum_range_succ]
    _ = ∑ n ∈ Finset.range 4, c n * elementaryEvenMoment n :=
      integral_evenPolynomial 4 c
    _ = -(1458306257 / 750000000 : ℝ) := by
      norm_num [c, elementaryEvenMoment, Finset.sum_range_succ]

private theorem integral_centeredEnvelopePolynomial2 :
    (∫ x : ℝ in -1..1, centeredEnvelopePolynomial2 x) =
      -(8969538901 / 31500000000 : ℝ) := by
  let c : ℕ → ℝ
    | 0 => 89916223 / 200000000
    | 1 => -355248257 / 200000000
    | 2 => 125743 / 200000000
    | 3 => -89 / 200000000
    | 4 => 1 / 200000000
    | _ => 0
  calc
    (∫ x : ℝ in -1..1, centeredEnvelopePolynomial2 x) =
        ∫ x : ℝ in -1..1,
          ∑ n ∈ Finset.range 5, c n * x ^ (2 * n) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      simp [c, centeredEnvelopePolynomial2, Finset.sum_range_succ]
    _ = ∑ n ∈ Finset.range 5, c n * elementaryEvenMoment n :=
      integral_evenPolynomial 5 c
    _ = -(8969538901 / 31500000000 : ℝ) := by
      norm_num [c, elementaryEvenMoment, Finset.sum_range_succ]

private theorem integral_p2_mul_centeredEnvelopePolynomial0 :
    (∫ x : ℝ in -1..1,
      centeredEvenP2 x * centeredEnvelopePolynomial0 x) =
      -(556147 / 1953125 : ℝ) := by
  let a0 : ℝ := -123253709 / 200000000
  let a1 : ℝ := -213563519 / 200000000
  let a2 : ℝ := 3507 / 200000000
  let a3 : ℝ := 91 / 200000000
  let c : ℕ → ℝ
    | 0 => -a0 / 2
    | 1 => (3 * a0 - a1) / 2
    | 2 => (3 * a1 - a2) / 2
    | 3 => (3 * a2 - a3) / 2
    | 4 => 3 * a3 / 2
    | _ => 0
  calc
    (∫ x : ℝ in -1..1,
        centeredEvenP2 x * centeredEnvelopePolynomial0 x) =
        ∫ x : ℝ in -1..1,
          ∑ n ∈ Finset.range 5, c n * x ^ (2 * n) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      simp [c, a0, a1, a2, a3, centeredEvenP2,
        centeredEnvelopePolynomial0, Finset.sum_range_succ]
      ring
    _ = ∑ n ∈ Finset.range 5, c n * elementaryEvenMoment n :=
      integral_evenPolynomial 5 c
    _ = -(556147 / 1953125 : ℝ) := by
      norm_num [c, a0, a1, a2, a3, elementaryEvenMoment,
        Finset.sum_range_succ]

private theorem integral_p2_mul_centeredEnvelopePolynomial2 :
    (∫ x : ℝ in -1..1,
      centeredEvenP2 x * centeredEnvelopePolynomial2 x) =
      -(41018732399 / 86625000000 : ℝ) := by
  let a0 : ℝ := 89916223 / 200000000
  let a1 : ℝ := -355248257 / 200000000
  let a2 : ℝ := 125743 / 200000000
  let a3 : ℝ := -89 / 200000000
  let a4 : ℝ := 1 / 200000000
  let c : ℕ → ℝ
    | 0 => -a0 / 2
    | 1 => (3 * a0 - a1) / 2
    | 2 => (3 * a1 - a2) / 2
    | 3 => (3 * a2 - a3) / 2
    | 4 => (3 * a3 - a4) / 2
    | 5 => 3 * a4 / 2
    | _ => 0
  calc
    (∫ x : ℝ in -1..1,
        centeredEvenP2 x * centeredEnvelopePolynomial2 x) =
        ∫ x : ℝ in -1..1,
          ∑ n ∈ Finset.range 6, c n * x ^ (2 * n) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      simp [c, a0, a1, a2, a3, a4, centeredEvenP2,
        centeredEnvelopePolynomial2, Finset.sum_range_succ]
      ring
    _ = ∑ n ∈ Finset.range 6, c n * elementaryEvenMoment n :=
      integral_evenPolynomial 6 c
    _ = -(41018732399 / 86625000000 : ℝ) := by
      norm_num [c, a0, a1, a2, a3, a4, elementaryEvenMoment,
        Finset.sum_range_succ]

private theorem abs_centeredEvenP2_le_one
    {x : ℝ} (hx : x ∈ Icc (-1) 1) : |centeredEvenP2 x| ≤ 1 := by
  have hxSq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 (abs_le.mpr hx)
  unfold centeredEvenP2
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg x]

private theorem abs_integral_shifted0_sub_center_lt :
    |(∫ x : ℝ in -1..1, fixedProjectedShiftedRemainder0 x) -
        ∫ x : ℝ in -1..1, centeredEnvelopePolynomial0 x| <
      (1 / 350000 : ℝ) := by
  have hcenter : IntervalIntegrable centeredEnvelopePolynomial0 volume (-1) 1 :=
    (by unfold centeredEnvelopePolynomial0; fun_prop :
      Continuous centeredEnvelopePolynomial0) |>.intervalIntegrable (-1) 1
  rw [← intervalIntegral.integral_sub intervalIntegrable_shifted0 hcenter,
    ← Real.norm_eq_abs]
  calc
    ‖∫ x : ℝ in -1..1,
        fixedProjectedShiftedRemainder0 x - centeredEnvelopePolynomial0 x‖ ≤
        ((1 / 720000 : ℝ) + 1 / 50000000) * |(1 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le (by norm_num)] at hx
      have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have htrue := abs_fixedProjectedShiftedRemainder0_sub_explicit_lt hxIcc
      have hpoly := abs_shiftedPolynomial0_sub_center_lt hxIcc
      rw [Real.norm_eq_abs]
      calc
        |fixedProjectedShiftedRemainder0 x - centeredEnvelopePolynomial0 x| =
            |(fixedProjectedShiftedRemainder0 x -
                shiftedRemainderPolynomial6_0_explicit x) +
              (shiftedRemainderPolynomial6_0_explicit x -
                centeredEnvelopePolynomial0 x)| := by
          congr 1
          ring
        _ ≤ |fixedProjectedShiftedRemainder0 x -
              shiftedRemainderPolynomial6_0_explicit x| +
            |shiftedRemainderPolynomial6_0_explicit x -
              centeredEnvelopePolynomial0 x| := abs_add_le _ _
        _ ≤ (1 / 720000 : ℝ) + 1 / 50000000 :=
          (add_lt_add htrue hpoly).le
    _ < (1 / 350000 : ℝ) := by norm_num

private theorem abs_integral_shifted2_sub_center_lt :
    |(∫ x : ℝ in -1..1, fixedProjectedShiftedRemainder2 x) -
        ∫ x : ℝ in -1..1, centeredEnvelopePolynomial2 x| <
      (1 / 850000 : ℝ) := by
  have hcenter : IntervalIntegrable centeredEnvelopePolynomial2 volume (-1) 1 :=
    (by unfold centeredEnvelopePolynomial2; fun_prop :
      Continuous centeredEnvelopePolynomial2) |>.intervalIntegrable (-1) 1
  rw [← intervalIntegral.integral_sub intervalIntegrable_shifted2 hcenter,
    ← Real.norm_eq_abs]
  calc
    ‖∫ x : ℝ in -1..1,
        fixedProjectedShiftedRemainder2 x - centeredEnvelopePolynomial2 x‖ ≤
        ((1 / 1800000 : ℝ) + 1 / 40000000) * |(1 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le (by norm_num)] at hx
      have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have htrue := abs_fixedProjectedShiftedRemainder2_sub_explicit_lt hxIcc
      have hpoly := abs_shiftedPolynomial2_sub_center_lt hxIcc
      rw [Real.norm_eq_abs]
      calc
        |fixedProjectedShiftedRemainder2 x - centeredEnvelopePolynomial2 x| =
            |(fixedProjectedShiftedRemainder2 x -
                shiftedRemainderPolynomial6_2_explicit x) +
              (shiftedRemainderPolynomial6_2_explicit x -
                centeredEnvelopePolynomial2 x)| := by
          congr 1
          ring
        _ ≤ |fixedProjectedShiftedRemainder2 x -
              shiftedRemainderPolynomial6_2_explicit x| +
            |shiftedRemainderPolynomial6_2_explicit x -
              centeredEnvelopePolynomial2 x| := abs_add_le _ _
        _ ≤ (1 / 1800000 : ℝ) + 1 / 40000000 :=
          (add_lt_add htrue hpoly).le
    _ < (1 / 850000 : ℝ) := by norm_num

private theorem abs_integral_p2_shifted0_sub_center_lt :
    |(∫ x : ℝ in -1..1,
        centeredEvenP2 x * fixedProjectedShiftedRemainder0 x) -
        ∫ x : ℝ in -1..1,
          centeredEvenP2 x * centeredEnvelopePolynomial0 x| <
      (1 / 350000 : ℝ) := by
  have htrue : IntervalIntegrable
      (fun x : ℝ ↦ centeredEvenP2 x * fixedProjectedShiftedRemainder0 x)
      volume (-1) 1 := by
    apply (intervalIntegrable_shifted0.mul_continuousOn
      (by unfold centeredEvenP2; fun_prop : Continuous centeredEvenP2).continuousOn).congr
    intro x _hx
    ring
  have hcenter : IntervalIntegrable
      (fun x : ℝ ↦ centeredEvenP2 x * centeredEnvelopePolynomial0 x)
      volume (-1) 1 :=
    (by unfold centeredEvenP2 centeredEnvelopePolynomial0; fun_prop : Continuous
      (fun x : ℝ ↦ centeredEvenP2 x * centeredEnvelopePolynomial0 x))
      |>.intervalIntegrable (-1) 1
  rw [← intervalIntegral.integral_sub htrue hcenter, ← Real.norm_eq_abs]
  calc
    ‖∫ x : ℝ in -1..1,
        centeredEvenP2 x * fixedProjectedShiftedRemainder0 x -
          centeredEvenP2 x * centeredEnvelopePolynomial0 x‖ ≤
        ((1 / 720000 : ℝ) + 1 / 50000000) * |(1 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le (by norm_num)] at hx
      have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have hP2 := abs_centeredEvenP2_le_one hxIcc
      have htrueErr := abs_fixedProjectedShiftedRemainder0_sub_explicit_lt hxIcc
      have hpolyErr := abs_shiftedPolynomial0_sub_center_lt hxIcc
      have hdiff :
          |fixedProjectedShiftedRemainder0 x - centeredEnvelopePolynomial0 x| ≤
            (1 / 720000 : ℝ) + 1 / 50000000 := by
        calc
          |fixedProjectedShiftedRemainder0 x - centeredEnvelopePolynomial0 x| =
              |(fixedProjectedShiftedRemainder0 x -
                  shiftedRemainderPolynomial6_0_explicit x) +
                (shiftedRemainderPolynomial6_0_explicit x -
                  centeredEnvelopePolynomial0 x)| := by
            congr 1
            ring
          _ ≤ |fixedProjectedShiftedRemainder0 x -
                shiftedRemainderPolynomial6_0_explicit x| +
              |shiftedRemainderPolynomial6_0_explicit x -
                centeredEnvelopePolynomial0 x| := abs_add_le _ _
          _ ≤ (1 / 720000 : ℝ) + 1 / 50000000 :=
            (add_lt_add htrueErr hpolyErr).le
      rw [show centeredEvenP2 x * fixedProjectedShiftedRemainder0 x -
            centeredEvenP2 x * centeredEnvelopePolynomial0 x =
          centeredEvenP2 x *
            (fixedProjectedShiftedRemainder0 x - centeredEnvelopePolynomial0 x) by ring,
        Real.norm_eq_abs, abs_mul]
      calc
        |centeredEvenP2 x| *
            |fixedProjectedShiftedRemainder0 x - centeredEnvelopePolynomial0 x| ≤
            1 * |fixedProjectedShiftedRemainder0 x -
              centeredEnvelopePolynomial0 x| :=
          mul_le_mul_of_nonneg_right hP2 (abs_nonneg _)
        _ ≤ (1 / 720000 : ℝ) + 1 / 50000000 := by simpa using hdiff
    _ < (1 / 350000 : ℝ) := by norm_num

private theorem abs_integral_p2_shifted2_sub_center_lt :
    |(∫ x : ℝ in -1..1,
        centeredEvenP2 x * fixedProjectedShiftedRemainder2 x) -
        ∫ x : ℝ in -1..1,
          centeredEvenP2 x * centeredEnvelopePolynomial2 x| <
      (1 / 850000 : ℝ) := by
  have htrue : IntervalIntegrable
      (fun x : ℝ ↦ centeredEvenP2 x * fixedProjectedShiftedRemainder2 x)
      volume (-1) 1 := by
    apply (intervalIntegrable_shifted2.mul_continuousOn
      (by unfold centeredEvenP2; fun_prop : Continuous centeredEvenP2).continuousOn).congr
    intro x _hx
    ring
  have hcenter : IntervalIntegrable
      (fun x : ℝ ↦ centeredEvenP2 x * centeredEnvelopePolynomial2 x)
      volume (-1) 1 :=
    (by unfold centeredEvenP2 centeredEnvelopePolynomial2; fun_prop : Continuous
      (fun x : ℝ ↦ centeredEvenP2 x * centeredEnvelopePolynomial2 x))
      |>.intervalIntegrable (-1) 1
  rw [← intervalIntegral.integral_sub htrue hcenter, ← Real.norm_eq_abs]
  calc
    ‖∫ x : ℝ in -1..1,
        centeredEvenP2 x * fixedProjectedShiftedRemainder2 x -
          centeredEvenP2 x * centeredEnvelopePolynomial2 x‖ ≤
        ((1 / 1800000 : ℝ) + 1 / 40000000) * |(1 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le (by norm_num)] at hx
      have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have hP2 := abs_centeredEvenP2_le_one hxIcc
      have htrueErr := abs_fixedProjectedShiftedRemainder2_sub_explicit_lt hxIcc
      have hpolyErr := abs_shiftedPolynomial2_sub_center_lt hxIcc
      have hdiff :
          |fixedProjectedShiftedRemainder2 x - centeredEnvelopePolynomial2 x| ≤
            (1 / 1800000 : ℝ) + 1 / 40000000 := by
        calc
          |fixedProjectedShiftedRemainder2 x - centeredEnvelopePolynomial2 x| =
              |(fixedProjectedShiftedRemainder2 x -
                  shiftedRemainderPolynomial6_2_explicit x) +
                (shiftedRemainderPolynomial6_2_explicit x -
                  centeredEnvelopePolynomial2 x)| := by
            congr 1
            ring
          _ ≤ |fixedProjectedShiftedRemainder2 x -
                shiftedRemainderPolynomial6_2_explicit x| +
              |shiftedRemainderPolynomial6_2_explicit x -
                centeredEnvelopePolynomial2 x| := abs_add_le _ _
          _ ≤ (1 / 1800000 : ℝ) + 1 / 40000000 :=
            (add_lt_add htrueErr hpolyErr).le
      rw [show centeredEvenP2 x * fixedProjectedShiftedRemainder2 x -
            centeredEvenP2 x * centeredEnvelopePolynomial2 x =
          centeredEvenP2 x *
            (fixedProjectedShiftedRemainder2 x - centeredEnvelopePolynomial2 x) by ring,
        Real.norm_eq_abs, abs_mul]
      calc
        |centeredEvenP2 x| *
            |fixedProjectedShiftedRemainder2 x - centeredEnvelopePolynomial2 x| ≤
            1 * |fixedProjectedShiftedRemainder2 x -
              centeredEnvelopePolynomial2 x| :=
          mul_le_mul_of_nonneg_right hP2 (abs_nonneg _)
        _ ≤ (1 / 1800000 : ℝ) + 1 / 40000000 := by simpa using hdiff
    _ < (1 / 850000 : ℝ) := by norm_num

/-- Structural lower bound for the constant gap entry. -/
theorem fixedProjectedGapGram00_gt :
    (22749 / 10000 : ℝ) < fixedProjectedGapGram00 := by
  have hscalar := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hI := abs_lt.mp abs_integral_shifted0_sub_center_lt
  rw [integral_centeredEnvelopePolynomial0] at hI
  rw [fixedProjectedGapGram00_exact]
  norm_num at hscalar hI ⊢
  linarith

/-- Two-sided structural enclosure for the mixed gap entry. -/
theorem fixedProjectedGapGram02_bounds :
    (57641 / 100000 : ℝ) < fixedProjectedGapGram02 ∧
      fixedProjectedGapGram02 < (57642 / 100000 : ℝ) := by
  have hI2 := abs_lt.mp abs_integral_shifted2_sub_center_lt
  have hI20 := abs_lt.mp abs_integral_p2_shifted0_sub_center_lt
  rw [integral_centeredEnvelopePolynomial2] at hI2
  rw [integral_p2_mul_centeredEnvelopePolynomial0] at hI20
  rw [fixedProjectedGapGram02_exact]
  constructor <;> norm_num at hI2 hI20 ⊢ <;> linarith

/-- Structural lower bound for the degree-two gap entry. -/
theorem fixedProjectedGapGram22_gt :
    (73129 / 100000 : ℝ) < fixedProjectedGapGram22 := by
  have hscalar := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hI := abs_lt.mp abs_integral_p2_shifted2_sub_center_lt
  rw [integral_p2_mul_centeredEnvelopePolynomial2] at hI
  rw [fixedProjectedGapGram22_exact]
  norm_num at hscalar hI ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeClosure
