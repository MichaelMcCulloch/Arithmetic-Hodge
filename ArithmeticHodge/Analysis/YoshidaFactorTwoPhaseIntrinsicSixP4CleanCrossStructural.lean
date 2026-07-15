import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeMoments
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural

noncomputable section

open YoshidaConstantBounds
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenProjectedBaseIntegrable
open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenProjectedRemainderEnvelopeMoments
open YoshidaEndpointEvenProjectedRemainderEnvelopePolynomials
open YoshidaEndpointEvenProjectedRemainderMoments
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialExactLowMode
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
open YoshidaFactorTwoPhaseLegendreFourFiveStructural

/-!
# Structural clean `P0/P2`--`P4` crosses

The endpoint-independent clean crosses are reduced to two exact potential
moments and a single global degree-six Taylor remainder.  No subdivision,
quadrature, or finite certificate is used.
-/

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
    unfold fixedProjectionPolynomial fixedEvenLowProfile centeredEvenP0
      centeredEvenP2
    fun_prop
  apply (hregular.add (hcontinuous.intervalIntegrable (-1) 1)).congr
  intro x _hx
  unfold fixedProjectedShiftedRemainder fixedProjectedBoundedRemainder
  ring

private theorem intervalIntegrable_shifted0 :
    IntervalIntegrable fixedProjectedShiftedRemainder0 volume (-1) 1 := by
  unfold fixedProjectedShiftedRemainder0
  exact intervalIntegrable_fixedProjectedShiftedRemainder_local 1 0

private theorem intervalIntegrable_shifted2 :
    IntervalIntegrable fixedProjectedShiftedRemainder2 volume (-1) 1 := by
  unfold fixedProjectedShiftedRemainder2
  exact intervalIntegrable_fixedProjectedShiftedRemainder_local 0 1

/-- Exact potential part of the clean `P0`--`P4` cross. -/
theorem integral_endpointPotential_mul_centeredEvenP0_mul_P4 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredEvenP0 x *
        factorTwoCenteredP4 x) = (1 / 10 : ℝ) := by
  have h0 : IntervalIntegrable yoshidaEndpointPotential volume (-1) 1 :=
    by simpa only [one_pow, mul_one] using
      intervalIntegrable_endpointPotential_mul_sq (fun _x : ℝ ↦ 1)
        continuous_const
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq (fun x : ℝ ↦ x) continuous_id
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 :=
    by
      apply (intervalIntegrable_endpointPotential_mul_sq
        (fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2)).congr
      intro x _hx
      ring
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredEvenP0 x *
        factorTwoCenteredP4 x) =
      fun x ↦ (35 / 8 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) -
        (30 / 8 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) +
        (3 / 8 : ℝ) * yoshidaEndpointPotential x by
    funext x
    unfold centeredEvenP0 factorTwoCenteredP4
    ring,
    intervalIntegral.integral_add
      ((h4.const_mul (35 / 8 : ℝ)).sub (h2.const_mul (30 / 8 : ℝ)))
      (h0.const_mul (3 / 8 : ℝ)),
    intervalIntegral.integral_sub
      (h4.const_mul (35 / 8 : ℝ)) (h2.const_mul (30 / 8 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq, integral_endpointPotential_one]
  ring

/-- Exact potential part of the clean `P2`--`P4` cross. -/
theorem integral_endpointPotential_mul_centeredEvenP2_mul_P4 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredEvenP2 x *
        factorTwoCenteredP4 x) = (1 / 7 : ℝ) := by
  have h0 : IntervalIntegrable yoshidaEndpointPotential volume (-1) 1 :=
    by simpa only [one_pow, mul_one] using
      intervalIntegrable_endpointPotential_mul_sq (fun _x : ℝ ↦ 1)
        continuous_const
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq (fun x : ℝ ↦ x) continuous_id
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 :=
    by
      apply (intervalIntegrable_endpointPotential_mul_sq
        (fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2)).congr
      intro x _hx
      ring
  have h6 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 6) volume (-1) 1 :=
    by
      apply (intervalIntegrable_endpointPotential_mul_sq
        (fun x : ℝ ↦ x ^ 3) (continuous_id.pow 3)).congr
      intro x _hx
      ring
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredEvenP2 x *
        factorTwoCenteredP4 x) =
      fun x ↦ (105 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) -
        (125 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) +
        (39 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) -
        (3 / 16 : ℝ) * yoshidaEndpointPotential x by
    funext x
    unfold centeredEvenP2 factorTwoCenteredP4
    ring,
    intervalIntegral.integral_sub
      (((h6.const_mul (105 / 16 : ℝ)).sub
        (h4.const_mul (125 / 16 : ℝ))).add
          (h2.const_mul (39 / 16 : ℝ)))
      (h0.const_mul (3 / 16 : ℝ)),
    intervalIntegral.integral_add
      ((h6.const_mul (105 / 16 : ℝ)).sub
        (h4.const_mul (125 / 16 : ℝ)))
      (h2.const_mul (39 / 16 : ℝ)),
    intervalIntegral.integral_sub
      (h6.const_mul (105 / 16 : ℝ)) (h4.const_mul (125 / 16 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq, integral_endpointPotential_one]
  ring

/-- The clean `P0`--`P4` cross is its exact potential moment plus one
projected smooth remainder pairing. -/
theorem factorTwoIntrinsicP4CleanCross04_eq_potential_add_remainder :
    yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 =
      (1 / 10 : ℝ) +
        ∫ x : ℝ in -1..1,
          fixedProjectedShiftedRemainder0 x * factorTwoCenteredP4 x := by
  have hclean := yoshidaEndpointEvenLowTailCross_zero factorTwoCenteredP4
    continuous_factorTwoCenteredP4 even_factorTwoCenteredP4
    integral_factorTwoCenteredP4
  have hV := intervalIntegrable_endpointPotential_mul centeredEvenP0
    factorTwoCenteredP4 (by unfold centeredEvenP0; fun_prop)
      continuous_factorTwoCenteredP4
  have hshift : IntervalIntegrable
      (fun x ↦ fixedProjectedShiftedRemainder0 x * factorTwoCenteredP4 x)
      volume (-1) 1 :=
    intervalIntegrable_shifted0.mul_continuousOn
      continuous_factorTwoCenteredP4.continuousOn
  have hP4 : IntervalIntegrable factorTwoCenteredP4 volume (-1) 1 :=
    continuous_factorTwoCenteredP4.intervalIntegrable (-1) 1
  have hP2P4 : IntervalIntegrable
      (fun x ↦ factorTwoCenteredP4 x * centeredEvenP2 x) volume (-1) 1 :=
    (continuous_factorTwoCenteredP4.mul
      (by unfold centeredEvenP2; fun_prop : Continuous centeredEvenP2))
        |>.intervalIntegrable (-1) 1
  have hproj : IntervalIntegrable
      (fun x ↦ fixedProjectionPolynomial 1 0 x * factorTwoCenteredP4 x)
      volume (-1) 1 := by
    have hp : Continuous (fun x : ℝ ↦ fixedProjectionPolynomial 1 0 x) := by
      unfold fixedProjectionPolynomial centeredEvenP0 centeredEvenP2
      fun_prop
    exact (hp.mul continuous_factorTwoCenteredP4).intervalIntegrable (-1) 1
  have hprojZero :
      (∫ x : ℝ in -1..1,
        fixedProjectionPolynomial 1 0 x * factorTwoCenteredP4 x) = 0 := by
    rw [show (fun x : ℝ ↦
        fixedProjectionPolynomial 1 0 x * factorTwoCenteredP4 x) =
      fun x ↦ (73 / 48 : ℝ) * factorTwoCenteredP4 x +
        (35 / 48 : ℝ) *
          (factorTwoCenteredP4 x * centeredEvenP2 x) by
      funext x
      unfold fixedProjectionPolynomial centeredEvenP0
      ring,
      intervalIntegral.integral_add (hP4.const_mul (73 / 48 : ℝ))
        (hP2P4.const_mul (35 / 48 : ℝ)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_factorTwoCenteredP4,
      integral_factorTwoCenteredP4_mul_centeredEvenP2]
    ring
  rw [hclean]
  unfold yoshidaEndpointEvenTailRepresenter0
  rw [show (fun x : ℝ ↦
      yoshidaEndpointEvenTailRepresenter centeredEvenP0 x *
        factorTwoCenteredP4 x) =
      fun x ↦ (yoshidaEndpointPotential x * centeredEvenP0 x *
          factorTwoCenteredP4 x +
        fixedProjectedShiftedRemainder0 x * factorTwoCenteredP4 x +
        (41 / 60 : ℝ) * factorTwoCenteredP4 x) +
        fixedProjectionPolynomial 1 0 x * factorTwoCenteredP4 x by
    funext x
    unfold yoshidaEndpointEvenTailRepresenter fixedProjectedShiftedRemainder0
      fixedProjectedShiftedRemainder fixedProjectedBoundedRemainder
      fixedProjectionPolynomial fixedEvenLowProfile centeredEvenP0 centeredEvenP2
    ring,
    intervalIntegral.integral_add
      ((hV.add hshift).add (hP4.const_mul (41 / 60 : ℝ))) hproj,
    intervalIntegral.integral_add (hV.add hshift)
      (hP4.const_mul (41 / 60 : ℝ)),
    intervalIntegral.integral_add hV hshift,
    intervalIntegral.integral_const_mul,
    integral_factorTwoCenteredP4, hprojZero,
    integral_endpointPotential_mul_centeredEvenP0_mul_P4]
  ring

/-- The clean `P2`--`P4` cross has the analogous exact decomposition. -/
theorem factorTwoIntrinsicP4CleanCross24_eq_potential_add_remainder :
    yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 =
      (1 / 7 : ℝ) +
        ∫ x : ℝ in -1..1,
          fixedProjectedShiftedRemainder2 x * factorTwoCenteredP4 x := by
  have hclean := yoshidaEndpointEvenLowTailCross_two factorTwoCenteredP4
    continuous_factorTwoCenteredP4 even_factorTwoCenteredP4
    integral_factorTwoCenteredP4_mul_centeredEvenP2
  have hV := intervalIntegrable_endpointPotential_mul centeredEvenP2
    factorTwoCenteredP4 (by unfold centeredEvenP2; fun_prop)
      continuous_factorTwoCenteredP4
  have hshift : IntervalIntegrable
      (fun x ↦ fixedProjectedShiftedRemainder2 x * factorTwoCenteredP4 x)
      volume (-1) 1 :=
    intervalIntegrable_shifted2.mul_continuousOn
      continuous_factorTwoCenteredP4.continuousOn
  have hP2P4 : IntervalIntegrable
      (fun x ↦ centeredEvenP2 x * factorTwoCenteredP4 x) volume (-1) 1 :=
    ((by unfold centeredEvenP2; fun_prop : Continuous centeredEvenP2).mul
      continuous_factorTwoCenteredP4).intervalIntegrable (-1) 1
  have hP4 : IntervalIntegrable factorTwoCenteredP4 volume (-1) 1 :=
    continuous_factorTwoCenteredP4.intervalIntegrable (-1) 1
  have hproj : IntervalIntegrable
      (fun x ↦ fixedProjectionPolynomial 0 1 x * factorTwoCenteredP4 x)
      volume (-1) 1 := by
    have hp : Continuous (fun x : ℝ ↦ fixedProjectionPolynomial 0 1 x) := by
      unfold fixedProjectionPolynomial centeredEvenP0 centeredEvenP2
      fun_prop
    exact (hp.mul continuous_factorTwoCenteredP4).intervalIntegrable (-1) 1
  have hprojZero :
      (∫ x : ℝ in -1..1,
        fixedProjectionPolynomial 0 1 x * factorTwoCenteredP4 x) = 0 := by
    rw [show (fun x : ℝ ↦
        fixedProjectionPolynomial 0 1 x * factorTwoCenteredP4 x) =
      fun x ↦ (7 / 48 : ℝ) * factorTwoCenteredP4 x +
        (1 / 2 : ℝ) *
          (centeredEvenP2 x * factorTwoCenteredP4 x) by
      funext x
      unfold fixedProjectionPolynomial centeredEvenP0
      ring,
      intervalIntegral.integral_add (hP4.const_mul (7 / 48 : ℝ))
        (hP2P4.const_mul (1 / 2 : ℝ)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_factorTwoCenteredP4,
      show (∫ x : ℝ in -1..1,
        centeredEvenP2 x * factorTwoCenteredP4 x) = 0 by
        simpa only [mul_comm] using
          integral_factorTwoCenteredP4_mul_centeredEvenP2]
    ring
  rw [hclean]
  unfold yoshidaEndpointEvenTailRepresenter2
  rw [show (fun x : ℝ ↦
      yoshidaEndpointEvenTailRepresenter centeredEvenP2 x *
        factorTwoCenteredP4 x) =
      fun x ↦ (yoshidaEndpointPotential x * centeredEvenP2 x *
          factorTwoCenteredP4 x +
        fixedProjectedShiftedRemainder2 x * factorTwoCenteredP4 x +
        (41 / 60 : ℝ) *
          (centeredEvenP2 x * factorTwoCenteredP4 x)) +
        fixedProjectionPolynomial 0 1 x * factorTwoCenteredP4 x by
    funext x
    unfold yoshidaEndpointEvenTailRepresenter fixedProjectedShiftedRemainder2
      fixedProjectedShiftedRemainder fixedProjectedBoundedRemainder
      fixedProjectionPolynomial fixedEvenLowProfile centeredEvenP0 centeredEvenP2
    ring,
    intervalIntegral.integral_add
      ((hV.add hshift).add (hP2P4.const_mul (41 / 60 : ℝ))) hproj,
    intervalIntegral.integral_add (hV.add hshift)
      (hP2P4.const_mul (41 / 60 : ℝ)),
    intervalIntegral.integral_add hV hshift,
    intervalIntegral.integral_const_mul,
    show (∫ x : ℝ in -1..1,
      centeredEvenP2 x * factorTwoCenteredP4 x) = 0 by
      simpa only [mul_comm] using integral_factorTwoCenteredP4_mul_centeredEvenP2,
    hprojZero,
    integral_endpointPotential_mul_centeredEvenP2_mul_P4]
  ring

/-! ## One global polynomial model -/

private def cleanP4RemainderPolynomial0 (x : ℝ) : ℝ :=
  -yoshidaEndpointA * regularRepresenterPolynomial6_0_explicit x +
    2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP0 *
      yoshidaEndpointCoshPolynomial6 x -
    (883 / 480 : ℝ) - (35 / 32 : ℝ) * x ^ 2

private def cleanP4RemainderPolynomial2 (x : ℝ) : ℝ :=
  -yoshidaEndpointA * regularRepresenterPolynomial6_2_explicit x +
    2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP2 *
      yoshidaEndpointCoshPolynomial6 x +
    (107 / 240 : ℝ) - (71 / 40 : ℝ) * x ^ 2

private theorem shiftedPolynomial0_eq
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    fixedProjectedShiftedRemainderPolynomial6_0 x =
      cleanP4RemainderPolynomial0 x := by
  unfold fixedProjectedShiftedRemainderPolynomial6_0
    fixedProjectedSmoothRemainderPolynomial6_0
    cleanP4RemainderPolynomial0
  rw [regularRepresenterPolynomial6_p0_eq hx]

private theorem shiftedPolynomial2_eq
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    fixedProjectedShiftedRemainderPolynomial6_2 x =
      cleanP4RemainderPolynomial2 x := by
  unfold fixedProjectedShiftedRemainderPolynomial6_2
    fixedProjectedSmoothRemainderPolynomial6_2
    cleanP4RemainderPolynomial2
  rw [regularRepresenterPolynomial6_p2_eq hx]

private theorem continuous_cleanP4RemainderPolynomial0 :
    Continuous cleanP4RemainderPolynomial0 := by
  unfold cleanP4RemainderPolynomial0 regularRepresenterPolynomial6_0_explicit
    yoshidaEndpointCoshPolynomial6 centeredEvenP0
  fun_prop

private theorem continuous_cleanP4RemainderPolynomial2 :
    Continuous cleanP4RemainderPolynomial2 := by
  unfold cleanP4RemainderPolynomial2 regularRepresenterPolynomial6_2_explicit
    yoshidaEndpointCoshPolynomial6 centeredEvenP2
  fun_prop

private theorem integral_pow_four_mul_P4 :
    (∫ x : ℝ in -1..1, x ^ 4 * factorTwoCenteredP4 x) = 16 / 315 := by
  unfold factorTwoCenteredP4
  ring_nf
  repeat' rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  norm_num

private theorem integral_sq_mul_P4 :
    (∫ x : ℝ in -1..1, x ^ 2 * factorTwoCenteredP4 x) = 0 := by
  unfold factorTwoCenteredP4
  ring_nf
  repeat' rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  norm_num

private theorem integral_pow_six_mul_P4 :
    (∫ x : ℝ in -1..1, x ^ 6 * factorTwoCenteredP4 x) = 16 / 231 := by
  unfold factorTwoCenteredP4
  ring_nf
  repeat' rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  norm_num

private theorem integral_pow_eight_mul_P4 :
    (∫ x : ℝ in -1..1, x ^ 8 * factorTwoCenteredP4 x) = 32 / 429 := by
  unfold factorTwoCenteredP4
  ring_nf
  repeat' rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  norm_num

/-- Exact degree-six model pairing for the constant clean cross. -/
def factorTwoIntrinsicP4CleanRemainderModel04 : ℝ :=
  (16 / 315 : ℝ) *
      (-(7 * yoshidaEndpointA ^ 4) / 23040 -
        5 * yoshidaEndpointA ^ 5 / 768 +
        155 * yoshidaEndpointA ^ 6 / 1935360 +
        610 * yoshidaEndpointA ^ 7 / 184320 +
        yoshidaEndpointCoshMoment centeredEvenP0 *
          yoshidaEndpointA ^ 5 / 192) +
    (16 / 231 : ℝ) *
      (31 * yoshidaEndpointA ^ 6 / 5806080 +
        122 * yoshidaEndpointA ^ 7 / 184320 +
        yoshidaEndpointCoshMoment centeredEvenP0 *
          yoshidaEndpointA ^ 7 / 23040)

/-- Exact degree-six model pairing for the degree-two clean cross. -/
def factorTwoIntrinsicP4CleanRemainderModel24 : ℝ :=
  (16 / 315 : ℝ) *
      (yoshidaEndpointA ^ 2 / 192 +
        7 * yoshidaEndpointA ^ 4 / 46080 +
        155 * yoshidaEndpointA ^ 6 / 7741440 +
        244 * yoshidaEndpointA ^ 7 / 184320 +
        yoshidaEndpointCoshMoment centeredEvenP2 *
          yoshidaEndpointA ^ 5 / 192) +
    (16 / 231 : ℝ) *
      (-(7 * yoshidaEndpointA ^ 4) / 230400 -
        31 * yoshidaEndpointA ^ 6 / 11612160 +
        yoshidaEndpointCoshMoment centeredEvenP2 *
          yoshidaEndpointA ^ 7 / 23040) +
    (32 / 429 : ℝ) *
      (31 * yoshidaEndpointA ^ 6 / 108380160)

theorem integral_cleanP4RemainderPolynomial0_mul_P4 :
    (∫ x : ℝ in -1..1,
      cleanP4RemainderPolynomial0 x * factorTwoCenteredP4 x) =
        factorTwoIntrinsicP4CleanRemainderModel04 := by
  unfold cleanP4RemainderPolynomial0
    regularRepresenterPolynomial6_0_explicit yoshidaEndpointCoshPolynomial6
  rw [show (fun x : ℝ ↦
      (-yoshidaEndpointA *
          (1 / 2 - yoshidaEndpointA / 48 * (1 + x ^ 2) -
            yoshidaEndpointA ^ 2 / 32 * (2 / 3 + 2 * x ^ 2) +
            7 * yoshidaEndpointA ^ 3 / 11520 *
              (1 / 2 + 3 * x ^ 2 + x ^ 4 / 2) +
            5 * yoshidaEndpointA ^ 4 / 1536 *
              (2 / 5 + 4 * x ^ 2 + 2 * x ^ 4) -
            31 * yoshidaEndpointA ^ 5 / 1935360 *
              (1 / 3 + 5 * x ^ 2 + 5 * x ^ 4 + x ^ 6 / 3) -
            61 * yoshidaEndpointA ^ 6 / 184320 *
              (2 / 7 + 6 * x ^ 2 + 10 * x ^ 4 + 2 * x ^ 6)) +
        2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP0 *
          (1 + yoshidaEndpointA ^ 2 * x ^ 2 / 8 +
            yoshidaEndpointA ^ 4 * x ^ 4 / 384 +
            yoshidaEndpointA ^ 6 * x ^ 6 / 46080) -
        883 / 480 - 35 / 32 * x ^ 2) * factorTwoCenteredP4 x) =
      fun x ↦
        (-yoshidaEndpointA / 2 - 883 / 480 +
            yoshidaEndpointA ^ 2 / 48 + yoshidaEndpointA ^ 3 / 48 -
            7 * yoshidaEndpointA ^ 4 / 23040 -
            yoshidaEndpointA ^ 5 / 768 +
            31 * yoshidaEndpointA ^ 6 / 5806080 +
            61 * yoshidaEndpointA ^ 7 / 645120 +
            2 * yoshidaEndpointA *
              yoshidaEndpointCoshMoment centeredEvenP0) *
              factorTwoCenteredP4 x +
          (yoshidaEndpointA ^ 2 / 48 + yoshidaEndpointA ^ 3 / 16 -
            7 * yoshidaEndpointA ^ 4 / 3840 -
            5 * yoshidaEndpointA ^ 5 / 384 +
            31 * yoshidaEndpointA ^ 6 / 387072 +
            61 * yoshidaEndpointA ^ 7 / 30720 - 35 / 32 +
            yoshidaEndpointA ^ 3 *
              yoshidaEndpointCoshMoment centeredEvenP0 / 4) *
              (x ^ 2 * factorTwoCenteredP4 x) +
          (-(7 * yoshidaEndpointA ^ 4) / 23040 -
            5 * yoshidaEndpointA ^ 5 / 768 +
            155 * yoshidaEndpointA ^ 6 / 1935360 +
            610 * yoshidaEndpointA ^ 7 / 184320 +
            yoshidaEndpointCoshMoment centeredEvenP0 *
              yoshidaEndpointA ^ 5 / 192) *
              (x ^ 4 * factorTwoCenteredP4 x) +
          (31 * yoshidaEndpointA ^ 6 / 5806080 +
            122 * yoshidaEndpointA ^ 7 / 184320 +
            yoshidaEndpointCoshMoment centeredEvenP0 *
              yoshidaEndpointA ^ 7 / 23040) *
              (x ^ 6 * factorTwoCenteredP4 x) by
    funext x
    ring]
  have h0 : IntervalIntegrable factorTwoCenteredP4 volume (-1) 1 :=
    continuous_factorTwoCenteredP4.intervalIntegrable (-1) 1
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ x ^ 2 * factorTwoCenteredP4 x) volume (-1) 1 :=
    ((continuous_id.pow 2).mul continuous_factorTwoCenteredP4)
      |>.intervalIntegrable (-1) 1
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ x ^ 4 * factorTwoCenteredP4 x) volume (-1) 1 :=
    ((continuous_id.pow 4).mul continuous_factorTwoCenteredP4)
      |>.intervalIntegrable (-1) 1
  have h6 : IntervalIntegrable
      (fun x : ℝ ↦ x ^ 6 * factorTwoCenteredP4 x) volume (-1) 1 :=
    ((continuous_id.pow 6).mul continuous_factorTwoCenteredP4)
      |>.intervalIntegrable (-1) 1
  rw [intervalIntegral.integral_add
      (((h0.const_mul _).add (h2.const_mul _)).add (h4.const_mul _))
      (h6.const_mul _),
    intervalIntegral.integral_add
      ((h0.const_mul _).add (h2.const_mul _)) (h4.const_mul _),
    intervalIntegral.integral_add (h0.const_mul _) (h2.const_mul _)]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_pow_four_mul_P4, integral_pow_six_mul_P4,
    integral_factorTwoCenteredP4]
  rw [integral_sq_mul_P4]
  unfold factorTwoIntrinsicP4CleanRemainderModel04
  ring

theorem integral_cleanP4RemainderPolynomial2_mul_P4 :
    (∫ x : ℝ in -1..1,
      cleanP4RemainderPolynomial2 x * factorTwoCenteredP4 x) =
        factorTwoIntrinsicP4CleanRemainderModel24 := by
  unfold cleanP4RemainderPolynomial2
    regularRepresenterPolynomial6_2_explicit yoshidaEndpointCoshPolynomial6
  rw [show (fun x : ℝ ↦
      (-yoshidaEndpointA *
          (-(yoshidaEndpointA / 48) * (1 - x ^ 2) ^ 2 / 4 -
            yoshidaEndpointA ^ 2 / 32 * (4 / 15) +
            7 * yoshidaEndpointA ^ 3 / 11520 *
              (1 / 4 + 3 * x ^ 2 / 4 - x ^ 4 / 4 + x ^ 6 / 20) +
            5 * yoshidaEndpointA ^ 4 / 1536 *
              (8 / 35 + 8 * x ^ 2 / 5) -
            31 * yoshidaEndpointA ^ 5 / 1935360 *
              (5 / 24 + 5 * x ^ 2 / 2 + 5 * x ^ 4 / 4 -
                x ^ 6 / 6 + x ^ 8 / 56) -
            61 * yoshidaEndpointA ^ 6 / 184320 *
              (4 / 21 + 24 * x ^ 2 / 7 + 4 * x ^ 4)) +
        2 * yoshidaEndpointA * yoshidaEndpointCoshMoment centeredEvenP2 *
          (1 + yoshidaEndpointA ^ 2 * x ^ 2 / 8 +
            yoshidaEndpointA ^ 4 * x ^ 4 / 384 +
            yoshidaEndpointA ^ 6 * x ^ 6 / 46080) +
        107 / 240 - 71 / 40 * x ^ 2) * factorTwoCenteredP4 x) =
      fun x ↦
        (107 / 240 + yoshidaEndpointA ^ 2 / 192 +
            yoshidaEndpointA ^ 3 / 120 -
            7 * yoshidaEndpointA ^ 4 / 46080 -
            yoshidaEndpointA ^ 5 / 1344 +
            31 * yoshidaEndpointA ^ 6 / 9289728 +
            61 * yoshidaEndpointA ^ 7 / 967680 +
            2 * yoshidaEndpointA *
              yoshidaEndpointCoshMoment centeredEvenP2) *
              factorTwoCenteredP4 x +
          (-(yoshidaEndpointA ^ 2) / 96 -
            7 * yoshidaEndpointA ^ 4 / 15360 -
            yoshidaEndpointA ^ 5 / 192 +
            31 * yoshidaEndpointA ^ 6 / 774144 +
            61 * yoshidaEndpointA ^ 7 / 53760 - 71 / 40 +
            yoshidaEndpointA ^ 3 *
              yoshidaEndpointCoshMoment centeredEvenP2 / 4) *
              (x ^ 2 * factorTwoCenteredP4 x) +
          (yoshidaEndpointA ^ 2 / 192 +
            7 * yoshidaEndpointA ^ 4 / 46080 +
            155 * yoshidaEndpointA ^ 6 / 7741440 +
            244 * yoshidaEndpointA ^ 7 / 184320 +
            yoshidaEndpointCoshMoment centeredEvenP2 *
              yoshidaEndpointA ^ 5 / 192) *
              (x ^ 4 * factorTwoCenteredP4 x) +
          (-(7 * yoshidaEndpointA ^ 4) / 230400 -
            31 * yoshidaEndpointA ^ 6 / 11612160 +
            yoshidaEndpointCoshMoment centeredEvenP2 *
              yoshidaEndpointA ^ 7 / 23040) *
              (x ^ 6 * factorTwoCenteredP4 x) +
          (31 * yoshidaEndpointA ^ 6 / 108380160) *
              (x ^ 8 * factorTwoCenteredP4 x) by
    funext x
    ring]
  have h0 : IntervalIntegrable factorTwoCenteredP4 volume (-1) 1 :=
    continuous_factorTwoCenteredP4.intervalIntegrable (-1) 1
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ x ^ 2 * factorTwoCenteredP4 x) volume (-1) 1 :=
    ((continuous_id.pow 2).mul continuous_factorTwoCenteredP4)
      |>.intervalIntegrable (-1) 1
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ x ^ 4 * factorTwoCenteredP4 x) volume (-1) 1 :=
    ((continuous_id.pow 4).mul continuous_factorTwoCenteredP4)
      |>.intervalIntegrable (-1) 1
  have h6 : IntervalIntegrable
      (fun x : ℝ ↦ x ^ 6 * factorTwoCenteredP4 x) volume (-1) 1 :=
    ((continuous_id.pow 6).mul continuous_factorTwoCenteredP4)
      |>.intervalIntegrable (-1) 1
  have h8 : IntervalIntegrable
      (fun x : ℝ ↦ x ^ 8 * factorTwoCenteredP4 x) volume (-1) 1 :=
    ((continuous_id.pow 8).mul continuous_factorTwoCenteredP4)
      |>.intervalIntegrable (-1) 1
  rw [intervalIntegral.integral_add
      ((((h0.const_mul _).add (h2.const_mul _)).add (h4.const_mul _)).add
        (h6.const_mul _)) (h8.const_mul _),
    intervalIntegral.integral_add
      (((h0.const_mul _).add (h2.const_mul _)).add (h4.const_mul _))
        (h6.const_mul _),
    intervalIntegral.integral_add
      ((h0.const_mul _).add (h2.const_mul _)) (h4.const_mul _),
    intervalIntegral.integral_add (h0.const_mul _) (h2.const_mul _)]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_pow_four_mul_P4, integral_pow_six_mul_P4,
    integral_pow_eight_mul_P4, integral_factorTwoCenteredP4]
  rw [integral_sq_mul_P4]
  unfold factorTwoIntrinsicP4CleanRemainderModel24
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
