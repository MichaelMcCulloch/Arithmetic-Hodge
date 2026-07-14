import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowPotential
import ArithmeticHodge.Analysis.YoshidaConstantBounds
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRemainderBound
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddLowEndpointPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddAffineKernelEstimate
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddSymmetricBound
import ArithmeticHodge.Analysis.YoshidaFactorTwoStructuralConstantBounds

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive

noncomputable section

open CenteredOddOneThreeEnergy
open CenteredEndpointCorrelation
open YoshidaEndpointEvenLowPotential
open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointOcticPotential
open YoshidaEndpointOcticTwoModeSchurData
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialExactLowMode
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicRemainderBound
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddLowEndpointPositive
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaFactorTwoPhaseOddLowSchur
open YoshidaFactorTwoPhaseOddStructuralPerturbation
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoStructuralConstantBounds
open YoshidaEndpointWeightedCauchy
open YoshidaRegularKernelSharpMeanZeroSchur
open YoshidaRegularKernelSchur
open YoshidaRegularKernelBound

/-!
# Structural positivity of the intrinsic odd endpoint block

The logarithmic endpoint potential is evaluated on the complete
`P₁/P₃` block.  The only non-rational entry which survives in its Gram
matrix is the common diagonal `log 2` mass; it cancels the corresponding
part of the sharp odd mass loss.  The perturbation is then kept as its exact
correlation-polynomial functional.
-/

/-! ## The missing degree-six potential moment -/

private theorem integral_sixth_mul_log_one_sub :
    (∫ x : ℝ in 0..1, x ^ 6 * Real.log (1 - x)) = -363 / 980 := by
  let g : ℝ → ℝ := fun y ↦ (1 - y) ^ 6 * Real.log y
  calc
    (∫ x : ℝ in 0..1, x ^ 6 * Real.log (1 - x)) =
        ∫ x : ℝ in 0..1, g (1 - x) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [g]
      ring
    _ = ∫ x : ℝ in 0..1, g x := by
      simpa only [sub_self, sub_zero] using
        (intervalIntegral.integral_comp_sub_left (f := g)
          (a := (0 : ℝ)) (b := 1) 1)
    _ = ∫ x : ℝ in 0..1,
        x ^ 6 * Real.log x - 6 * (x ^ 5 * Real.log x) +
          15 * (x ^ 4 * Real.log x) - 20 * (x ^ 3 * Real.log x) +
          15 * (x ^ 2 * Real.log x) - 6 * (x ^ 1 * Real.log x) +
          x ^ 0 * Real.log x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [g]
      ring
    _ = (∫ x : ℝ in 0..1, x ^ 6 * Real.log x) -
          6 * (∫ x : ℝ in 0..1, x ^ 5 * Real.log x) +
          15 * (∫ x : ℝ in 0..1, x ^ 4 * Real.log x) -
          20 * (∫ x : ℝ in 0..1, x ^ 3 * Real.log x) +
          15 * (∫ x : ℝ in 0..1, x ^ 2 * Real.log x) -
          6 * (∫ x : ℝ in 0..1, x ^ 1 * Real.log x) +
          ∫ x : ℝ in 0..1, x ^ 0 * Real.log x := by
      have hJ (n : ℕ) : IntervalIntegrable
          (fun x : ℝ ↦ x ^ n * Real.log x) volume 0 1 :=
        intervalIntegral.intervalIntegrable_log'.continuousOn_mul
          (continuous_pow n).continuousOn
      rw [intervalIntegral.integral_add
          (((((hJ 6).sub ((hJ 5).const_mul 6)).add
            ((hJ 4).const_mul 15)).sub ((hJ 3).const_mul 20)).add
            ((hJ 2).const_mul 15) |>.sub ((hJ 1).const_mul 6)) (hJ 0),
        intervalIntegral.integral_sub
          ((((hJ 6).sub ((hJ 5).const_mul 6)).add
            ((hJ 4).const_mul 15)).sub ((hJ 3).const_mul 20) |>.add
            ((hJ 2).const_mul 15)) ((hJ 1).const_mul 6),
        intervalIntegral.integral_add
          (((hJ 6).sub ((hJ 5).const_mul 6)).add
            ((hJ 4).const_mul 15) |>.sub ((hJ 3).const_mul 20))
            ((hJ 2).const_mul 15),
        intervalIntegral.integral_sub
          ((hJ 6).sub ((hJ 5).const_mul 6) |>.add
            ((hJ 4).const_mul 15)) ((hJ 3).const_mul 20),
        intervalIntegral.integral_add
          ((hJ 6).sub ((hJ 5).const_mul 6)) ((hJ 4).const_mul 15),
        intervalIntegral.integral_sub (hJ 6) ((hJ 5).const_mul 6)]
      repeat rw [intervalIntegral.integral_const_mul]
    _ = -363 / 980 := by
      repeat rw [integral_pow_mul_log_zero_one]
      norm_num

private theorem integral_sixth_mul_log_one_add :
    (∫ x : ℝ in 0..1, x ^ 6 * Real.log (1 + x)) =
      (2 / 7 : ℝ) * Real.log 2 - 319 / 2940 := by
  let F : ℝ → ℝ := fun x ↦
    x ^ 7 / 7 * Real.log (1 + x) - x ^ 7 / 49 + x ^ 6 / 42 -
      x ^ 5 / 35 + x ^ 4 / 28 - x ^ 3 / 21 + x ^ 2 / 14 -
      x / 7 + Real.log (1 + x) / 7
  have hderiv (x : ℝ) (hx : 1 + x ≠ 0) :
      HasDerivAt F (x ^ 6 * Real.log (1 + x)) x := by
    have hone : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 x := by
      simpa using (hasDerivAt_const x 1).add (hasDerivAt_id x)
    have hlog : HasDerivAt (fun y : ℝ ↦ Real.log (1 + y))
        ((1 + x)⁻¹) x := by
      simpa only [Function.comp_apply, mul_one] using
        (Real.hasDerivAt_log hx).comp x hone
    dsimp only [F]
    convert (((hasDerivAt_id x).pow 7).div_const 7 |>.mul hlog)
      |>.sub (((hasDerivAt_id x).pow 7).div_const 49)
      |>.add (((hasDerivAt_id x).pow 6).div_const 42)
      |>.sub (((hasDerivAt_id x).pow 5).div_const 35)
      |>.add (((hasDerivAt_id x).pow 4).div_const 28)
      |>.sub (((hasDerivAt_id x).pow 3).div_const 21)
      |>.add (((hasDerivAt_id x).pow 2).div_const 14)
      |>.sub ((hasDerivAt_id x).div_const 7)
      |>.add (hlog.div_const 7) using 1
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat]
    field_simp [hx]
    ring
  have hcont : ContinuousOn (fun x : ℝ ↦ x ^ 6 * Real.log (1 + x))
      (uIcc (0 : ℝ) 1) := by
    intro x hx
    have hxu : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hxne : 1 + x ≠ 0 := by linarith [hxu.1]
    have hlog : ContinuousAt (fun y : ℝ ↦ Real.log (1 + y)) x := by
      exact ((Real.hasDerivAt_log hxne).comp x
        (by simpa using
          (hasDerivAt_const x 1).add (hasDerivAt_id x))).continuousAt
    exact ((continuousAt_id.pow 6).mul hlog).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ hderiv x (by
      have hxu : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      linarith [hxu.1])) hcont.intervalIntegrable
  rw [hint]
  dsimp only [F]
  norm_num
  ring

private theorem intervalIntegrable_sixth_mul_log_one_sub :
    IntervalIntegrable (fun x : ℝ ↦ x ^ 6 * Real.log (1 - x))
      volume 0 1 := by
  let g : ℝ → ℝ := fun y ↦ (1 - y) ^ 6 * Real.log y
  have hg : IntervalIntegrable g volume 0 1 := by
    have hbase : IntervalIntegrable
        (fun y : ℝ ↦ (1 - y) ^ 6 * Real.log y) volume 0 1 :=
      (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1))
        |>.continuousOn_mul
          ((continuous_const.sub continuous_id).pow 6).continuousOn
    simpa only [g] using hbase
  have hreflect : IntervalIntegrable (fun x : ℝ ↦ g (1 - x))
      volume 0 1 := by
    simpa only [sub_self, sub_zero] using (hg.comp_sub_left 1).symm
  apply hreflect.congr
  intro x _hx
  dsimp only [g]
  ring

private theorem intervalIntegrable_sixth_mul_log_one_add :
    IntervalIntegrable (fun x : ℝ ↦ x ^ 6 * Real.log (1 + x))
      volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hxu : x ∈ Icc (0 : ℝ) 1 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  have hxne : 1 + x ≠ 0 := by linarith [hxu.1]
  have hlog : ContinuousAt (fun y : ℝ ↦ Real.log (1 + y)) x := by
    exact ((Real.hasDerivAt_log hxne).comp x
      (by simpa using
        (hasDerivAt_const x 1).add (hasDerivAt_id x))).continuousAt
  exact ((continuousAt_id.pow 6).mul hlog).continuousWithinAt

/-- Exact sixth moment of the endpoint potential. -/
theorem integral_endpointPotential_mul_pow_six :
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * x ^ 6) =
      352 / 735 - (2 / 7 : ℝ) * Real.log 2 := by
  let q : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * x ^ 6
  have hqEven : Function.Even q := by
    intro x
    dsimp only [q, yoshidaEndpointPotential]
    congr 1
    · congr 3
      ring
    · ring
  let r : ℝ → ℝ := fun x ↦ -(1 / 2 : ℝ) *
    (x ^ 6 * Real.log (1 - x) + x ^ 6 * Real.log (1 + x))
  have hpoint : ∀ᵐ x : ℝ ∂volume, q x = r x := by
    filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-1 : ℝ)] with x hx1 hxneg1
    have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    have hadd : 1 + x ≠ 0 := by
      intro h
      apply hxneg1
      linarith
    dsimp only [q, r, yoshidaEndpointPotential]
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
      Real.log_mul hsub hadd]
    ring
  have hrRight : IntervalIntegrable r volume 0 1 := by
    have hsum := intervalIntegrable_sixth_mul_log_one_sub.add
      intervalIntegrable_sixth_mul_log_one_add
    have hscaled := hsum.const_mul (-(1 / 2 : ℝ))
    simpa only [r] using hscaled
  have hqRight : IntervalIntegrable q volume 0 1 := by
    have hrev : r =ᵐ[volume] q := by
      filter_upwards [hpoint] with x hx
      exact hx.symm
    apply hrRight.congr_ae
    exact hrev.filter_mono (ae_mono Measure.restrict_le_self)
  have hqLeft : IntervalIntegrable q volume (-1) 0 := by
    have hneg : IntervalIntegrable (fun x : ℝ ↦ q (-x)) volume (-1) 0 := by
      simpa only [zero_sub, sub_zero] using (hqRight.comp_sub_left 0).symm
    apply hneg.congr
    intro x _hx
    exact hqEven x
  have hfold : (∫ x : ℝ in -1..1, q x) =
      2 * ∫ x : ℝ in 0..1, q x := by
    have hreflect : (∫ x : ℝ in 0..1, q (-x)) =
        ∫ x : ℝ in -1..0, q x := by
      simpa only [neg_zero] using
        (intervalIntegral.integral_comp_neg
          (f := q) (a := (0 : ℝ)) (b := 1))
    calc
      (∫ x : ℝ in -1..1, q x) =
          (∫ x : ℝ in -1..0, q x) + ∫ x : ℝ in 0..1, q x :=
        (intervalIntegral.integral_add_adjacent_intervals hqLeft hqRight).symm
      _ = (∫ x : ℝ in 0..1, q x) + ∫ x : ℝ in 0..1, q x := by
        congr 1
        rw [← hreflect]
        apply intervalIntegral.integral_congr
        intro x _hx
        exact hqEven x
      _ = _ := by ring
  rw [show (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * x ^ 6) =
      ∫ x : ℝ in -1..1, q x by rfl, hfold]
  have hsplit : (∫ x : ℝ in 0..1, q x) =
      -(1 / 2 : ℝ) *
        ((∫ x : ℝ in 0..1, x ^ 6 * Real.log (1 - x)) +
          ∫ x : ℝ in 0..1, x ^ 6 * Real.log (1 + x)) := by
    calc
      (∫ x : ℝ in 0..1, q x) =
          ∫ x : ℝ in 0..1,
            -(1 / 2 : ℝ) *
              (x ^ 6 * Real.log (1 - x) +
                x ^ 6 * Real.log (1 + x)) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hpoint] with x hx _hxI
        simpa only [r] using hx
      _ = -(1 / 2 : ℝ) *
          ∫ x : ℝ in 0..1,
            (x ^ 6 * Real.log (1 - x) +
              x ^ 6 * Real.log (1 + x)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by
        rw [intervalIntegral.integral_add
          intervalIntegrable_sixth_mul_log_one_sub
          intervalIntegrable_sixth_mul_log_one_add]
  rw [hsplit, integral_sixth_mul_log_one_sub,
    integral_sixth_mul_log_one_add]
  ring

private theorem intervalIntegrable_endpointPotential_mul_pow_two :
    IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 :=
  intervalIntegrable_endpointPotential_mul_sq (fun x : ℝ ↦ x) continuous_id

private theorem intervalIntegrable_endpointPotential_mul_pow_four :
    IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 := by
  have h := intervalIntegrable_endpointPotential_mul_sq
    (fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2)
  apply h.congr
  intro x _hx
  ring

private theorem intervalIntegrable_endpointPotential_mul_pow_six :
    IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 6) volume (-1) 1 := by
  have h := intervalIntegrable_endpointPotential_mul_sq
    (fun x : ℝ ↦ x ^ 3) (continuous_id.pow 3)
  apply h.congr
  intro x _hx
  ring

/-- Exact endpoint-potential cross entry of the two intrinsic odd modes. -/
theorem integral_endpointPotential_mul_p1_mul_p3 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredP1 x * centeredP3 x) = 1 / 5 := by
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredP1 x * centeredP3 x) =
      fun x ↦ (5 / 2 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) -
        (3 / 2 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) by
    funext x
    unfold centeredP1 centeredP3
    ring,
    intervalIntegral.integral_sub
      (intervalIntegrable_endpointPotential_mul_pow_four.const_mul (5 / 2 : ℝ))
      (intervalIntegrable_endpointPotential_mul_pow_two.const_mul (3 / 2 : ℝ)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq]
  ring

/-- Exact endpoint-potential diagonal of the centered degree-three mode. -/
theorem integral_endpointPotential_mul_p3_sq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredP3 x ^ 2) =
      289 / 735 - (2 / 7 : ℝ) * Real.log 2 := by
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredP3 x ^ 2) =
      fun x ↦
        ((25 / 4 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) -
          (15 / 2 : ℝ) * (yoshidaEndpointPotential x * x ^ 4)) +
          (9 / 4 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) by
    funext x
    unfold centeredP3
    ring,
    intervalIntegral.integral_add
      ((intervalIntegrable_endpointPotential_mul_pow_six.const_mul (25 / 4 : ℝ)).sub
        (intervalIntegrable_endpointPotential_mul_pow_four.const_mul (15 / 2 : ℝ)))
      (intervalIntegrable_endpointPotential_mul_pow_two.const_mul (9 / 4 : ℝ)),
    intervalIntegral.integral_sub
      (intervalIntegrable_endpointPotential_mul_pow_six.const_mul (25 / 4 : ℝ))
      (intervalIntegrable_endpointPotential_mul_pow_four.const_mul (15 / 2 : ℝ)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq]
  ring

/-- Exact full logarithmic-potential Gram on `span(P₁,P₃)`. -/
theorem integral_endpointPotential_oddStructuralLow
    (c d : ℝ) :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x *
        factorTwoOddStructuralLowProfile c d x ^ 2) =
      (8 / 9 - (2 / 3 : ℝ) * Real.log 2) * c ^ 2 +
        2 * (1 / 5 : ℝ) * c * d +
        (289 / 735 - (2 / 7 : ℝ) * Real.log 2) * d ^ 2 := by
  have h11 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * centeredP1 x ^ 2)
      volume (-1) 1 := by
    simpa only [centeredP1] using
      intervalIntegrable_endpointPotential_mul_pow_two
  have h13 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * centeredP1 x * centeredP3 x)
      volume (-1) 1 := by
    rw [show (fun x : ℝ ↦
        yoshidaEndpointPotential x * centeredP1 x * centeredP3 x) =
      fun x ↦ (5 / 2 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) -
        (3 / 2 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) by
      funext x
      unfold centeredP1 centeredP3
      ring]
    exact (intervalIntegrable_endpointPotential_mul_pow_four.const_mul _).sub
      (intervalIntegrable_endpointPotential_mul_pow_two.const_mul _)
  have h33 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * centeredP3 x ^ 2)
      volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq centeredP3
      (by unfold centeredP3; fun_prop)
  rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x *
      factorTwoOddStructuralLowProfile c d x ^ 2) =
      fun x ↦ c ^ 2 *
          (yoshidaEndpointPotential x * centeredP1 x ^ 2) +
        (2 * c * d) *
          (yoshidaEndpointPotential x * centeredP1 x * centeredP3 x) +
        d ^ 2 *
          (yoshidaEndpointPotential x * centeredP3 x ^ 2) by
    funext x
    unfold factorTwoOddStructuralLowProfile
    ring]
  rw [intervalIntegral.integral_add
      ((h11.const_mul (c ^ 2)).add (h13.const_mul (2 * c * d)))
      (h33.const_mul (d ^ 2)),
    intervalIntegral.integral_add
      (h11.const_mul (c ^ 2)) (h13.const_mul (2 * c * d))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [show (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredP1 x ^ 2) =
      8 / 9 - (2 / 3 : ℝ) * Real.log 2 by
        simpa only [centeredP1] using integral_endpointPotential_mul_sq,
    integral_endpointPotential_mul_p1_mul_p3,
    integral_endpointPotential_mul_p3_sq]
  ring

/-! ## A rational clean Gram reserve -/

private theorem integral_oddStructuralLow_sq (c d : ℝ) :
    (∫ x : ℝ in -1..1,
      factorTwoOddStructuralLowProfile c d x ^ 2) =
      (2 / 3 : ℝ) * c ^ 2 + (2 / 7 : ℝ) * d ^ 2 := by
  have h11 : IntervalIntegrable (fun x : ℝ ↦ centeredP1 x ^ 2)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredP1
    fun_prop
  have h13 : IntervalIntegrable
      (fun x : ℝ ↦ centeredP1 x * centeredP3 x) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredP1 centeredP3
    fun_prop
  have h33 : IntervalIntegrable (fun x : ℝ ↦ centeredP3 x ^ 2)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredP3
    fun_prop
  rw [show (fun x : ℝ ↦ factorTwoOddStructuralLowProfile c d x ^ 2) =
      fun x ↦ c ^ 2 * centeredP1 x ^ 2 +
        (2 * c * d) * (centeredP1 x * centeredP3 x) +
        d ^ 2 * centeredP3 x ^ 2 by
    funext x
    unfold factorTwoOddStructuralLowProfile
    ring,
    intervalIntegral.integral_add
      ((h11.const_mul (c ^ 2)).add (h13.const_mul (2 * c * d)))
      (h33.const_mul (d ^ 2)),
    intervalIntegral.integral_add
      (h11.const_mul (c ^ 2)) (h13.const_mul (2 * c * d))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_centeredP1_sq, integral_centeredP1_mul_p3,
    integral_centeredP3_sq]
  ring

/-- The four independent analytic constant bounds fit below one small
rational number.  This is a series/monotonicity estimate, not a decimal
evaluation. -/
theorem oddLow_totalMassLoss_lt_five_hundred_nineteen_div_two_hundred_fifty :
    Real.eulerMascheroniConstant + Real.log (Real.pi * Real.log 2) +
        Real.log 2 / 64 + 1 / Real.sqrt 2 < (519 / 250 : ℝ) := by
  have hgamma :=
    eulerMascheroniConstant_lt_two_hundred_eighty_nine_div_five_hundred
  have hrenorm :=
    log_pi_mul_log_two_lt_seven_hundred_seventy_nine_div_thousand
  have hlog :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred
  have hsqrt :=
    inv_sqrt_two_lt_one_hundred_seventy_seven_div_two_hundred_fifty
  linarith

/-- Exact full-potential coercivity leaves this rational positive Gram on
the intrinsic odd block.  Both the regular kernel and the hyperbolic rank
are controlled structurally, while the `P₁/P₃` orientation is retained. -/
theorem oddStructuralLow_clean_rationalGram_le
    (c d : ℝ) :
    (193 / 1125 : ℝ) * c ^ 2 + 2 * (1 / 5 : ℝ) * c * d +
        (5951 / 18375 : ℝ) * d ^ 2 ≤
      yoshidaEndpointOddCleanQuadratic
        (factorTwoOddStructuralLowProfile c d) := by
  let w : ℝ → ℝ := factorTwoOddStructuralLowProfile c d
  let E : ℝ := (2 / 3 : ℝ) * c ^ 2 + (2 / 7 : ℝ) * d ^ 2
  let T : ℝ := Real.eulerMascheroniConstant +
    Real.log (Real.pi * Real.log 2) + Real.log 2 / 64 +
      1 / Real.sqrt 2
  have hw : Continuous w := continuous_factorTwoOddStructuralLowProfile c d
  have hodd : Function.Odd w := odd_factorTwoOddStructuralLowProfile c d
  have hmass : (∫ x : ℝ in -1..1, w x ^ 2) = E := by
    dsimp only [w, E]
    exact integral_oddStructuralLow_sq c d
  have hmean : (∫ x : ℝ in -1..1, w x) = 0 :=
    centered_interval_integral_eq_zero_of_odd w hodd
  have hregular :=
    endpoint_mul_regularQuadratic_re_le_log_two_div_sixty_four_energy
      w hw hmean
  change yoshidaEndpointA *
      (yoshidaEndpointRegularQuadratic (fun x ↦ (w x : ℂ))).re ≤
    (Real.log 2 / 64) * (∫ x : ℝ in -1..1, w x ^ 2) at hregular
  rw [hmass] at hregular
  have hhyper := yoshidaEndpointHyperbolicQuadratic_lower
    (fun x ↦ (w x : ℂ)) (by fun_prop)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hhyper
  rw [hmass] at hhyper
  have hraw := centeredRawLogEnergy_factorTwoOddStructuralLowProfile c d
  have hpotential := integral_endpointPotential_oddStructuralLow c d
  have hT :=
    oddLow_totalMassLoss_lt_five_hundred_nineteen_div_two_hundred_fifty
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hscaledT : T * E ≤ (519 / 250 : ℝ) * E :=
    mul_le_mul_of_nonneg_right hT.le hE
  dsimp only [T] at hscaledT
  unfold yoshidaEndpointOddCleanQuadratic yoshidaEndpointScalarMassLoss
  rw [hraw, hpotential, hmass]
  dsimp only [E, w] at hregular hhyper hscaledT
  dsimp only [E]
  ring_nf at hregular hhyper hscaledT ⊢
  linarith

/-! ## Exact correlation moments for the regular/pole split -/

/-- The exact `P₁/P₁` centered correlation polynomial. -/
def oddStructuralCorrelation11 (t : ℝ) : ℝ :=
  (t - 2) * (t ^ 2 + 2 * t - 2) / 6

/-- The exact polarized `P₁/P₃` centered correlation polynomial. -/
def oddStructuralCorrelation13 (t : ℝ) : ℝ :=
  t * (t - 2) * (t ^ 3 + 2 * t ^ 2 - 8 * t + 4) / 8

/-- The exact `P₃/P₃` centered correlation polynomial. -/
def oddStructuralCorrelation33 (t : ℝ) : ℝ :=
  (t - 2) *
    (5 * t ^ 6 + 10 * t ^ 5 - 22 * t ^ 4 - 44 * t ^ 3 +
      24 * t ^ 2 + 48 * t - 16) / 112

/-- The quadratic part of the regular scalar kernel which survives against
the zero-moment correlation block. -/
def oddStructuralRegularQuadratic (t : ℝ) : ℝ :=
  79 / 60 + (3 / 125 : ℝ) * t ^ 2

/-- The sole analytic kernel estimate needed below.  It is a uniform
quadratic approximation to the nonsingular regular kernel itself; the two
Cauchy poles are kept exact and are not included in this assertion. -/
def OddStructuralRegularKernelControl : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 2,
    |yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
      oddStructuralRegularQuadratic t| ≤ 1 / 500

/-- The pole-free global Taylor envelope supplies the required kernel
control on the whole overlap interval. -/
theorem oddStructuralRegularKernelControl :
    OddStructuralRegularKernelControl := by
  intro t ht
  simpa only [oddStructuralRegularQuadratic] using
    abs_yoshidaEndpointA_mul_factorTwoCenteredSymmetricRegularWeight_sub_quadratic_le
      ht.1 ht.2

/-- The signed residual of the regular scalar kernel after subtracting its
quadratic structural approximation. -/
def oddStructuralRegularError (C : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ in 0..2,
    (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
      oddStructuralRegularQuadratic t) * C t

private theorem measurable_yoshidaRegularKernel :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

private theorem measurable_factorTwoCenteredSymmetricRegularWeight :
    Measurable factorTwoCenteredSymmetricRegularWeight := by
  unfold factorTwoCenteredSymmetricRegularWeight
  exact (((measurable_const.mul
      (Real.measurable_cosh.comp (by fun_prop))).add
        (measurable_const.mul
          (Real.measurable_cosh.comp (by fun_prop)))).sub
      (measurable_yoshidaRegularKernel.comp (by fun_prop))).sub
        (measurable_yoshidaRegularKernel.comp (by fun_prop))

private theorem intervalIntegrable_oddStructuralRegularError_of_control
    (hcontrol : OddStructuralRegularKernelControl)
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦
        (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          oddStructuralRegularQuadratic t) * C t) volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
      oddStructuralRegularQuadratic t) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 500 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact ((measurable_const.mul
      measurable_factorTwoCenteredSymmetricRegularWeight).sub
        (by unfold oddStructuralRegularQuadratic; fun_prop)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1.le, ht.2⟩
    have hk := hcontrol t htIcc
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

/-- Uniform kernel control turns directly into an `L¹` error bound. -/
theorem abs_oddStructuralRegularError_le
    (hcontrol : OddStructuralRegularKernelControl)
    (C : ℝ → ℝ) (hC : Continuous C) :
    |oddStructuralRegularError C| ≤
      (1 / 500 : ℝ) * (∫ t : ℝ in 0..2, |C t|) := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
      oddStructuralRegularQuadratic t) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 500 : ℝ) * |C t|
  have hf : IntervalIntegrable f volume 0 2 := by
    dsimp only [f]
    exact intervalIntegrable_oddStructuralRegularError_of_control
      hcontrol C hC
  have hg : IntervalIntegrable g volume 0 2 := by
    dsimp only [g]
    exact (hC.abs.const_mul (1 / 500 : ℝ)).intervalIntegrable 0 2
  have hmono : (∫ t : ℝ in 0..2, |f t|) ≤ ∫ t : ℝ in 0..2, g t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf.abs hg
    intro t ht
    have hk := hcontrol t ht
    dsimp only [f, g]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  calc
    |oddStructuralRegularError C| = |∫ t : ℝ in 0..2, f t| := by
      rfl
    _ ≤ ∫ t : ℝ in 0..2, |f t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t : ℝ in 0..2, g t := hmono
    _ = (1 / 500 : ℝ) * (∫ t : ℝ in 0..2, |C t|) := by
      rw [intervalIntegral.integral_const_mul]

private theorem integral_nonic
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
        (a₃ * x ^ 3 + (a₄ * x ^ 4 + (a₅ * x ^ 5 +
          (a₆ * x ^ 6 + (a₇ * x ^ 7 +
            (a₈ * x ^ 8 + a₉ * x ^ 9))))))))) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 +
        a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 +
        a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 +
        a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 +
        a₉ * (r ^ 10 - l ^ 10) / 10 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem integral_decic
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
        (a₃ * x ^ 3 + (a₄ * x ^ 4 + (a₅ * x ^ 5 +
          (a₆ * x ^ 6 + (a₇ * x ^ 7 + (a₈ * x ^ 8 +
            (a₉ * x ^ 9 + a₁₀ * x ^ 10)))))))))) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 +
        a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 +
        a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 +
        a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 +
        a₉ * (r ^ 10 - l ^ 10) / 10 +
        a₁₀ * (r ^ 11 - l ^ 11) / 11 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-- All three correlation entries have zero scalar moment.  This is the
orthogonality which removes the constant part of the regular kernel. -/
theorem integral_oddStructuralCorrelations :
    (∫ t : ℝ in 0..2, oddStructuralCorrelation11 t) = 0 ∧
      (∫ t : ℝ in 0..2, oddStructuralCorrelation13 t) = 0 ∧
      (∫ t : ℝ in 0..2, oddStructuralCorrelation33 t) = 0 := by
  constructor
  · rw [show oddStructuralCorrelation11 = fun t : ℝ ↦
        (2 / 3 : ℝ) * t ^ 0 + ((-1 : ℝ) * t ^ 1 +
          (0 * t ^ 2 + ((1 / 6 : ℝ) * t ^ 3 +
            (0 * t ^ 4 + (0 * t ^ 5 + (0 * t ^ 6 +
              (0 * t ^ 7 + (0 * t ^ 8 + 0 * t ^ 9)))))))) by
      funext t
      unfold oddStructuralCorrelation11
      ring,
      integral_nonic]
    norm_num
  · constructor
    · rw [show oddStructuralCorrelation13 = fun t : ℝ ↦
          0 * t ^ 0 + ((-1 : ℝ) * t ^ 1 +
            ((5 / 2 : ℝ) * t ^ 2 + ((-3 / 2 : ℝ) * t ^ 3 +
              (0 * t ^ 4 + ((1 / 8 : ℝ) * t ^ 5 +
                (0 * t ^ 6 + (0 * t ^ 7 +
                  (0 * t ^ 8 + 0 * t ^ 9)))))))) by
        funext t
        unfold oddStructuralCorrelation13
        ring,
        integral_nonic]
      norm_num
    · rw [show oddStructuralCorrelation33 = fun t : ℝ ↦
          (2 / 7 : ℝ) * t ^ 0 + ((-1 : ℝ) * t ^ 1 +
            (0 * t ^ 2 + (1 * t ^ 3 + (0 * t ^ 4 +
              ((-3 / 8 : ℝ) * t ^ 5 + (0 * t ^ 6 +
                ((5 / 112 : ℝ) * t ^ 7 +
                  (0 * t ^ 8 + 0 * t ^ 9)))))))) by
        funext t
        unfold oddStructuralCorrelation33
        ring,
        integral_nonic]
      norm_num

/-- Only the `P₁/P₁` entry has a nonzero quadratic moment. -/
theorem integral_sq_mul_oddStructuralCorrelations :
    (∫ t : ℝ in 0..2, t ^ 2 * oddStructuralCorrelation11 t) = -4 / 9 ∧
      (∫ t : ℝ in 0..2, t ^ 2 * oddStructuralCorrelation13 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 2 * oddStructuralCorrelation33 t) = 0 := by
  constructor
  · rw [show (fun t : ℝ ↦ t ^ 2 * oddStructuralCorrelation11 t) =
        fun t ↦ 0 * t ^ 0 + (0 * t ^ 1 +
          ((2 / 3 : ℝ) * t ^ 2 + ((-1 : ℝ) * t ^ 3 +
            (0 * t ^ 4 + ((1 / 6 : ℝ) * t ^ 5 +
              (0 * t ^ 6 + (0 * t ^ 7 +
                (0 * t ^ 8 + 0 * t ^ 9)))))))) by
      funext t
      unfold oddStructuralCorrelation11
      ring,
      integral_nonic]
    norm_num
  · constructor
    · rw [show (fun t : ℝ ↦ t ^ 2 * oddStructuralCorrelation13 t) =
          fun t ↦ 0 * t ^ 0 + (0 * t ^ 1 + (0 * t ^ 2 +
            ((-1 : ℝ) * t ^ 3 + ((5 / 2 : ℝ) * t ^ 4 +
              ((-3 / 2 : ℝ) * t ^ 5 + (0 * t ^ 6 +
                ((1 / 8 : ℝ) * t ^ 7 +
                  (0 * t ^ 8 + 0 * t ^ 9)))))))) by
        funext t
        unfold oddStructuralCorrelation13
        ring,
        integral_nonic]
      norm_num
    · rw [show (fun t : ℝ ↦ t ^ 2 * oddStructuralCorrelation33 t) =
          fun t ↦ 0 * t ^ 0 + (0 * t ^ 1 +
            ((2 / 7 : ℝ) * t ^ 2 + ((-1 : ℝ) * t ^ 3 +
              (0 * t ^ 4 + (1 * t ^ 5 + (0 * t ^ 6 +
                ((-3 / 8 : ℝ) * t ^ 7 + (0 * t ^ 8 +
                  (5 / 112 : ℝ) * t ^ 9)))))))) by
        funext t
        unfold oddStructuralCorrelation33
        ring,
        integral_nonic]
      norm_num

/-- The quadratic regular approximation contributes exactly `-4/375` on
the first diagonal and vanishes on the other two entries. -/
theorem integral_regularQuadratic_mul_oddStructuralCorrelations :
    (∫ t : ℝ in 0..2,
        oddStructuralRegularQuadratic t * oddStructuralCorrelation11 t) =
        -4 / 375 ∧
      (∫ t : ℝ in 0..2,
        oddStructuralRegularQuadratic t * oddStructuralCorrelation13 t) = 0 ∧
      (∫ t : ℝ in 0..2,
        oddStructuralRegularQuadratic t * oddStructuralCorrelation33 t) = 0 := by
  have hcont (C : ℝ → ℝ) (hC : Continuous C) :
      IntervalIntegrable C volume 0 2 := hC.intervalIntegrable 0 2
  have h11c : Continuous oddStructuralCorrelation11 := by
    unfold oddStructuralCorrelation11
    fun_prop
  have h13c : Continuous oddStructuralCorrelation13 := by
    unfold oddStructuralCorrelation13
    fun_prop
  have h33c : Continuous oddStructuralCorrelation33 := by
    unfold oddStructuralCorrelation33
    fun_prop
  rw [show (fun t : ℝ ↦
      oddStructuralRegularQuadratic t * oddStructuralCorrelation11 t) =
      fun t ↦ (79 / 60 : ℝ) * oddStructuralCorrelation11 t +
        (3 / 125 : ℝ) *
          (t ^ 2 * oddStructuralCorrelation11 t) by
    funext t
    unfold oddStructuralRegularQuadratic
    ring,
    intervalIntegral.integral_add
      (hcont _ h11c |>.const_mul (79 / 60 : ℝ))
      (hcont _ (by fun_prop) |>.const_mul (3 / 125 : ℝ)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_oddStructuralCorrelations.1,
    integral_sq_mul_oddStructuralCorrelations.1]
  constructor
  · ring
  · constructor
    · rw [show (fun t : ℝ ↦
          oddStructuralRegularQuadratic t * oddStructuralCorrelation13 t) =
          fun t ↦ (79 / 60 : ℝ) * oddStructuralCorrelation13 t +
            (3 / 125 : ℝ) *
              (t ^ 2 * oddStructuralCorrelation13 t) by
        funext t
        unfold oddStructuralRegularQuadratic
        ring,
        intervalIntegral.integral_add
          (hcont _ h13c |>.const_mul (79 / 60 : ℝ))
          (hcont _ (by fun_prop) |>.const_mul (3 / 125 : ℝ)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        integral_oddStructuralCorrelations.2.1,
        integral_sq_mul_oddStructuralCorrelations.2.1]
      ring
    · rw [show (fun t : ℝ ↦
          oddStructuralRegularQuadratic t * oddStructuralCorrelation33 t) =
          fun t ↦ (79 / 60 : ℝ) * oddStructuralCorrelation33 t +
            (3 / 125 : ℝ) *
              (t ^ 2 * oddStructuralCorrelation33 t) by
        funext t
        unfold oddStructuralRegularQuadratic
        ring,
        intervalIntegral.integral_add
          (hcont _ h33c |>.const_mul (79 / 60 : ℝ))
          (hcont _ (by fun_prop) |>.const_mul (3 / 125 : ℝ)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        integral_oddStructuralCorrelations.2.2,
        integral_sq_mul_oddStructuralCorrelations.2.2]
      ring

/-- The diagonal correlation polynomials have their sharp autocorrelation
`L¹` budgets. -/
theorem integral_abs_oddStructuralCorrelation11_le :
    (∫ t : ℝ in 0..2, |oddStructuralCorrelation11 t|) ≤ 2 / 3 := by
  have h := integral_abs_centeredEndpointCorrelation_le_energy centeredP1
    (by unfold centeredP1; fun_prop)
  have hpoint (t : ℝ) :
      centeredEndpointCorrelation centeredP1 t =
        oddStructuralCorrelation11 t := by
    rw [← factorTwoCenteredCorrelationBilinear_self,
      factorTwoCenteredCorrelationBilinear_p1_p1]
    rfl
  simp_rw [hpoint] at h
  rw [integral_centeredP1_sq] at h
  exact h

theorem integral_abs_oddStructuralCorrelation33_le :
    (∫ t : ℝ in 0..2, |oddStructuralCorrelation33 t|) ≤ 2 / 7 := by
  have h := integral_abs_centeredEndpointCorrelation_le_energy centeredP3
    (by unfold centeredP3; fun_prop)
  have hpoint (t : ℝ) :
      centeredEndpointCorrelation centeredP3 t =
        oddStructuralCorrelation33 t := by
    rw [← factorTwoCenteredCorrelationBilinear_self,
      factorTwoCenteredCorrelationBilinear_p3_p3]
    rfl
  simp_rw [hpoint] at h
  rw [integral_centeredP3_sq] at h
  exact h

/-- Consequently the two diagonal regular residuals have tiny rational
budgets, with no sign discarded elsewhere in the formula. -/
theorem abs_oddStructuralRegularError11_le
    (hcontrol : OddStructuralRegularKernelControl) :
    |oddStructuralRegularError oddStructuralCorrelation11| ≤ 1 / 375 := by
  have herr := abs_oddStructuralRegularError_le hcontrol
    oddStructuralCorrelation11 (by unfold oddStructuralCorrelation11; fun_prop)
  have hcorr := integral_abs_oddStructuralCorrelation11_le
  nlinarith

theorem abs_oddStructuralRegularError33_le
    (hcontrol : OddStructuralRegularKernelControl) :
    |oddStructuralRegularError oddStructuralCorrelation33| ≤ 1 / 875 := by
  have herr := abs_oddStructuralRegularError_le hcontrol
    oddStructuralCorrelation33 (by unfold oddStructuralCorrelation33; fun_prop)
  have hcorr := integral_abs_oddStructuralCorrelation33_le
  nlinarith

private theorem sq_intervalIntegral_mul_le_zero_two
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ x : ℝ in 0..2, f x * g x) ^ 2 ≤
      (∫ x : ℝ in 0..2, f x ^ 2) *
        (∫ x : ℝ in 0..2, g x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 2)
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have hgMeas : AEStronglyMeasurable g μ :=
    hg.aestronglyMeasurable.restrict
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (0 : ℝ) 2) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hgLp : MemLp g 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hgMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖g x‖ ^ 2)
        (Icc (0 : ℝ) 2) :=
      (hg.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have h := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1) f g
    (by simp) (by simpa using hfLp) (by simpa using hgLp)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa only [μ, div_one, one_mul] using h

private theorem integral_oddStructuralCorrelation13_sq :
    (∫ t : ℝ in 0..2, oddStructuralCorrelation13 t ^ 2) = 16 / 1155 := by
  rw [show (fun t : ℝ ↦ oddStructuralCorrelation13 t ^ 2) = fun t ↦
      0 * t ^ 0 + (0 * t ^ 1 + (1 * t ^ 2 + ((-5 : ℝ) * t ^ 3 +
        ((37 / 4 : ℝ) * t ^ 4 + ((-15 / 2 : ℝ) * t ^ 5 +
          (2 * t ^ 6 + ((5 / 8 : ℝ) * t ^ 7 +
            ((-3 / 8 : ℝ) * t ^ 8 + (0 * t ^ 9 +
              (1 / 64 : ℝ) * t ^ 10))))))))) by
    funext t
    unfold oddStructuralCorrelation13
    ring,
    integral_decic]
  norm_num

/-- Cauchy--Schwarz is already sharp enough for the off-diagonal residual:
the exact squared correlation mass lies just below the `1/6` threshold. -/
theorem integral_abs_oddStructuralCorrelation13_lt :
    (∫ t : ℝ in 0..2, |oddStructuralCorrelation13 t|) < 1 / 6 := by
  have hcs := sq_intervalIntegral_mul_le_zero_two
    (fun _ : ℝ ↦ 1) (fun t ↦ |oddStructuralCorrelation13 t|)
    continuous_const (by unfold oddStructuralCorrelation13; fun_prop)
  simp only [one_mul, one_pow, sq_abs] at hcs
  rw [show (∫ _t : ℝ in 0..2, (1 : ℝ)) = 2 by norm_num,
    integral_oddStructuralCorrelation13_sq] at hcs
  have hnonneg : 0 ≤ ∫ t : ℝ in 0..2,
      |oddStructuralCorrelation13 t| :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ abs_nonneg _)
  have hrat : (2 : ℝ) * (16 / 1155) < (1 / 6 : ℝ) ^ 2 := by
    norm_num
  nlinarith

theorem abs_oddStructuralRegularError13_lt :
    |oddStructuralRegularError oddStructuralCorrelation13| < 1 / 3000 := by
  have herr := abs_oddStructuralRegularError_le
    oddStructuralRegularKernelControl oddStructuralCorrelation13
      (by unfold oddStructuralCorrelation13; fun_prop)
  have hcorr := integral_abs_oddStructuralCorrelation13_lt
  nlinarith

/-- The two explicit Cauchy poles in the centered symmetric weight. -/
def oddStructuralPoleWeight (t : ℝ) : ℝ :=
  -1 / (2 * (2 + t)) - 1 / (2 * (2 - t))

private theorem integral_inv_two_add :
    (∫ t : ℝ in 0..2, 1 / (2 + t)) = Real.log 2 := by
  let F : ℝ → ℝ := fun t ↦ Real.log (2 + t)
  have hderiv (t : ℝ) (ht : 2 + t ≠ 0) :
      HasDerivAt F (1 / (2 + t)) t := by
    have hadd : HasDerivAt (fun x : ℝ ↦ 2 + x) 1 t := by
      simpa using (hasDerivAt_const t 2).add (hasDerivAt_id t)
    simpa only [F, Function.comp_apply, one_div, mul_one] using
      (Real.hasDerivAt_log ht).comp t hadd
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / (2 + t))
      (uIcc (0 : ℝ) 2) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 2 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have hne : 2 + t ≠ 0 := by linarith [ht'.1]
    exact (continuousAt_const.div
      (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hderiv t (by
      have ht' : t ∈ Icc (0 : ℝ) 2 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
      linarith [ht'.1])) hcont.intervalIntegrable
  rw [hint]
  dsimp only [F]
  norm_num
  rw [show Real.log 4 = 2 * Real.log 2 by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
    ring]
  ring

private theorem intervalIntegrable_inv_two_add :
    IntervalIntegrable (fun t : ℝ ↦ 1 / (2 + t)) volume 0 2 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have hne : 2 + t ≠ 0 := by linarith [ht'.1]
  exact (continuousAt_const.div
    (continuousAt_const.add continuousAt_id) hne).continuousWithinAt

private theorem endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles
    (C : ℝ → ℝ) :
    yoshidaEndpointA *
        (∫ t : ℝ in 0..2,
          factorTwoSymmetricWeight (yoshidaEndpointA * t) * C t) =
      ∫ t : ℝ in 0..2,
        (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
          oddStructuralPoleWeight t) * C t := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [
      (Set.countable_singleton (2 : ℝ)).ae_notMem
        (volume.restrict (Set.uIoc (0 : ℝ) 2)),
      ae_restrict_mem measurableSet_uIoc] with t ht2 ht
  have ht' : t ∈ Set.Ioc (0 : ℝ) 2 := by
    simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have htne : t ≠ 2 := by simpa using ht2
  have htlt : t < 2 := lt_of_le_of_ne ht'.2 htne
  calc
    yoshidaEndpointA *
        (factorTwoSymmetricWeight (yoshidaEndpointA * t) * C t) =
      (yoshidaEndpointA *
        factorTwoSymmetricWeight (yoshidaEndpointA * t)) * C t := by ring
    _ = _ := by
      rw [yoshidaEndpointA_mul_factorTwoSymmetricWeight_eq_regular_poles
        ht'.1 htlt]
      unfold oddStructuralPoleWeight
      ring

private theorem intervalIntegrable_poleWeight_mul_correlation11 :
    IntervalIntegrable
      (fun t ↦ oddStructuralPoleWeight t * oddStructuralCorrelation11 t)
      volume 0 2 := by
  have hbase : IntervalIntegrable
      (fun t : ℝ ↦ t / 3 - (2 / 3 : ℝ) * (1 / (2 + t)))
      volume 0 2 :=
    ((by fun_prop : Continuous (fun t : ℝ ↦ t / 3)).intervalIntegrable 0 2).sub
      (intervalIntegrable_inv_two_add.const_mul (2 / 3 : ℝ))
  apply hbase.congr_ae
  filter_upwards [
    (MeasureTheory.Measure.ae_ne volume (2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self),
    (MeasureTheory.Measure.ae_ne volume (-2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)] with t ht2 htneg2
  have hp : 2 + t ≠ 0 := by
    intro h
    apply htneg2
    linarith
  have hm : 2 - t ≠ 0 := by
    intro h
    apply ht2
    linarith
  unfold oddStructuralPoleWeight oddStructuralCorrelation11
  field_simp [hp, hm]
  ring

private theorem intervalIntegrable_poleWeight_mul_correlation13 :
    IntervalIntegrable
      (fun t ↦ oddStructuralPoleWeight t * oddStructuralCorrelation13 t)
      volume 0 2 := by
  have hbase : IntervalIntegrable
      (fun t : ℝ ↦ (5 - 2 * t + t ^ 3 / 4) - 10 * (1 / (2 + t)))
      volume 0 2 :=
    ((by fun_prop : Continuous
        (fun t : ℝ ↦ 5 - 2 * t + t ^ 3 / 4)).intervalIntegrable 0 2).sub
      (intervalIntegrable_inv_two_add.const_mul 10)
  apply hbase.congr_ae
  filter_upwards [
    (MeasureTheory.Measure.ae_ne volume (2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self),
    (MeasureTheory.Measure.ae_ne volume (-2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)] with t ht2 htneg2
  have hp : 2 + t ≠ 0 := by
    intro h
    apply htneg2
    linarith
  have hm : 2 - t ≠ 0 := by
    intro h
    apply ht2
    linarith
  unfold oddStructuralPoleWeight oddStructuralCorrelation13
  field_simp [hp, hm]
  ring

private theorem intervalIntegrable_poleWeight_mul_correlation33 :
    IntervalIntegrable
      (fun t ↦ oddStructuralPoleWeight t * oddStructuralCorrelation33 t)
      volume 0 2 := by
  have hbase : IntervalIntegrable
      (fun t : ℝ ↦
        ((3 / 7 : ℝ) * t - (11 / 28 : ℝ) * t ^ 3 +
          (5 / 56 : ℝ) * t ^ 5) - (2 / 7 : ℝ) * (1 / (2 + t)))
      volume 0 2 :=
    ((by fun_prop : Continuous (fun t : ℝ ↦
        (3 / 7 : ℝ) * t - (11 / 28 : ℝ) * t ^ 3 +
          (5 / 56 : ℝ) * t ^ 5)).intervalIntegrable 0 2).sub
      (intervalIntegrable_inv_two_add.const_mul (2 / 7 : ℝ))
  apply hbase.congr_ae
  filter_upwards [
    (MeasureTheory.Measure.ae_ne volume (2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self),
    (MeasureTheory.Measure.ae_ne volume (-2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)] with t ht2 htneg2
  have hp : 2 + t ≠ 0 := by
    intro h
    apply htneg2
    linarith
  have hm : 2 - t ≠ 0 := by
    intro h
    apply ht2
    linarith
  unfold oddStructuralPoleWeight oddStructuralCorrelation33
  field_simp [hp, hm]
  ring

/-- Exact contribution of both explicit endpoint poles to the three
correlation entries.  The apparent singularity at `t = 2` is removable
because every correlation has the factor `t - 2`; the proof discards only
that singleton and then performs polynomial division. -/
theorem integral_poleWeight_mul_oddStructuralCorrelations :
    (∫ t : ℝ in 0..2,
        oddStructuralPoleWeight t * oddStructuralCorrelation11 t) =
        2 / 3 - (2 / 3 : ℝ) * Real.log 2 ∧
      (∫ t : ℝ in 0..2,
        oddStructuralPoleWeight t * oddStructuralCorrelation13 t) =
        7 - 10 * Real.log 2 ∧
      (∫ t : ℝ in 0..2,
        oddStructuralPoleWeight t * oddStructuralCorrelation33 t) =
        5 / 21 - (2 / 7 : ℝ) * Real.log 2 := by
  have h11 : (∫ t : ℝ in 0..2,
      oddStructuralPoleWeight t * oddStructuralCorrelation11 t) =
      ∫ t : ℝ in 0..2, t / 3 - (2 / 3 : ℝ) / (2 + t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by
      intro h
      apply htneg2
      linarith
    have hm : 2 - t ≠ 0 := by
      intro h
      apply ht2
      linarith
    unfold oddStructuralPoleWeight oddStructuralCorrelation11
    field_simp [hp, hm]
    ring
  have h13 : (∫ t : ℝ in 0..2,
      oddStructuralPoleWeight t * oddStructuralCorrelation13 t) =
      ∫ t : ℝ in 0..2,
        (5 - 2 * t + t ^ 3 / 4) - 10 / (2 + t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by
      intro h
      apply htneg2
      linarith
    have hm : 2 - t ≠ 0 := by
      intro h
      apply ht2
      linarith
    unfold oddStructuralPoleWeight oddStructuralCorrelation13
    field_simp [hp, hm]
    ring
  have h33 : (∫ t : ℝ in 0..2,
      oddStructuralPoleWeight t * oddStructuralCorrelation33 t) =
      ∫ t : ℝ in 0..2,
        ((3 / 7 : ℝ) * t - (11 / 28 : ℝ) * t ^ 3 +
          (5 / 56 : ℝ) * t ^ 5) - (2 / 7 : ℝ) / (2 + t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by
      intro h
      apply htneg2
      linarith
    have hm : 2 - t ≠ 0 := by
      intro h
      apply ht2
      linarith
    unfold oddStructuralPoleWeight oddStructuralCorrelation33
    field_simp [hp, hm]
    ring
  rw [h11, h13, h33]
  have hinv : IntervalIntegrable (fun t : ℝ ↦ 1 / (2 + t))
      volume 0 2 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 2 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have hne : 2 + t ≠ 0 := by linarith [ht'.1]
    exact (continuousAt_const.div
      (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hpoly (f : ℝ → ℝ) (hf : Continuous f) :
      IntervalIntegrable f volume 0 2 := hf.intervalIntegrable 0 2
  have hpoly11 : (∫ t : ℝ in 0..2, t / 3) = 2 / 3 := by
    rw [show (fun t : ℝ ↦ t / 3) = fun t ↦
        0 * t ^ 0 + ((1 / 3 : ℝ) * t ^ 1 + (0 * t ^ 2 +
          (0 * t ^ 3 + (0 * t ^ 4 + (0 * t ^ 5 +
            (0 * t ^ 6 + (0 * t ^ 7 + (0 * t ^ 8 + 0 * t ^ 9)))))))) by
      funext t
      ring,
      integral_nonic]
    norm_num
  have hpoly13 :
      (∫ t : ℝ in 0..2, 5 - 2 * t + t ^ 3 / 4) = 7 := by
    rw [show (fun t : ℝ ↦ 5 - 2 * t + t ^ 3 / 4) = fun t ↦
        5 * t ^ 0 + ((-2 : ℝ) * t ^ 1 + (0 * t ^ 2 +
          ((1 / 4 : ℝ) * t ^ 3 + (0 * t ^ 4 + (0 * t ^ 5 +
            (0 * t ^ 6 + (0 * t ^ 7 + (0 * t ^ 8 + 0 * t ^ 9)))))))) by
      funext t
      ring,
      integral_nonic]
    norm_num
  have hpoly33 : (∫ t : ℝ in 0..2,
      (3 / 7 : ℝ) * t - (11 / 28 : ℝ) * t ^ 3 +
        (5 / 56 : ℝ) * t ^ 5) = 5 / 21 := by
    rw [show (fun t : ℝ ↦
        (3 / 7 : ℝ) * t - (11 / 28 : ℝ) * t ^ 3 +
          (5 / 56 : ℝ) * t ^ 5) = fun t ↦
        0 * t ^ 0 + ((3 / 7 : ℝ) * t ^ 1 + (0 * t ^ 2 +
          ((-11 / 28 : ℝ) * t ^ 3 + (0 * t ^ 4 +
            ((5 / 56 : ℝ) * t ^ 5 + (0 * t ^ 6 +
              (0 * t ^ 7 + (0 * t ^ 8 + 0 * t ^ 9)))))))) by
      funext t
      ring,
      integral_nonic]
    norm_num
  constructor
  · rw [show (fun t : ℝ ↦ t / 3 - (2 / 3 : ℝ) / (2 + t)) =
        fun t ↦ t / 3 - (2 / 3 : ℝ) * (1 / (2 + t)) by
      funext t
      ring,
      intervalIntegral.integral_sub
        (hpoly _ (by fun_prop)) (hinv.const_mul (2 / 3 : ℝ)),
      intervalIntegral.integral_const_mul,
      integral_inv_two_add, hpoly11]
  · constructor
    · rw [show (fun t : ℝ ↦
          (5 - 2 * t + t ^ 3 / 4) - 10 / (2 + t)) =
          fun t ↦ (5 - 2 * t + t ^ 3 / 4) - 10 * (1 / (2 + t)) by
        funext t
        ring,
        intervalIntegral.integral_sub
          (hpoly _ (by fun_prop)) (hinv.const_mul 10),
        intervalIntegral.integral_const_mul,
        integral_inv_two_add, hpoly13]
    · rw [show (fun t : ℝ ↦
          ((3 / 7 : ℝ) * t - (11 / 28 : ℝ) * t ^ 3 +
            (5 / 56 : ℝ) * t ^ 5) - (2 / 7 : ℝ) / (2 + t)) =
          fun t ↦
            ((3 / 7 : ℝ) * t - (11 / 28 : ℝ) * t ^ 3 +
              (5 / 56 : ℝ) * t ^ 5) -
                (2 / 7 : ℝ) * (1 / (2 + t)) by
        funext t
        ring,
        intervalIntegral.integral_sub
          (hpoly _ (by fun_prop)) (hinv.const_mul (2 / 7 : ℝ)),
        intervalIntegral.integral_const_mul,
        integral_inv_two_add, hpoly33]

private theorem integral_regular_poles_correlation11_eq :
    (∫ t : ℝ in 0..2,
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        oddStructuralPoleWeight t) * oddStructuralCorrelation11 t) =
      oddStructuralRegularError oddStructuralCorrelation11 - 4 / 375 +
        (2 / 3 - (2 / 3 : ℝ) * Real.log 2) := by
  have herr := intervalIntegrable_oddStructuralRegularError_of_control
    oddStructuralRegularKernelControl oddStructuralCorrelation11
      (by unfold oddStructuralCorrelation11; fun_prop)
  have hquad : IntervalIntegrable
      (fun t ↦ oddStructuralRegularQuadratic t *
        oddStructuralCorrelation11 t) volume 0 2 := by
    exact (by
      unfold oddStructuralRegularQuadratic oddStructuralCorrelation11
      fun_prop : Continuous (fun t ↦ oddStructuralRegularQuadratic t *
        oddStructuralCorrelation11 t)).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        oddStructuralPoleWeight t) * oddStructuralCorrelation11 t) =
      fun t ↦
        ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          oddStructuralRegularQuadratic t) * oddStructuralCorrelation11 t +
          oddStructuralRegularQuadratic t * oddStructuralCorrelation11 t) +
        oddStructuralPoleWeight t * oddStructuralCorrelation11 t by
    funext t
    ring,
    intervalIntegral.integral_add (herr.add hquad)
      intervalIntegrable_poleWeight_mul_correlation11,
    intervalIntegral.integral_add herr hquad,
    integral_regularQuadratic_mul_oddStructuralCorrelations.1,
    integral_poleWeight_mul_oddStructuralCorrelations.1]
  unfold oddStructuralRegularError
  ring

private theorem integral_regular_poles_correlation13_eq :
    (∫ t : ℝ in 0..2,
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        oddStructuralPoleWeight t) * oddStructuralCorrelation13 t) =
      oddStructuralRegularError oddStructuralCorrelation13 +
        (7 - 10 * Real.log 2) := by
  have herr := intervalIntegrable_oddStructuralRegularError_of_control
    oddStructuralRegularKernelControl oddStructuralCorrelation13
      (by unfold oddStructuralCorrelation13; fun_prop)
  have hquad : IntervalIntegrable
      (fun t ↦ oddStructuralRegularQuadratic t *
        oddStructuralCorrelation13 t) volume 0 2 := by
    exact (by
      unfold oddStructuralRegularQuadratic oddStructuralCorrelation13
      fun_prop : Continuous (fun t ↦ oddStructuralRegularQuadratic t *
        oddStructuralCorrelation13 t)).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        oddStructuralPoleWeight t) * oddStructuralCorrelation13 t) =
      fun t ↦
        ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          oddStructuralRegularQuadratic t) * oddStructuralCorrelation13 t +
          oddStructuralRegularQuadratic t * oddStructuralCorrelation13 t) +
        oddStructuralPoleWeight t * oddStructuralCorrelation13 t by
    funext t
    ring,
    intervalIntegral.integral_add (herr.add hquad)
      intervalIntegrable_poleWeight_mul_correlation13,
    intervalIntegral.integral_add herr hquad,
    integral_regularQuadratic_mul_oddStructuralCorrelations.2.1,
    integral_poleWeight_mul_oddStructuralCorrelations.2.1]
  unfold oddStructuralRegularError
  ring

private theorem integral_regular_poles_correlation33_eq :
    (∫ t : ℝ in 0..2,
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        oddStructuralPoleWeight t) * oddStructuralCorrelation33 t) =
      oddStructuralRegularError oddStructuralCorrelation33 +
        (5 / 21 - (2 / 7 : ℝ) * Real.log 2) := by
  have herr := intervalIntegrable_oddStructuralRegularError_of_control
    oddStructuralRegularKernelControl oddStructuralCorrelation33
      (by unfold oddStructuralCorrelation33; fun_prop)
  have hquad : IntervalIntegrable
      (fun t ↦ oddStructuralRegularQuadratic t *
        oddStructuralCorrelation33 t) volume 0 2 := by
    exact (by
      unfold oddStructuralRegularQuadratic oddStructuralCorrelation33
      fun_prop : Continuous (fun t ↦ oddStructuralRegularQuadratic t *
        oddStructuralCorrelation33 t)).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        oddStructuralPoleWeight t) * oddStructuralCorrelation33 t) =
      fun t ↦
        ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          oddStructuralRegularQuadratic t) * oddStructuralCorrelation33 t +
          oddStructuralRegularQuadratic t * oddStructuralCorrelation33 t) +
        oddStructuralPoleWeight t * oddStructuralCorrelation33 t by
    funext t
    ring,
    intervalIntegral.integral_add (herr.add hquad)
      intervalIntegrable_poleWeight_mul_correlation33,
    intervalIntegral.integral_add herr hquad,
    integral_regularQuadratic_mul_oddStructuralCorrelations.2.2,
    integral_poleWeight_mul_oddStructuralCorrelations.2.2]
  unfold oddStructuralRegularError
  ring

/-- Exact sign-preserving perturbation entries after the regular kernel,
both Cauchy poles, and both retained prime atoms have been separated. -/
theorem factorTwoCenteredSymmetricPerturbation_p1_structural_eq :
    factorTwoCenteredSymmetricPerturbation centeredP1 =
      oddStructuralRegularError oddStructuralCorrelation11 - 4 / 375 +
        (2 / 3 - (2 / 3 : ℝ) * Real.log 2) -
        (Real.log 2 / Real.sqrt 2) * (2 / 3) -
        (Real.log 3 / Real.sqrt 3) * oddStructuralCorrelation11
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  rw [factorTwoCenteredSymmetricPerturbation_p1_eq]
  rw [show (fun t : ℝ ↦
      factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        ((t - 2) * (t ^ 2 + 2 * t - 2) / 6)) =
      fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        oddStructuralCorrelation11 t by
    funext t
    rfl,
    endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles,
    integral_regular_poles_correlation11_eq]
  unfold oddStructuralCorrelation11
  ring

theorem factorTwoCenteredSymmetricPerturbationBilinear_p1_p3_structural_eq :
    factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3 =
      oddStructuralRegularError oddStructuralCorrelation13 +
        (7 - 10 * Real.log 2) -
        (Real.log 3 / Real.sqrt 3) * oddStructuralCorrelation13
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  rw [factorTwoCenteredSymmetricPerturbationBilinear_p1_p3_eq]
  rw [show (fun t : ℝ ↦
      factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        (t * (t - 2) * (t ^ 3 + 2 * t ^ 2 - 8 * t + 4) / 8)) =
      fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        oddStructuralCorrelation13 t by
    funext t
    rfl,
    endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles,
    integral_regular_poles_correlation13_eq]
  unfold oddStructuralCorrelation13
  ring

theorem factorTwoCenteredSymmetricPerturbation_p3_structural_eq :
    factorTwoCenteredSymmetricPerturbation centeredP3 =
      oddStructuralRegularError oddStructuralCorrelation33 +
        (5 / 21 - (2 / 7 : ℝ) * Real.log 2) -
        (Real.log 2 / Real.sqrt 2) * (2 / 7) -
        (Real.log 3 / Real.sqrt 3) * oddStructuralCorrelation33
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  rw [factorTwoCenteredSymmetricPerturbation_p3_eq]
  rw [show (fun t : ℝ ↦
      factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        ((t - 2) *
          (5 * t ^ 6 + 10 * t ^ 5 - 22 * t ^ 4 - 44 * t ^ 3 +
            24 * t ^ 2 + 48 * t - 16) / 112)) =
      fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        oddStructuralCorrelation33 t by
    funext t
    rfl,
    endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles,
    integral_regular_poles_correlation33_eq]
  unfold oddStructuralCorrelation33
  ring

/-! ## Analytic constants and the retained prime lag -/

private theorem strict_log_three_halves_bounds :
    (4054 / 10000 : ℝ) < Real.log (3 / 2) ∧
      Real.log (3 / 2) < (4055 / 10000 : ℝ) := by
  have h := strict_log_three_halves_fine_bounds
  constructor <;> linarith

private theorem log_two_div_sqrt_two_bounds :
    (49 / 100 : ℝ) < Real.log 2 / Real.sqrt 2 ∧
      Real.log 2 / Real.sqrt 2 < (491 / 1000 : ℝ) := by
  exact factorTwoDyadicWeight_bounds

private theorem log_three_div_sqrt_three_bounds :
    (634 / 1000 : ℝ) < Real.log 3 / Real.sqrt 3 ∧
      Real.log 3 / Real.sqrt 3 < (635 / 1000 : ℝ) := by
  have htwo := strict_log_two_bounds
  have hshift := strict_log_three_halves_bounds
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsupper : Real.sqrt 3 < (17321 / 10000 : ℝ) := by
    nlinarith
  have hslower : (433 / 250 : ℝ) < Real.sqrt 3 := by
    nlinarith
  have hlog : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    calc
      Real.log 3 = Real.log (2 * (3 / 2 : ℝ)) := by norm_num
      _ = Real.log 2 + Real.log (3 / 2) :=
        Real.log_mul (by norm_num) (by norm_num)
  constructor
  · rw [lt_div_iff₀ hspos, hlog]
    nlinarith [htwo.1, hshift.1]
  · rw [div_lt_iff₀ hspos, hlog]
    nlinarith [htwo.2, hshift.2]

private theorem factorTwoPrimeShift_div_endpointA_bounds :
    (1169 / 1000 : ℝ) < factorTwoPrimeShift / yoshidaEndpointA ∧
      factorTwoPrimeShift / yoshidaEndpointA < (1171 / 1000 : ℝ) := by
  have h := factorTwoPrimeLag_bounds
  constructor <;> linarith

private theorem hasDerivAt_oddStructuralCorrelation11 (x : ℝ) :
    HasDerivAt oddStructuralCorrelation11 (-1 + x ^ 2 / 2) x := by
  rw [show oddStructuralCorrelation11 = fun t : ℝ ↦
      2 / 3 - t + t ^ 3 / 6 by
    funext t
    unfold oddStructuralCorrelation11
    ring]
  convert (((hasDerivAt_const x (2 / 3 : ℝ)).sub (hasDerivAt_id x)).add
    (((hasDerivAt_id x).pow 3).div_const 6)) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem hasDerivAt_oddStructuralCorrelation13 (x : ℝ) :
    HasDerivAt oddStructuralCorrelation13
      (-1 + 5 * x - (9 / 2) * x ^ 2 + (5 / 8) * x ^ 4) x := by
  rw [show oddStructuralCorrelation13 = fun t : ℝ ↦
      -t + (5 / 2) * t ^ 2 - (3 / 2) * t ^ 3 + (1 / 8) * t ^ 5 by
    funext t
    unfold oddStructuralCorrelation13
    ring]
  convert ((((hasDerivAt_id x).neg.add
      (((hasDerivAt_id x).pow 2).const_mul (5 / 2))).sub
    (((hasDerivAt_id x).pow 3).const_mul (3 / 2))).add
      (((hasDerivAt_id x).pow 5).const_mul (1 / 8))) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem hasDerivAt_oddStructuralCorrelation33 (x : ℝ) :
    HasDerivAt oddStructuralCorrelation33
      (-1 + 3 * x ^ 2 - (15 / 8) * x ^ 4 + (5 / 16) * x ^ 6) x := by
  rw [show oddStructuralCorrelation33 = fun t : ℝ ↦
      2 / 7 - t + t ^ 3 - (3 / 8) * t ^ 5 + (5 / 112) * t ^ 7 by
    funext t
    unfold oddStructuralCorrelation33
    ring]
  convert (((((hasDerivAt_const x (2 / 7 : ℝ)).sub
      (hasDerivAt_id x)).add ((hasDerivAt_id x).pow 3)).sub
    (((hasDerivAt_id x).pow 5).const_mul (3 / 8))).add
      (((hasDerivAt_id x).pow 7).const_mul (5 / 112))) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem oddStructuralCorrelation11_strictAntiOn :
    StrictAntiOn oddStructuralCorrelation11
      (Icc (1169 / 1000 : ℝ) (1171 / 1000)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (by unfold oddStructuralCorrelation11; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_oddStructuralCorrelation11 x).deriv]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx2 := pow_lt_pow_left₀ hx.2 hx0 (by norm_num : (2 : ℕ) ≠ 0)
  norm_num at hx2 ⊢
  nlinarith

private theorem oddStructuralCorrelation13_strictAntiOn :
    StrictAntiOn oddStructuralCorrelation13
      (Icc (1169 / 1000 : ℝ) (1171 / 1000)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (by unfold oddStructuralCorrelation13; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_oddStructuralCorrelation13 x).deriv]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx2lo := pow_lt_pow_left₀ hx.1 (by norm_num : (0 : ℝ) ≤ 1169 / 1000)
    (by norm_num : (2 : ℕ) ≠ 0)
  have hx4hi := pow_lt_pow_left₀ hx.2 hx0 (by norm_num : (4 : ℕ) ≠ 0)
  norm_num at hx2lo hx4hi ⊢
  nlinarith

private theorem oddStructuralCorrelation33_strictMonoOn :
    StrictMonoOn oddStructuralCorrelation33
      (Icc (1169 / 1000 : ℝ) (1171 / 1000)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (by unfold oddStructuralCorrelation33; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_oddStructuralCorrelation33 x).deriv]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx2lo := pow_lt_pow_left₀ hx.1 (by norm_num : (0 : ℝ) ≤ 1169 / 1000)
    (by norm_num : (2 : ℕ) ≠ 0)
  have hx4hi := pow_lt_pow_left₀ hx.2 hx0 (by norm_num : (4 : ℕ) ≠ 0)
  have hx6lo := pow_lt_pow_left₀ hx.1 (by norm_num : (0 : ℝ) ≤ 1169 / 1000)
    (by norm_num : (6 : ℕ) ≠ 0)
  norm_num at hx2lo hx4hi hx6lo ⊢
  nlinarith

private theorem oddStructuralPrimeCorrelation_bounds :
    (-237 / 1000 : ℝ) < oddStructuralCorrelation11
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      oddStructuralCorrelation11
        (factorTwoPrimeShift / yoshidaEndpointA) < (-236 / 1000 : ℝ) ∧
    (123 / 1000 : ℝ) < oddStructuralCorrelation13
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      oddStructuralCorrelation13
        (factorTwoPrimeShift / yoshidaEndpointA) < (125 / 1000 : ℝ) ∧
    (28 / 1000 : ℝ) < oddStructuralCorrelation33
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      oddStructuralCorrelation33
        (factorTwoPrimeShift / yoshidaEndpointA) < (30 / 1000 : ℝ) := by
  let τ : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  have hτ := factorTwoPrimeShift_div_endpointA_bounds
  have hlo : (1169 / 1000 : ℝ) ∈
      Icc (1169 / 1000 : ℝ) (1171 / 1000) := by norm_num
  have hhi : (1171 / 1000 : ℝ) ∈
      Icc (1169 / 1000 : ℝ) (1171 / 1000) := by norm_num
  have hτmem : τ ∈ Icc (1169 / 1000 : ℝ) (1171 / 1000) :=
    ⟨hτ.1.le, hτ.2.le⟩
  have h11lo := oddStructuralCorrelation11_strictAntiOn hτmem hhi hτ.2
  have h11hi := oddStructuralCorrelation11_strictAntiOn hlo hτmem hτ.1
  have h13lo := oddStructuralCorrelation13_strictAntiOn hτmem hhi hτ.2
  have h13hi := oddStructuralCorrelation13_strictAntiOn hlo hτmem hτ.1
  have h33lo := oddStructuralCorrelation33_strictMonoOn hlo hτmem hτ.1
  have h33hi := oddStructuralCorrelation33_strictMonoOn hτmem hhi hτ.2
  dsimp only [τ] at h11lo h11hi h13lo h13hi h33lo h33hi ⊢
  constructor
  · calc
      (-237 / 1000 : ℝ) < oddStructuralCorrelation11 (1171 / 1000) := by
        norm_num [oddStructuralCorrelation11]
      _ < oddStructuralCorrelation11
          (factorTwoPrimeShift / yoshidaEndpointA) := h11lo
  · constructor
    · calc
        oddStructuralCorrelation11
            (factorTwoPrimeShift / yoshidaEndpointA) <
          oddStructuralCorrelation11 (1169 / 1000) := h11hi
        _ < (-236 / 1000 : ℝ) := by
          norm_num [oddStructuralCorrelation11]
    · constructor
      · calc
          (123 / 1000 : ℝ) < oddStructuralCorrelation13 (1171 / 1000) := by
            norm_num [oddStructuralCorrelation13]
          _ < oddStructuralCorrelation13
              (factorTwoPrimeShift / yoshidaEndpointA) := h13lo
      · constructor
        · calc
            oddStructuralCorrelation13
                (factorTwoPrimeShift / yoshidaEndpointA) <
              oddStructuralCorrelation13 (1169 / 1000) := h13hi
            _ < (125 / 1000 : ℝ) := by
              norm_num [oddStructuralCorrelation13]
        · constructor
          · calc
              (28 / 1000 : ℝ) <
                  oddStructuralCorrelation33 (1169 / 1000) := by
                norm_num [oddStructuralCorrelation33]
              _ < oddStructuralCorrelation33
                  (factorTwoPrimeShift / yoshidaEndpointA) := h33lo
          · calc
              oddStructuralCorrelation33
                  (factorTwoPrimeShift / yoshidaEndpointA) <
                oddStructuralCorrelation33 (1171 / 1000) := h33hi
              _ < (30 / 1000 : ℝ) := by
                norm_num [oddStructuralCorrelation33]

/-- The three exact perturbation entries lie in broad rational boxes.  The
only approximation is the global pole-free Taylor envelope; the endpoint
poles and retained primes keep their signs throughout. -/
theorem oddStructuralLow_perturbation_bounds :
    ((1 / 100 : ℝ) < factorTwoCenteredSymmetricPerturbation centeredP1 ∧
      factorTwoCenteredSymmetricPerturbation centeredP1 < (1 / 40 : ℝ)) ∧
    ((-3 / 200 : ℝ) <
        factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3 ∧
      factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3 <
        (-9 / 1000 : ℝ)) ∧
    ((-121 / 1000 : ℝ) <
        factorTwoCenteredSymmetricPerturbation centeredP3 ∧
      factorTwoCenteredSymmetricPerturbation centeredP3 < (-11 / 100 : ℝ)) := by
  let α : ℝ := Real.log 2 / Real.sqrt 2
  let β : ℝ := Real.log 3 / Real.sqrt 3
  let τ : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let c11 : ℝ := oddStructuralCorrelation11 τ
  let c13 : ℝ := oddStructuralCorrelation13 τ
  let c33 : ℝ := oddStructuralCorrelation33 τ
  have hlog := strict_log_two_fine_bounds
  have hα : (49 / 100 : ℝ) < α ∧ α < (491 / 1000 : ℝ) := by
    simpa only [α] using log_two_div_sqrt_two_bounds
  have hβ : (634 / 1000 : ℝ) < β ∧ β < (635 / 1000 : ℝ) := by
    simpa only [β] using log_three_div_sqrt_three_bounds
  have hc := oddStructuralPrimeCorrelation_bounds
  have hc11 : (-237 / 1000 : ℝ) < c11 ∧ c11 < (-236 / 1000 : ℝ) := by
    simpa only [c11, τ] using ⟨hc.1, hc.2.1⟩
  have hc13 : (123 / 1000 : ℝ) < c13 ∧ c13 < (125 / 1000 : ℝ) := by
    simpa only [c13, τ] using ⟨hc.2.2.1, hc.2.2.2.1⟩
  have hc33 : (28 / 1000 : ℝ) < c33 ∧ c33 < (30 / 1000 : ℝ) := by
    simpa only [c33, τ] using ⟨hc.2.2.2.2.1, hc.2.2.2.2.2⟩
  have hprime11Lower :
      (634 / 1000 : ℝ) * (236 / 1000) < -(β * c11) := by
    have hq : (236 / 1000 : ℝ) < -c11 := by linarith [hc11.2]
    have hmul := mul_lt_mul_of_nonneg hβ.1 hq (by norm_num) (by norm_num)
    nlinarith
  have hprime11Upper :
      -(β * c11) < (635 / 1000 : ℝ) * (237 / 1000) := by
    have hq : -c11 < (237 / 1000 : ℝ) := by linarith [hc11.1]
    have hmul := mul_lt_mul_of_nonneg hβ.2 hq
      (by linarith [hc11.2]) (by linarith [hβ.1])
    nlinarith
  have hprime13Lower :
      (634 / 1000 : ℝ) * (123 / 1000) < β * c13 := by
    exact mul_lt_mul_of_nonneg hβ.1 hc13.1 (by norm_num) (by norm_num)
  have hprime13Upper :
      β * c13 < (635 / 1000 : ℝ) * (125 / 1000) := by
    exact mul_lt_mul_of_nonneg hβ.2 hc13.2
      (by linarith [hc13.1]) (by linarith [hβ.1])
  have hprime33Lower :
      (634 / 1000 : ℝ) * (28 / 1000) < β * c33 := by
    exact mul_lt_mul_of_nonneg hβ.1 hc33.1 (by norm_num) (by norm_num)
  have hprime33Upper :
      β * c33 < (635 / 1000 : ℝ) * (30 / 1000) := by
    exact mul_lt_mul_of_nonneg hβ.2 hc33.2
      (by linarith [hc33.1]) (by linarith [hβ.1])
  have he11 := abs_le.mp
    (abs_oddStructuralRegularError11_le oddStructuralRegularKernelControl)
  have he13 := abs_lt.mp abs_oddStructuralRegularError13_lt
  have he33 := abs_le.mp
    (abs_oddStructuralRegularError33_le oddStructuralRegularKernelControl)
  constructor
  · constructor
    · rw [factorTwoCenteredSymmetricPerturbation_p1_structural_eq]
      change (1 / 100 : ℝ) <
        oddStructuralRegularError oddStructuralCorrelation11 - 4 / 375 +
          (2 / 3 - (2 / 3 : ℝ) * Real.log 2) - α * (2 / 3) - β * c11
      linarith only [he11.1, hlog.2, hα.2, hprime11Lower]
    · rw [factorTwoCenteredSymmetricPerturbation_p1_structural_eq]
      change oddStructuralRegularError oddStructuralCorrelation11 - 4 / 375 +
          (2 / 3 - (2 / 3 : ℝ) * Real.log 2) - α * (2 / 3) - β * c11 <
        (1 / 40 : ℝ)
      linarith only [he11.2, hlog.1, hα.1, hprime11Upper]
  · constructor
    · constructor
      · rw [factorTwoCenteredSymmetricPerturbationBilinear_p1_p3_structural_eq]
        change (-3 / 200 : ℝ) <
          oddStructuralRegularError oddStructuralCorrelation13 +
            (7 - 10 * Real.log 2) - β * c13
        linarith only [he13.1, hlog.2, hprime13Upper]
      · rw [factorTwoCenteredSymmetricPerturbationBilinear_p1_p3_structural_eq]
        change oddStructuralRegularError oddStructuralCorrelation13 +
            (7 - 10 * Real.log 2) - β * c13 < (-9 / 1000 : ℝ)
        linarith only [he13.2, hlog.1, hprime13Lower]
    · constructor
      · rw [factorTwoCenteredSymmetricPerturbation_p3_structural_eq]
        change (-121 / 1000 : ℝ) <
          oddStructuralRegularError oddStructuralCorrelation33 +
            (5 / 21 - (2 / 7 : ℝ) * Real.log 2) - α * (2 / 7) - β * c33
        linarith only [he33.1, hlog.2, hα.2, hprime33Upper]
      · rw [factorTwoCenteredSymmetricPerturbation_p3_structural_eq]
        change oddStructuralRegularError oddStructuralCorrelation33 +
            (5 / 21 - (2 / 7 : ℝ) * Real.log 2) - α * (2 / 7) - β * c33 <
          (-11 / 100 : ℝ)
        linarith only [he33.2, hlog.1, hα.1, hprime33Lower]

/-! ## Sign-preserving endpoint reduction -/

/-- Six broad scalar perturbation inequalities suffice for both endpoint
forms.  The determinant margins are rational and are checked exactly. -/
theorem signed_oddStructuralLow_forms_positive_of_perturbation_bounds
    (hp11Lower : (1 / 100 : ℝ) <
      factorTwoCenteredSymmetricPerturbation centeredP1)
    (hp11Upper : factorTwoCenteredSymmetricPerturbation centeredP1 <
      (1 / 40 : ℝ))
    (hp13Lower : (-3 / 200 : ℝ) <
      factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3)
    (hp13Upper :
      factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3 <
        (-9 / 1000 : ℝ))
    (hp33Lower : (-121 / 1000 : ℝ) <
      factorTwoCenteredSymmetricPerturbation centeredP3)
    (hp33Upper : factorTwoCenteredSymmetricPerturbation centeredP3 <
      (-11 / 100 : ℝ)) :
    (∀ c d : ℝ, c ≠ 0 ∨ d ≠ 0 →
        0 < yoshidaEndpointOddCleanQuadratic
              (factorTwoOddStructuralLowProfile c d) +
            factorTwoCenteredSymmetricPerturbation
              (factorTwoOddStructuralLowProfile c d)) ∧
      (∀ c d : ℝ, c ≠ 0 ∨ d ≠ 0 →
        0 < yoshidaEndpointOddCleanQuadratic
              (factorTwoOddStructuralLowProfile c d) -
            factorTwoCenteredSymmetricPerturbation
              (factorTwoOddStructuralLowProfile c d)) := by
  let p11 := factorTwoCenteredSymmetricPerturbation centeredP1
  let p13 :=
    factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3
  let p33 := factorTwoCenteredSymmetricPerturbation centeredP3
  have hplus11 : 0 < (193 / 1125 : ℝ) + p11 := by
    dsimp only [p11]
    linarith
  have hplus33 : 0 < (5951 / 18375 : ℝ) + p33 := by
    dsimp only [p33]
    linarith
  have hplus13Lower : 0 < (1 / 5 : ℝ) + p13 := by
    dsimp only [p13]
    linarith
  have hplus13Upper : (1 / 5 : ℝ) + p13 < 191 / 1000 := by
    dsimp only [p13]
    linarith
  have hplusProd :
      (193 / 1125 + p11) * (5951 / 18375 + p33) >
        ((193 / 1125 + 1 / 100) *
          (5951 / 18375 - 121 / 1000) : ℝ) := by
    have hA : (193 / 1125 + 1 / 100 : ℝ) < 193 / 1125 + p11 := by
      dsimp only [p11]
      linarith
    have hD : (5951 / 18375 - 121 / 1000 : ℝ) <
        5951 / 18375 + p33 := by
      dsimp only [p33]
      linarith
    have hLA : 0 < (193 / 1125 + 1 / 100 : ℝ) := by norm_num
    have hLD : 0 < (5951 / 18375 - 121 / 1000 : ℝ) := by norm_num
    nlinarith [mul_pos (sub_pos.mpr hA) (sub_pos.mpr hD)]
  have hplusSq : ((1 / 5 : ℝ) + p13) ^ 2 < (191 / 1000 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((1 / 5 : ℝ) + p13 - 191 / 1000)]
  have hplusDet : 0 <
      ((193 / 1125 : ℝ) + p11) * (5951 / 18375 + p33) -
        ((1 / 5 : ℝ) + p13) ^ 2 := by
    have hmargin :
        (191 / 1000 : ℝ) ^ 2 <
          (193 / 1125 + 1 / 100) *
            (5951 / 18375 - 121 / 1000) := by norm_num
    linarith
  have hminus11 : 0 < (193 / 1125 : ℝ) - p11 := by
    dsimp only [p11]
    linarith
  have hminus33 : 0 < (5951 / 18375 : ℝ) - p33 := by
    dsimp only [p33]
    linarith
  have hminus13Lower : 0 < (1 / 5 : ℝ) - p13 := by
    dsimp only [p13]
    linarith
  have hminus13Upper : (1 / 5 : ℝ) - p13 < 43 / 200 := by
    dsimp only [p13]
    linarith
  have hminusProd :
      (193 / 1125 - p11) * (5951 / 18375 - p33) >
        ((193 / 1125 - 1 / 40) *
          (5951 / 18375 + 11 / 100) : ℝ) := by
    have hA : (193 / 1125 - 1 / 40 : ℝ) < 193 / 1125 - p11 := by
      dsimp only [p11]
      linarith
    have hD : (5951 / 18375 + 11 / 100 : ℝ) <
        5951 / 18375 - p33 := by
      dsimp only [p33]
      linarith
    have hLA : 0 < (193 / 1125 - 1 / 40 : ℝ) := by norm_num
    have hLD : 0 < (5951 / 18375 + 11 / 100 : ℝ) := by norm_num
    nlinarith [mul_pos (sub_pos.mpr hA) (sub_pos.mpr hD)]
  have hminusSq : ((1 / 5 : ℝ) - p13) ^ 2 < (43 / 200 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((1 / 5 : ℝ) - p13 - 43 / 200)]
  have hminusDet : 0 <
      ((193 / 1125 : ℝ) - p11) * (5951 / 18375 - p33) -
        ((1 / 5 : ℝ) - p13) ^ 2 := by
    have hmargin :
        (43 / 200 : ℝ) ^ 2 <
          (193 / 1125 - 1 / 40) *
            (5951 / 18375 + 11 / 100) := by norm_num
    linarith
  constructor
  · intro c d hne
    have hmatrix := real_twoByTwo_quadratic_pos
      ((193 / 1125 : ℝ) + p11) ((1 / 5 : ℝ) + p13)
      ((5951 / 18375 : ℝ) + p33) c d hplus11 hplusDet hne
    have hclean := oddStructuralLow_clean_rationalGram_le c d
    have hpert := factorTwoCenteredSymmetricPerturbation_oddStructuralLow c d
    dsimp only [p11, p13, p33] at hmatrix
    rw [hpert]
    nlinarith
  · intro c d hne
    have hmatrix := real_twoByTwo_quadratic_pos
      ((193 / 1125 : ℝ) - p11) ((1 / 5 : ℝ) - p13)
      ((5951 / 18375 : ℝ) - p33) c d hminus11 hminusDet hne
    have hclean := oddStructuralLow_clean_rationalGram_le c d
    have hpert := factorTwoCenteredSymmetricPerturbation_oddStructuralLow c d
    dsimp only [p11, p13, p33] at hmatrix
    rw [hpert]
    nlinarith

/-- The same six structural scalar bounds discharge the four endpoint
gates used by the odd low Schur API. -/
theorem oddStructuralLow_endpoint_gates_of_perturbation_bounds
    (hp11Lower : (1 / 100 : ℝ) <
      factorTwoCenteredSymmetricPerturbation centeredP1)
    (hp11Upper : factorTwoCenteredSymmetricPerturbation centeredP1 <
      (1 / 40 : ℝ))
    (hp13Lower : (-3 / 200 : ℝ) <
      factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3)
    (hp13Upper :
      factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3 <
        (-9 / 1000 : ℝ))
    (hp33Lower : (-121 / 1000 : ℝ) <
      factorTwoCenteredSymmetricPerturbation centeredP3)
    (hp33Upper : factorTwoCenteredSymmetricPerturbation centeredP3 <
      (-11 / 100 : ℝ)) :
    0 < factorTwoOddStructuralPhaseLow11 1 ∧
      0 < factorTwoOddStructuralPhaseLow11 1 *
          factorTwoOddStructuralPhaseLow33 1 -
        factorTwoOddStructuralPhaseLow13 1 ^ 2 ∧
      0 < factorTwoOddStructuralPhaseLow11 (-1) ∧
      0 < factorTwoOddStructuralPhaseLow11 (-1) *
          factorTwoOddStructuralPhaseLow33 (-1) -
        factorTwoOddStructuralPhaseLow13 (-1) ^ 2 := by
  rw [factorTwoOddStructuralPhaseLow_endpoint_hypotheses_iff_signed_forms]
  exact signed_oddStructuralLow_forms_positive_of_perturbation_bounds
    hp11Lower hp11Upper hp13Lower hp13Upper hp33Lower hp33Upper

/-- Both complete endpoint forms are strictly positive on every nonzero
vector in the intrinsic odd `P₁/P₃` plane. -/
theorem signed_oddStructuralLow_forms_positive :
    (∀ c d : ℝ, c ≠ 0 ∨ d ≠ 0 →
        0 < yoshidaEndpointOddCleanQuadratic
              (factorTwoOddStructuralLowProfile c d) +
            factorTwoCenteredSymmetricPerturbation
              (factorTwoOddStructuralLowProfile c d)) ∧
      (∀ c d : ℝ, c ≠ 0 ∨ d ≠ 0 →
        0 < yoshidaEndpointOddCleanQuadratic
              (factorTwoOddStructuralLowProfile c d) -
            factorTwoCenteredSymmetricPerturbation
              (factorTwoOddStructuralLowProfile c d)) := by
  rcases oddStructuralLow_perturbation_bounds with
    ⟨⟨hp11Lower, hp11Upper⟩,
      ⟨⟨hp13Lower, hp13Upper⟩, ⟨hp33Lower, hp33Upper⟩⟩⟩
  exact signed_oddStructuralLow_forms_positive_of_perturbation_bounds
    hp11Lower hp11Upper hp13Lower hp13Upper hp33Lower hp33Upper

/-- The four scalar endpoint gates required by the odd low Schur API. -/
theorem oddStructuralLow_endpoint_gates :
    0 < factorTwoOddStructuralPhaseLow11 1 ∧
      0 < factorTwoOddStructuralPhaseLow11 1 *
          factorTwoOddStructuralPhaseLow33 1 -
        factorTwoOddStructuralPhaseLow13 1 ^ 2 ∧
      0 < factorTwoOddStructuralPhaseLow11 (-1) ∧
      0 < factorTwoOddStructuralPhaseLow11 (-1) *
          factorTwoOddStructuralPhaseLow33 (-1) -
        factorTwoOddStructuralPhaseLow13 (-1) ^ 2 := by
  rw [factorTwoOddStructuralPhaseLow_endpoint_hypotheses_iff_signed_forms]
  exact signed_oddStructuralLow_forms_positive

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
