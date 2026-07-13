import ArithmeticHodge.Analysis.CenteredOddOneThreeEnergy
import ArithmeticHodge.Analysis.YoshidaEndpointOcticTwoModeSchurData

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaEndpointOcticOddCoercivity

open CenteredOddOneThreeEnergy
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection
open YoshidaEndpointOcticPotential
open YoshidaEndpointOcticTwoModeSchurData

noncomputable section

/-!
# Structural odd octic coercivity

The logarithmic form retains the exact `P₁,P₃` block and a uniform infinite
tail.  The octic potential couples the low block to that tail through two
explicit residual polynomials.  A single exact square spends the uniform
tail reserve, leaving the fixed positive two-mode Schur form.
-/

def centeredOddCombinedOcticResidual (w : ℝ → ℝ) : ℝ → ℝ := fun x ↦
  centeredOddP1Coefficient w * octicResidualP1 x +
    centeredOddP3Coefficient w * octicResidualP3 x

theorem integral_centeredOddResidual_mul_p1
    (w : ℝ → ℝ) (hwcont : Continuous w) :
    (∫ x : ℝ in -1..1,
      centeredOddOneThreeResidual w x * centeredP1 x) = 0 := by
  let a := centeredOddP1Coefficient w
  let b := centeredOddP3Coefficient w
  rw [show (fun x : ℝ ↦ centeredOddOneThreeResidual w x * centeredP1 x) =
      fun x ↦ w x * centeredP1 x +
        (-a) * centeredP1 x ^ 2 +
        (-b) * (centeredP1 x * centeredP3 x) by
    funext x
    dsimp only [centeredOddOneThreeResidual, a, b]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [centeredP1, centeredP3]
    fun_prop
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_mul_centeredP1_eq, integral_centeredP1_sq,
    integral_centeredP1_mul_p3]
  dsimp only [a, b]
  ring

theorem integral_centeredOddResidual_mul_p3
    (w : ℝ → ℝ) (hwcont : Continuous w) :
    (∫ x : ℝ in -1..1,
      centeredOddOneThreeResidual w x * centeredP3 x) = 0 := by
  let a := centeredOddP1Coefficient w
  let b := centeredOddP3Coefficient w
  rw [show (fun x : ℝ ↦ centeredOddOneThreeResidual w x * centeredP3 x) =
      fun x ↦ w x * centeredP3 x +
        (-a) * (centeredP1 x * centeredP3 x) +
        (-b) * centeredP3 x ^ 2 by
    funext x
    dsimp only [centeredOddOneThreeResidual, a, b]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [centeredP1, centeredP3]
    fun_prop
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_mul_centeredP3_eq, integral_centeredP1_mul_p3,
    integral_centeredP3_sq]
  dsimp only [a, b]
  ring

theorem integral_octic_mul_sq_decomposition
    (w : ℝ → ℝ) (hwcont : Continuous w) :
    (∫ x : ℝ in -1..1, yoshidaEndpointOctic x * w x ^ 2) =
      (13771 / 41580 : ℝ) * centeredOddP1Coefficient w ^ 2 +
        2 * (8 / 65 : ℝ) * centeredOddP1Coefficient w *
          centeredOddP3Coefficient w +
        (23161 / 180180 : ℝ) * centeredOddP3Coefficient w ^ 2 +
        2 * (∫ x : ℝ in -1..1,
          centeredOddOneThreeResidual w x *
            centeredOddCombinedOcticResidual w x) +
        ∫ x : ℝ in -1..1,
          yoshidaEndpointOctic x * centeredOddOneThreeResidual w x ^ 2 := by
  let a := centeredOddP1Coefficient w
  let b := centeredOddP3Coefficient w
  let v := centeredOddOneThreeResidual w
  let r := centeredOddCombinedOcticResidual w
  have hv1 := integral_centeredOddResidual_mul_p1 w hwcont
  have hv3 := integral_centeredOddResidual_mul_p3 w hwcont
  have hlow :
      (∫ x : ℝ in -1..1,
        yoshidaEndpointOctic x *
          (a * centeredP1 x + b * centeredP3 x) ^ 2) =
        (13771 / 41580 : ℝ) * a ^ 2 +
          2 * (8 / 65 : ℝ) * a * b +
          (23161 / 180180 : ℝ) * b ^ 2 := by
    rw [show (fun x : ℝ ↦ yoshidaEndpointOctic x *
        (a * centeredP1 x + b * centeredP3 x) ^ 2) = fun x ↦
      a ^ 2 * (yoshidaEndpointOctic x * centeredP1 x ^ 2) +
        (2 * a * b) *
          (yoshidaEndpointOctic x * centeredP1 x * centeredP3 x) +
        b ^ 2 * (yoshidaEndpointOctic x * centeredP3 x ^ 2) by
      funext x
      ring]
    repeat rw [intervalIntegral.integral_add]
    all_goals try
      apply Continuous.intervalIntegrable
      simp only [yoshidaEndpointOctic, centeredP1, centeredP3]
      fun_prop
    repeat rw [intervalIntegral.integral_const_mul]
    rw [integral_octic_mul_p1_sq, integral_octic_mul_p1_mul_p3,
      integral_octic_mul_p3_sq]
    ring
  have hcross :
      (∫ x : ℝ in -1..1,
        v x * (yoshidaEndpointOctic x *
          (a * centeredP1 x + b * centeredP3 x))) =
        ∫ x : ℝ in -1..1, v x * r x := by
    rw [show (fun x : ℝ ↦ v x * (yoshidaEndpointOctic x *
        (a * centeredP1 x + b * centeredP3 x))) = fun x ↦
      v x * r x +
        (a * (13771 / 27720 : ℝ) + b * (12 / 65 : ℝ)) *
          (v x * centeredP1 x) +
        (a * (28 / 65 : ℝ) + b * (23161 / 51480 : ℝ)) *
          (v x * centeredP3 x) by
      funext x
      dsimp only [v, r, centeredOddCombinedOcticResidual,
        octicResidualP1, octicResidualP3, a, b]
      ring]
    repeat rw [intervalIntegral.integral_add]
    all_goals try
      apply Continuous.intervalIntegrable
      simp only [v, r, centeredOddCombinedOcticResidual,
        centeredOddOneThreeResidual, octicResidualP1, octicResidualP3,
        yoshidaEndpointOctic, centeredP1, centeredP3]
      fun_prop
    repeat rw [intervalIntegral.integral_const_mul]
    dsimp only [v]
    rw [hv1, hv3]
    ring
  rw [show (fun x : ℝ ↦ yoshidaEndpointOctic x * w x ^ 2) = fun x ↦
      yoshidaEndpointOctic x *
          (a * centeredP1 x + b * centeredP3 x) ^ 2 +
        2 * (v x * (yoshidaEndpointOctic x *
          (a * centeredP1 x + b * centeredP3 x))) +
        yoshidaEndpointOctic x * v x ^ 2 by
    funext x
    dsimp only [v, centeredOddOneThreeResidual, a, b]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [v, centeredOddOneThreeResidual, yoshidaEndpointOctic,
      centeredP1, centeredP3]
    fun_prop
  rw [hlow, intervalIntegral.integral_const_mul, hcross]

theorem integral_combinedOcticResidual_sq
    (w : ℝ → ℝ) :
    (∫ x : ℝ in -1..1, centeredOddCombinedOcticResidual w x ^ 2) =
      residualGramC11 * centeredOddP1Coefficient w ^ 2 +
        2 * residualGramC13 * centeredOddP1Coefficient w *
          centeredOddP3Coefficient w +
        residualGramC33 * centeredOddP3Coefficient w ^ 2 := by
  let a := centeredOddP1Coefficient w
  let b := centeredOddP3Coefficient w
  rw [show (fun x : ℝ ↦ centeredOddCombinedOcticResidual w x ^ 2) =
      fun x ↦ a ^ 2 * octicResidualP1 x ^ 2 +
        (2 * a * b) * (octicResidualP1 x * octicResidualP3 x) +
        b ^ 2 * octicResidualP3 x ^ 2 by
    funext x
    dsimp only [centeredOddCombinedOcticResidual, a, b]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [octicResidualP1, octicResidualP3, yoshidaEndpointOctic,
      centeredP1, centeredP3]
    fun_prop
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_octicResidualP1_sq,
    integral_octicResidualP1_mul_residualP3, integral_octicResidualP3_sq]
  dsimp only [a, b]
  ring

theorem octic_residual_tail_nonneg
    (w : ℝ → ℝ) :
    0 ≤ ∫ x : ℝ in -1..1,
      yoshidaEndpointOctic x * centeredOddOneThreeResidual w x ^ 2 := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x _hx
  apply mul_nonneg
  · unfold yoshidaEndpointOctic
    positivity
  · exact sq_nonneg _

theorem tailReserve_completion
    (w : ℝ → ℝ) (hwcont : Continuous w) :
    tailReserve *
          (∫ x : ℝ in -1..1, centeredOddOneThreeResidual w x ^ 2) +
        2 * (∫ x : ℝ in -1..1,
          centeredOddOneThreeResidual w x *
            centeredOddCombinedOcticResidual w x) ≥
      -(∫ x : ℝ in -1..1,
          centeredOddCombinedOcticResidual w x ^ 2) / tailReserve := by
  let v := centeredOddOneThreeResidual w
  let r := centeredOddCombinedOcticResidual w
  have hδ : 0 < tailReserve := by norm_num [tailReserve]
  have hsquare : 0 ≤ ∫ x : ℝ in -1..1,
      (tailReserve * v x + r x) ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _hx
    exact sq_nonneg _
  have hexpand :
      (∫ x : ℝ in -1..1, (tailReserve * v x + r x) ^ 2) =
        tailReserve ^ 2 * (∫ x : ℝ in -1..1, v x ^ 2) +
          (2 * tailReserve) * (∫ x : ℝ in -1..1, v x * r x) +
          ∫ x : ℝ in -1..1, r x ^ 2 := by
    rw [show (fun x : ℝ ↦ (tailReserve * v x + r x) ^ 2) = fun x ↦
      tailReserve ^ 2 * v x ^ 2 +
        (2 * tailReserve) * (v x * r x) + r x ^ 2 by
      funext x
      ring]
    repeat rw [intervalIntegral.integral_add]
    all_goals try
      apply Continuous.intervalIntegrable
      simp only [v, r, centeredOddOneThreeResidual,
        centeredOddCombinedOcticResidual, octicResidualP1,
        octicResidualP3, yoshidaEndpointOctic, centeredP1, centeredP3]
      fun_prop
    repeat rw [intervalIntegral.integral_const_mul]
  rw [hexpand] at hsquare
  dsimp only [v, r] at hsquare ⊢
  norm_num [tailReserve] at hsquare ⊢
  linarith

theorem seven_fifths_mul_integral_sq_le_logEnergy_div_four_add_octic
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hwodd : Function.Odd w) :
    (7 / 5 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      centeredRawLogEnergy w / 4 +
        ∫ x : ℝ in -1..1, yoshidaEndpointOctic x * w x ^ 2 := by
  let a := centeredOddP1Coefficient w
  let b := centeredOddP3Coefficient w
  let v := centeredOddOneThreeResidual w
  let r := centeredOddCombinedOcticResidual w
  have hlog := centered_odd_one_three_tail_energy_le
    w hwcont hf henergy hwodd
  have hmass0 := integral_centeredOddOneThreeResidual_sq w hwcont
  have hmass :
      (∫ x : ℝ in -1..1, w x ^ 2) =
        (2 / 3 : ℝ) * a ^ 2 + (2 / 7 : ℝ) * b ^ 2 +
          ∫ x : ℝ in -1..1, v x ^ 2 := by
    dsimp only [a, b, v]
    linarith
  have hpot := integral_octic_mul_sq_decomposition w hwcont
  have hgram := integral_combinedOcticResidual_sq w
  have htail := octic_residual_tail_nonneg w
  have hcompletion := tailReserve_completion w hwcont
  have hschur := schurQuadratic_nonneg a b
  have hQ11 : rawLowQ11 =
      (1 - 7 / 5 : ℝ) * (2 / 3 : ℝ) + 13771 / 41580 := by
    norm_num [rawLowQ11]
  have hQ33 : rawLowQ33 =
      (11 / 6 - 7 / 5 : ℝ) * (2 / 7 : ℝ) + 23161 / 180180 := by
    norm_num [rawLowQ33]
  have hQ13 : rawLowQ13 = (8 / 65 : ℝ) := by
    rfl
  have hδ : tailReserve = 137 / 60 - 7 / 5 := by
    norm_num [tailReserve]
  have hSchurEq :
      schurS11 * a ^ 2 + 2 * schurS13 * a * b + schurS33 * b ^ 2 =
        rawLowQ11 * a ^ 2 + 2 * rawLowQ13 * a * b +
          rawLowQ33 * b ^ 2 -
        (residualGramC11 * a ^ 2 +
          2 * residualGramC13 * a * b + residualGramC33 * b ^ 2) /
            tailReserve := by
    unfold schurS11 schurS13 schurS33
    ring
  have hsecond :
      schurS11 * a ^ 2 + 2 * schurS13 * a * b + schurS33 * b ^ 2 ≤
        rawLowQ11 * a ^ 2 + 2 * rawLowQ13 * a * b +
          rawLowQ33 * b ^ 2 +
        tailReserve * (∫ x : ℝ in -1..1, v x ^ 2) +
        2 * (∫ x : ℝ in -1..1, v x * r x) +
        ∫ x : ℝ in -1..1, yoshidaEndpointOctic x * v x ^ 2 := by
    rw [hSchurEq]
    dsimp only [a, b, v, r] at hgram hcompletion htail ⊢
    rw [hgram] at hcompletion
    norm_num [tailReserve] at hcompletion ⊢
    linarith
  have hfirst :
      rawLowQ11 * a ^ 2 + 2 * rawLowQ13 * a * b + rawLowQ33 * b ^ 2 +
          tailReserve * (∫ x : ℝ in -1..1, v x ^ 2) +
          2 * (∫ x : ℝ in -1..1, v x * r x) +
          ∫ x : ℝ in -1..1, yoshidaEndpointOctic x * v x ^ 2 ≤
        centeredRawLogEnergy w / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointOctic x * w x ^ 2) -
          (7 / 5 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
    dsimp only [a, b, v, r] at hlog hmass hpot ⊢
    rw [hQ11, hQ13, hQ33, hδ]
    linarith
  have hnonneg : 0 ≤
      centeredRawLogEnergy w / 4 +
        (∫ x : ℝ in -1..1, yoshidaEndpointOctic x * w x ^ 2) -
        (7 / 5 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) :=
    hschur.trans (hsecond.trans hfirst)
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointOcticOddCoercivity
