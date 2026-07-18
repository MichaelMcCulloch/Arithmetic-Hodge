import ArithmeticHodge.Analysis.ShiftedLegendreJacobiSturmStructural
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialIntegrable
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointPotentialLegendreGreenStructural

open ShiftedLegendreJacobiSturmStructural
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable

noncomputable section

/-!
# Green identity for the endpoint potential

The endpoint logarithm intertwines the centered Legendre Sturm operator with
the first-order Wronskian form.  The proof is uniform in both polynomials and
uses `Real.negMulLog` to absorb both singular endpoints continuously.
-/

/-- Exact Green commutator identity for the centered endpoint potential. -/
theorem integral_endpointPotential_sturm_commutator (p q : ℝ[X]) :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x *
        ((centeredLegendreSturm p).eval x * q.eval x -
          p.eval x * (centeredLegendreSturm q).eval x)) =
      ∫ x : ℝ in -1..1,
        x * (p.derivative.eval x * q.eval x -
          p.eval x * q.derivative.eval x) := by
  let R : ℝ[X] := derivative p * q - p * derivative q
  let C : ℝ[X] := centeredLegendreSturm p * q -
    p * centeredLegendreSturm q
  have hC : C = -derivative ((1 - X ^ 2) * R) := by
    dsimp only [C, R, centeredLegendreSturm]
    simp only [derivative_mul, derivative_sub]
    ring
  have hCeval (x : ℝ) :
      C.eval x = 2 * x * R.eval x -
        (1 - x ^ 2) * R.derivative.eval x := by
    rw [hC]
    simp [derivative_mul]
    ring
  let F : ℝ → ℝ := fun x ↦
    -(1 / 2 : ℝ) * Real.negMulLog (1 - x ^ 2) * R.eval x
  let f : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * C.eval x - x * R.eval x
  have hRcont : Continuous (fun x : ℝ ↦ R.eval x) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (R.hasDerivAt x).continuousAt
  have hCcont : Continuous (fun x : ℝ ↦ C.eval x) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (C.hasDerivAt x).continuousAt
  have hFcont : Continuous F := by
    dsimp only [F]
    fun_prop
  have hderiv (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt F (f x) x := by
    have hy : 1 - x ^ 2 ≠ 0 := by
      have habs : |x| < 1 := (abs_lt).2 hx
      nlinarith [(sq_lt_one_iff_abs_lt_one x).2 habs]
    have hinner : HasDerivAt (fun y : ℝ ↦ 1 - y ^ 2) (-2 * x) x := by
      convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1
      all_goals simp
    have hneg := (Real.hasDerivAt_negMulLog hy).comp x hinner
    have hraw := (hneg.mul (R.hasDerivAt x)).const_mul (-(1 / 2 : ℝ))
    convert hraw using 1
    · funext y
      dsimp only [F]
      simp only [Pi.mul_apply, Function.comp_apply]
      ring
    · dsimp only [f, yoshidaEndpointPotential]
      rw [hCeval x]
      simp only [Real.negMulLog_def, Function.comp_apply]
      ring
  have hVC : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * C.eval x)
      volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul (fun x : ℝ ↦ C.eval x) hCcont
  have hxR : IntervalIntegrable (fun x : ℝ ↦ x * R.eval x)
      volume (-1) 1 :=
    (continuous_id.mul hRcont).intervalIntegrable (-1) 1
  have hf : IntervalIntegrable f volume (-1) 1 := by
    exact hVC.sub hxR
  have hFTC : (∫ x : ℝ in -1..1, f x) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (by norm_num : (-1 : ℝ) ≤ 1) hFcont.continuousOn hderiv hf]
    dsimp only [F]
    norm_num [Real.negMulLog_zero]
  have hsplit :
      (∫ x : ℝ in -1..1, f x) =
        (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * C.eval x) -
        ∫ x : ℝ in -1..1, x * R.eval x := by
    rw [show f = fun x : ℝ ↦
        yoshidaEndpointPotential x * C.eval x - x * R.eval x by rfl]
    exact intervalIntegral.integral_sub hVC hxR
  rw [hsplit] at hFTC
  have heq :
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * C.eval x) =
      ∫ x : ℝ in -1..1, x * R.eval x := by
    linarith
  simpa only [C, R, Polynomial.eval_sub, Polynomial.eval_mul] using heq

end

end ArithmeticHodge.Analysis.YoshidaEndpointPotentialLegendreGreenStructural
