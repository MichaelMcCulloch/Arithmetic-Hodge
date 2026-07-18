import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowPotential
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointPotentialEvenMomentStructural

open YoshidaEndpointEvenLowPotential
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable

noncomputable section

/-!
# Structural recurrence for endpoint-potential moments

The logarithmic endpoint potential has an exact first-order recurrence on
all even monomials.  The proof uses one continuous antiderivative built from
`Real.negMulLog`; its endpoint values are automatic, so no mode or degree is
expanded.
-/

/-- The degree-`2n` moment of the centered endpoint potential. -/
def endpointPotentialEvenMoment (n : ℕ) : ℝ :=
  ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * x ^ (2 * n)

/-- The structural initial value of the even endpoint-potential moments. -/
theorem endpointPotentialEvenMoment_zero :
    endpointPotentialEvenMoment 0 = 2 - 2 * Real.log 2 := by
  simpa [endpointPotentialEvenMoment] using integral_endpointPotential_one

/-- Exact all-degree recurrence for the even endpoint-potential moments. -/
theorem endpointPotentialEvenMoment_succ (n : ℕ) :
    (2 * n + 3 : ℝ) * endpointPotentialEvenMoment (n + 1) =
      (2 * n + 1 : ℝ) * endpointPotentialEvenMoment n +
        2 / (2 * n + 3 : ℝ) := by
  let F : ℝ → ℝ := fun x ↦
    -(1 / 2 : ℝ) * x ^ (2 * n + 1) * Real.negMulLog (1 - x ^ 2) +
      x ^ (2 * n + 3) / (2 * n + 3 : ℝ)
  let f : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x *
      ((2 * n + 3 : ℝ) * x ^ (2 * n + 2) -
        (2 * n + 1 : ℝ) * x ^ (2 * n))
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
    have hnegMulLog := (Real.hasDerivAt_negMulLog hy).comp x hinner
    have hleft :=
      (((hasDerivAt_id x).pow (2 * n + 1)).mul hnegMulLog).const_mul
        (-(1 / 2 : ℝ))
    have hright :=
      ((hasDerivAt_id x).pow (2 * n + 3)).div_const
        (2 * n + 3 : ℝ)
    convert hleft.add hright using 1
    · funext y
      dsimp only [F]
      simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
        Function.comp_apply, id_eq]
      ring
    · dsimp only [f, yoshidaEndpointPotential, Real.negMulLog]
      have hden : (2 * n + 3 : ℝ) ≠ 0 := by positivity
      have hn1 : 2 * n + 1 - 1 = 2 * n := by omega
      have hn3 : 2 * n + 3 - 1 = 2 * n + 2 := by omega
      simp only [Real.negMulLog_def, Function.comp_apply, Pi.pow_apply,
        id_eq, hn1, hn3,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      field_simp [hy, hden]
      ring
  have hlow : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ (2 * n))
      volume (-1) 1 := by
    have h := intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ n) (continuous_id.pow n)
    apply h.congr
    intro x _hx
    ring
  have hhigh : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ (2 * n + 2))
      volume (-1) 1 := by
    have h := intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ (n + 1)) (continuous_id.pow (n + 1))
    apply h.congr
    intro x _hx
    ring
  have hf : IntervalIntegrable f volume (-1) 1 := by
    have h :=
      (hhigh.const_mul (2 * n + 3 : ℝ)).sub
        (hlow.const_mul (2 * n + 1 : ℝ))
    apply h.congr
    intro x _hx
    dsimp only [f]
    ring
  have hFTC : (∫ x : ℝ in -1..1, f x) = 2 / (2 * n + 3 : ℝ) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (by norm_num : (-1 : ℝ) ≤ 1) hFcont.continuousOn hderiv hf]
    dsimp only [F]
    have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
    rw [hodd.neg_one_pow]
    have hzero : Real.negMulLog (0 : ℝ) = 0 := Real.negMulLog_zero
    simp only [one_pow, neg_one_sq, sub_self, hzero, mul_zero, zero_add]
    ring
  have hsplit :
      (∫ x : ℝ in -1..1, f x) =
        (2 * n + 3 : ℝ) *
            (∫ x : ℝ in -1..1,
              yoshidaEndpointPotential x * x ^ (2 * n + 2)) -
          (2 * n + 1 : ℝ) *
            (∫ x : ℝ in -1..1,
              yoshidaEndpointPotential x * x ^ (2 * n)) := by
    rw [show f = fun x : ℝ ↦
        (2 * n + 3 : ℝ) *
            (yoshidaEndpointPotential x * x ^ (2 * n + 2)) -
          (2 * n + 1 : ℝ) *
            (yoshidaEndpointPotential x * x ^ (2 * n)) by
      funext x
      dsimp only [f]
      ring]
    rw [intervalIntegral.integral_sub
        (hhigh.const_mul (2 * n + 3 : ℝ))
        (hlow.const_mul (2 * n + 1 : ℝ)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hsplit] at hFTC
  unfold endpointPotentialEvenMoment
  rw [show 2 * (n + 1) = 2 * n + 2 by omega]
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointPotentialEvenMomentStructural
