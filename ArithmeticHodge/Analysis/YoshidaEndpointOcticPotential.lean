import ArithmeticHodge.Analysis.YoshidaEndpointPotentialBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointOcticPotential

open YoshidaEndpointPotentialBound

noncomputable section

/-- The first four positive terms forced by the logarithmic endpoint potential. -/
def yoshidaEndpointOctic (x : ℝ) : ℝ :=
  x ^ 2 / 2 + x ^ 4 / 4 + x ^ 6 / 6 + x ^ 8 / 8

/-- The centered degree-one Legendre polynomial. -/
def centeredP1 (x : ℝ) : ℝ := x

/-- The centered degree-three Legendre polynomial. -/
def centeredP3 (x : ℝ) : ℝ := (5 * x ^ 3 - 3 * x) / 2

theorem octic_le_endpointPotential {x : ℝ} (hx : |x| < 1) :
    yoshidaEndpointOctic x ≤ yoshidaEndpointPotential x := by
  let R : ℝ → ℝ := fun u ↦
    -Real.log (1 - u) - u - u ^ 2 / 2 - u ^ 3 / 3 - u ^ 4 / 4
  have hu0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hu1 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).2 hx
  have hRderiv (u : ℝ) (hu : u < 1) :
      HasDerivAt R (u ^ 4 / (1 - u)) u := by
    have hinner : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) u := by
      convert (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u) using 1
      ring
    have hne : 1 - u ≠ 0 := by linarith
    have hlog := (Real.hasDerivAt_log hne).comp u hinner
    have hsq := ((hasDerivAt_id u).pow 2).div_const 2
    have hcub := ((hasDerivAt_id u).pow 3).div_const 3
    have hquart := ((hasDerivAt_id u).pow 4).div_const 4
    dsimp only [R]
    convert (((hlog.neg.sub (hasDerivAt_id u)).sub hsq).sub hcub).sub hquart using 1
    simp only [id_eq, Nat.cast_ofNat]
    field_simp [hne]
    ring
  have hRcont : ContinuousOn R (Icc 0 (x ^ 2)) := by
    intro u hu
    exact (hRderiv u (lt_of_le_of_lt hu.2 hu1)).continuousAt.continuousWithinAt
  have hRmono : MonotoneOn R (Icc 0 (x ^ 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (x ^ 2)) hRcont ?_ ?_
    · intro u hu
      exact (hRderiv u (lt_of_le_of_lt (interior_subset hu).2 hu1)).differentiableAt
        |>.differentiableWithinAt
    · intro u hu
      rw [(hRderiv u (lt_of_le_of_lt (interior_subset hu).2 hu1)).deriv]
      exact div_nonneg (by positivity) (by linarith [(interior_subset hu).2])
  have hRnonneg : 0 ≤ R (x ^ 2) := by
    have hmono := hRmono (by exact ⟨le_rfl, hu0⟩)
      (by exact ⟨hu0, le_rfl⟩) hu0
    simpa [R] using hmono
  dsimp only [R] at hRnonneg
  dsimp only [yoshidaEndpointOctic, yoshidaEndpointPotential]
  ring_nf at hRnonneg ⊢
  linarith

/-- Structural antiderivative formula for every natural monomial. -/
theorem integral_pow_nat (n : ℕ) (a b : ℝ) :
    (∫ x : ℝ in a..b, x ^ n) =
      (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  let F : ℝ → ℝ := fun x ↦ x ^ (n + 1) / (n + 1)
  have hderiv (x : ℝ) : HasDerivAt F (x ^ n) x := by
    dsimp only [F]
    convert ((hasDerivAt_id x).pow (n + 1)).div_const (n + 1) using 1
    simp only [id_eq, Nat.cast_add, Nat.cast_one]
    field_simp
    rw [Nat.add_sub_cancel]
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx ↦ hderiv x)
      (Continuous.intervalIntegrable (by fun_prop) a b)
  rw [hint]
  dsimp only [F]
  ring

theorem integral_octic_mul_p1_sq :
    (∫ x : ℝ in -1..1, yoshidaEndpointOctic x * centeredP1 x ^ 2) =
      13771 / 41580 := by
  simp only [yoshidaEndpointOctic, centeredP1]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

theorem integral_octic_mul_p1_mul_p3 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointOctic x * centeredP1 x * centeredP3 x) =
      8 / 65 := by
  rw [show (fun x : ℝ ↦
      yoshidaEndpointOctic x * centeredP1 x * centeredP3 x) =
    fun x ↦ x ^ 4 * (-3 / 4) + x ^ 6 * (7 / 8) + x ^ 8 * (3 / 8) +
      x ^ 10 * (11 / 48) + x ^ 12 * (5 / 16) by
    funext x
    simp only [yoshidaEndpointOctic, centeredP1, centeredP3]
    ring]
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

theorem integral_octic_mul_p3_sq :
    (∫ x : ℝ in -1..1, yoshidaEndpointOctic x * centeredP3 x ^ 2) =
      23161 / 180180 := by
  rw [show (fun x : ℝ ↦ yoshidaEndpointOctic x * centeredP3 x ^ 2) =
    fun x ↦ x ^ 4 * (9 / 8) + x ^ 6 * (-51 / 16) + x ^ 8 * (13 / 8) +
      x ^ 10 * (19 / 32) + x ^ 12 * (5 / 48) + x ^ 14 * (25 / 32) by
    funext x
    simp only [yoshidaEndpointOctic, centeredP3]
    ring]
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

theorem integral_octic_sq_mul_p1_sq :
    (∫ x : ℝ in -1..1, yoshidaEndpointOctic x ^ 2 * centeredP1 x ^ 2) =
      27844421 / 126977760 := by
  simp only [yoshidaEndpointOctic, centeredP1]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

theorem integral_octic_sq_mul_p1_mul_p3 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointOctic x ^ 2 * centeredP1 x * centeredP3 x) =
      1781146 / 14549535 := by
  rw [show (fun x : ℝ ↦
      yoshidaEndpointOctic x ^ 2 * centeredP1 x * centeredP3 x) =
    fun x ↦ x ^ 6 * (-3 / 8) + x ^ 8 * (1 / 4) + x ^ 10 * (9 / 32) +
      x ^ 12 * (25 / 96) + x ^ 14 * (37 / 96) + x ^ 16 * (47 / 288) +
      x ^ 18 * (31 / 384) + x ^ 20 * (5 / 128) by
    funext x
    simp only [yoshidaEndpointOctic, centeredP1, centeredP3]
    ring]
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

theorem integral_octic_sq_mul_p3_sq :
    (∫ x : ℝ in -1..1, yoshidaEndpointOctic x ^ 2 * centeredP3 x ^ 2) =
      1078013191 / 10708457760 := by
  rw [show (fun x : ℝ ↦ yoshidaEndpointOctic x ^ 2 * centeredP3 x ^ 2) =
    fun x ↦ x ^ 6 * (9 / 16) + x ^ 8 * (-21 / 16) + x ^ 10 * (13 / 64) +
      x ^ 12 * (5 / 16) + x ^ 14 * (7 / 96) + x ^ 16 * (23 / 32) +
      x ^ 18 * (661 / 2304) + x ^ 20 * (55 / 384) + x ^ 22 * (25 / 256) by
    funext x
    simp only [yoshidaEndpointOctic, centeredP3]
    ring]
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

end

end ArithmeticHodge.Analysis.YoshidaEndpointOcticPotential
