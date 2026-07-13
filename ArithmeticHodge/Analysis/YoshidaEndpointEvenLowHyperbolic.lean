import ArithmeticHodge.Analysis.YoshidaConstantBounds
import ArithmeticHodge.Analysis.YoshidaEndpointEvenStructuralReduction
import ArithmeticHodge.Analysis.YoshidaEndpointHyperbolicBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenLowHyperbolic

open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaConstantBounds

noncomputable section

/-!
# Exact low even hyperbolic moments

The rank-two hyperbolic term has an exact rank-one restriction to the even
sector.  This module evaluates its constant and centered degree-two moments
by structural antiderivatives, with no numerical approximation.
-/

/-- Exact constant moment of the scaled even hyperbolic weight. -/
theorem integral_cosh_scaled {a : ℝ} (ha : a ≠ 0) :
    (∫ x : ℝ in -1..1, Real.cosh (a * x / 2)) =
      4 * Real.sinh (a / 2) / a := by
  let F : ℝ → ℝ := fun x ↦ 2 * Real.sinh (a * x / 2) / a
  have hderiv (x : ℝ) :
      HasDerivAt F (Real.cosh (a * x / 2)) x := by
    have hlin : HasDerivAt (fun y : ℝ ↦ a * y / 2) (a / 2) x := by
      simpa only [mul_one] using
        ((hasDerivAt_id x).const_mul a).div_const 2
    have hsinh := (Real.hasDerivAt_sinh (a * x / 2)).comp x hlin
    dsimp only [F]
    convert (hsinh.const_mul 2).div_const a using 1
    field_simp [ha]
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx ↦ hderiv x)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
  rw [hint]
  dsimp only [F]
  rw [show a * (1 : ℝ) / 2 = a / 2 by ring,
    show a * (-1 : ℝ) / 2 = -(a / 2) by ring, Real.sinh_neg]
  field_simp [ha]
  ring

/-- Exact quadratic moment of the scaled even hyperbolic weight. -/
theorem integral_sq_mul_cosh_scaled {a : ℝ} (ha : a ≠ 0) :
    (∫ x : ℝ in -1..1, x ^ 2 * Real.cosh (a * x / 2)) =
      4 * Real.sinh (a / 2) / a -
        16 * Real.cosh (a / 2) / a ^ 2 +
        32 * Real.sinh (a / 2) / a ^ 3 := by
  let F : ℝ → ℝ := fun x ↦
    2 * x ^ 2 * Real.sinh (a * x / 2) / a -
      8 * x * Real.cosh (a * x / 2) / a ^ 2 +
      16 * Real.sinh (a * x / 2) / a ^ 3
  have hderiv (x : ℝ) :
      HasDerivAt F (x ^ 2 * Real.cosh (a * x / 2)) x := by
    have hlin : HasDerivAt (fun y : ℝ ↦ a * y / 2) (a / 2) x := by
      simpa only [mul_one] using
        ((hasDerivAt_id x).const_mul a).div_const 2
    have hsinh := (Real.hasDerivAt_sinh (a * x / 2)).comp x hlin
    have hcosh := (Real.hasDerivAt_cosh (a * x / 2)).comp x hlin
    dsimp only [F]
    convert (((((hasDerivAt_id x).pow 2).const_mul 2).mul hsinh).div_const a)
      |>.sub ((((hasDerivAt_id x).const_mul 8).mul hcosh).div_const (a ^ 2))
      |>.add ((hsinh.const_mul 16).div_const (a ^ 3)) using 1
    simp only [Function.comp_apply, id_eq, Pi.pow_apply, Nat.cast_ofNat]
    field_simp [ha]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx ↦ hderiv x)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
  rw [hint]
  dsimp only [F]
  rw [show a * (1 : ℝ) / 2 = a / 2 by ring,
    show a * (-1 : ℝ) / 2 = -(a / 2) by ring,
    Real.sinh_neg, Real.cosh_neg]
  norm_num
  ring

/-- Exact centered degree-two moment of the scaled even hyperbolic weight. -/
theorem integral_cosh_scaled_mul_centeredEvenP2 {a : ℝ} (ha : a ≠ 0) :
    (∫ x : ℝ in -1..1,
      Real.cosh (a * x / 2) * centeredEvenP2 x) =
        4 * ((a ^ 2 + 12) * Real.sinh (a / 2) -
          6 * a * Real.cosh (a / 2)) / a ^ 3 := by
  rw [show (fun x : ℝ ↦
      Real.cosh (a * x / 2) * centeredEvenP2 x) =
      fun x ↦ (3 / 2 : ℝ) *
          (x ^ 2 * Real.cosh (a * x / 2)) -
        (1 / 2 : ℝ) * Real.cosh (a * x / 2) by
    funext x
    unfold centeredEvenP2
    ring]
  have hsq : IntervalIntegrable
      (fun x : ℝ ↦ x ^ 2 * Real.cosh (a * x / 2)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hzero : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (a * x / 2)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_sub (hsq.const_mul (3 / 2 : ℝ))
      (hzero.const_mul (1 / 2 : ℝ)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_sq_mul_cosh_scaled ha,
    integral_cosh_scaled ha]
  field_simp [ha]
  ring

/-- Exact endpoint constant moment of the even hyperbolic weight. -/
theorem integral_yoshidaEndpoint_cosh :
    (∫ x : ℝ in -1..1,
      Real.cosh (yoshidaEndpointA * x / 2)) =
        4 * Real.sinh (yoshidaEndpointA / 2) / yoshidaEndpointA :=
  integral_cosh_scaled yoshidaEndpointA_pos.ne'

/-- Exact endpoint centered degree-two moment of the even hyperbolic weight. -/
theorem integral_yoshidaEndpoint_cosh_mul_centeredEvenP2 :
    (∫ x : ℝ in -1..1,
      Real.cosh (yoshidaEndpointA * x / 2) * centeredEvenP2 x) =
        4 * ((yoshidaEndpointA ^ 2 + 12) *
            Real.sinh (yoshidaEndpointA / 2) -
          6 * yoshidaEndpointA * Real.cosh (yoshidaEndpointA / 2)) /
            yoshidaEndpointA ^ 3 :=
  integral_cosh_scaled_mul_centeredEvenP2 yoshidaEndpointA_pos.ne'

/-- The endpoint constant hyperbolic moment is strictly larger than its
constant-weight value. -/
theorem two_lt_integral_yoshidaEndpoint_cosh :
    (2 : ℝ) < ∫ x : ℝ in -1..1,
      Real.cosh (yoshidaEndpointA * x / 2) := by
  rw [integral_yoshidaEndpoint_cosh]
  have ha := yoshidaEndpointA_pos
  have hsinh : yoshidaEndpointA / 2 <
      Real.sinh (yoshidaEndpointA / 2) :=
    Real.self_lt_sinh_iff.mpr (half_pos ha)
  rw [lt_div_iff₀ ha]
  nlinarith

private theorem one_add_sq_div_two_le_cosh (x : ℝ) :
    1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have hnonneg (y : ℝ) (hy : 0 ≤ y) :
      1 + y ^ 2 / 2 ≤ Real.cosh y := by
    let q : ℝ → ℝ := fun z ↦ Real.cosh z - 1 - z ^ 2 / 2
    have hderiv (z : ℝ) : HasDerivAt q (Real.sinh z - z) z := by
      dsimp only [q]
      convert ((Real.hasDerivAt_cosh z).sub (hasDerivAt_const z 1)).sub
        (((hasDerivAt_id z).pow 2).div_const 2) using 1
      simp only [id_eq, Nat.cast_ofNat]
      ring
    have hcont : Continuous q := by
      dsimp only [q]
      fun_prop
    have hmono : MonotoneOn q (Icc 0 y) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 y) hcont.continuousOn
      · intro z _hz
        exact (hderiv z).differentiableAt.differentiableWithinAt
      · intro z hz
        rw [(hderiv z).deriv]
        exact sub_nonneg.mpr
          (Real.self_le_sinh_iff.mpr (interior_subset hz).1)
    have hq := hmono (show (0 : ℝ) ∈ Icc 0 y by exact ⟨le_rfl, hy⟩)
      (show y ∈ Icc 0 y by exact ⟨hy, le_rfl⟩) hy
    dsimp only [q] at hq
    norm_num at hq
    linarith
  by_cases hx : 0 ≤ x
  · exact hnonneg x hx
  · have h := hnonneg (-x) (by linarith)
    simpa only [Real.cosh_neg, neg_sq] using h

/-- A transparent lower bound for the constant hyperbolic moment, obtained
from the quadratic Taylor lower bound for `cosh`. -/
theorem two_hundred_one_div_hundred_lt_integral_yoshidaEndpoint_cosh :
    (201 / 100 : ℝ) < ∫ x : ℝ in -1..1,
      Real.cosh (yoshidaEndpointA * x / 2) := by
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦ 1 + (yoshidaEndpointA * x / 2) ^ 2 / 2)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hcosh : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hle :
      (∫ x : ℝ in -1..1,
        1 + (yoshidaEndpointA * x / 2) ^ 2 / 2) ≤
        ∫ x : ℝ in -1..1,
          Real.cosh (yoshidaEndpointA * x / 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hpoly hcosh
    intro x _hx
    exact one_add_sq_div_two_le_cosh (yoshidaEndpointA * x / 2)
  have hpolyExact :
      (∫ x : ℝ in -1..1,
        1 + (yoshidaEndpointA * x / 2) ^ 2 / 2) =
          2 + yoshidaEndpointA ^ 2 / 12 := by
    rw [show (fun x : ℝ ↦
        1 + (yoshidaEndpointA * x / 2) ^ 2 / 2) =
        fun x ↦ 1 + (yoshidaEndpointA ^ 2 / 8) * x ^ 2 by
      funext x
      ring]
    rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable continuous_const (-1) 1)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  have hlog := strict_log_two_bounds.1
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : (6931 / 10000 : ℝ) ^ 2 < (Real.log 2) ^ 2 := by
    have hprod : 0 < (Real.log 2 - 6931 / 10000) *
        (Real.log 2 + 6931 / 10000) := by
      apply mul_pos
      · linarith
      · positivity
    nlinarith
  have hmargin : (1 / 100 : ℝ) < (Real.log 2) ^ 2 / 48 := by
    norm_num at hsq ⊢
    nlinarith
  rw [hpolyExact] at hle
  have htarget : (201 / 100 : ℝ) <
      2 + yoshidaEndpointA ^ 2 / 12 := by
    rw [show yoshidaEndpointA ^ 2 / 12 = (Real.log 2) ^ 2 / 48 by
      unfold yoshidaEndpointA
      ring]
    linarith
  exact htarget.trans_le hle

private theorem log_two_lt_one_hundred_thirty_nine_div_two_hundred :
    Real.log 2 < (139 / 200 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem cosh_yoshidaEndpointA_half_lt_sixty_one_div_sixty :
    Real.cosh (yoshidaEndpointA / 2) < (61 / 60 : ℝ) := by
  let t : ℝ := yoshidaEndpointA / 2
  have ht0 : 0 ≤ t := (half_pos yoshidaEndpointA_pos).le
  have ht : t < (139 / 800 : ℝ) := by
    dsimp only [t]
    unfold yoshidaEndpointA
    linarith [log_two_lt_one_hundred_thirty_nine_div_two_hundred]
  have hprod : 0 < ((139 / 800 : ℝ) - t) *
      ((139 / 800 : ℝ) + t) := by
    apply mul_pos
    · linarith
    · positivity
  have hsq : t ^ 2 < (139 / 800 : ℝ) ^ 2 := by
    nlinarith
  let u : ℝ := t ^ 2 / 2
  have hu0 : 0 ≤ u := by
    dsimp only [u]
    positivity
  have hu61 : u < (1 / 61 : ℝ) := by
    dsimp only [u]
    nlinarith
  have hu1 : u < 1 := lt_trans hu61 (by norm_num)
  have hexp : Real.exp u ≤ 1 / (1 - u) :=
    Real.exp_bound_div_one_sub_of_interval hu0 hu1
  have hfrac : 1 / (1 - u) < (61 / 60 : ℝ) := by
    rw [div_lt_iff₀ (sub_pos.mpr hu1)]
    nlinarith
  have hcosh : Real.cosh t ≤ Real.exp u := by
    dsimp only [u]
    exact Real.cosh_le_exp_half_sq t
  dsimp only [t] at hcosh ⊢
  exact hcosh.trans_lt (hexp.trans_lt hfrac)

/-- A short structural rational upper bound for the endpoint constant
hyperbolic moment. -/
theorem integral_yoshidaEndpoint_cosh_lt_sixty_one_div_thirty :
    (∫ x : ℝ in -1..1,
      Real.cosh (yoshidaEndpointA * x / 2)) < (61 / 30 : ℝ) := by
  have hweight : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hconst : IntervalIntegrable
      (fun _x : ℝ ↦ Real.cosh (yoshidaEndpointA / 2))
      volume (-1) 1 :=
    Continuous.intervalIntegrable continuous_const (-1) 1
  have hle :
      (∫ x : ℝ in -1..1,
        Real.cosh (yoshidaEndpointA * x / 2)) ≤
        ∫ _x : ℝ in -1..1, Real.cosh (yoshidaEndpointA / 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hweight hconst
    intro x hx
    apply Real.cosh_le_cosh.mpr
    have hxabs : |x| ≤ 1 := abs_le.mpr hx
    calc
      |yoshidaEndpointA * x / 2| =
          yoshidaEndpointA * |x| / 2 := by
        rw [abs_div, abs_mul, abs_of_nonneg yoshidaEndpointA_pos.le]
        norm_num
      _ ≤ yoshidaEndpointA * 1 / 2 := by
        have hmul := mul_le_mul_of_nonneg_left hxabs yoshidaEndpointA_pos.le
        linarith
      _ = |yoshidaEndpointA / 2| := by
        rw [abs_div, abs_of_nonneg yoshidaEndpointA_pos.le]
        norm_num
  have hcosh := cosh_yoshidaEndpointA_half_lt_sixty_one_div_sixty
  norm_num at hle
  nlinarith

private theorem yoshidaEndpoint_cosh_p2_numerator_bounds :
    0 < (yoshidaEndpointA ^ 2 + 12) *
          Real.sinh (yoshidaEndpointA / 2) -
        6 * yoshidaEndpointA * Real.cosh (yoshidaEndpointA / 2) ∧
      (yoshidaEndpointA ^ 2 + 12) *
          Real.sinh (yoshidaEndpointA / 2) -
        6 * yoshidaEndpointA * Real.cosh (yoshidaEndpointA / 2) ≤
          yoshidaEndpointA ^ 5 *
            Real.cosh (yoshidaEndpointA / 2) / 120 := by
  let h : ℝ → ℝ := fun x ↦ x * Real.cosh x - Real.sinh x
  have hhderiv (x : ℝ) : HasDerivAt h (x * Real.sinh x) x := by
    dsimp only [h]
    convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x) using 1
    simp only [id_eq]
    ring
  have hhcont : Continuous h := by
    dsimp only [h]
    fun_prop
  have hhstrict : StrictMonoOn h (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hhcont.continuousOn
    intro x hx
    rw [(hhderiv x).deriv]
    have hx0 : 0 < x := by
      simpa only [interior_Ici, mem_Ioi] using hx
    exact mul_pos hx0 (Real.sinh_pos_iff.mpr hx0)
  have hhpos {x : ℝ} (hx : 0 < x) : 0 < h x := by
    have hstrict := hhstrict (show (0 : ℝ) ∈ Ici 0 by simp)
      (show x ∈ Ici 0 by exact hx.le) hx
    simpa only [h, zero_mul, Real.sinh_zero, sub_zero] using hstrict
  have hhnonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ h x := by
    rcases hx.eq_or_lt with rfl | hxpos
    · norm_num [h]
    · exact (hhpos hxpos).le
  let g : ℝ → ℝ := fun x ↦
    (x ^ 2 + 3) * Real.sinh x - 3 * x * Real.cosh x
  have hgderiv (x : ℝ) : HasDerivAt g (x * h x) x := by
    have hpoly : HasDerivAt (fun y : ℝ ↦ y ^ 2 + 3) (2 * x) x := by
      convert ((hasDerivAt_id x).pow 2).add (hasDerivAt_const x 3) using 1
      simp only [id_eq, Nat.cast_ofNat]
      ring
    dsimp only [g]
    convert (hpoly.mul (Real.hasDerivAt_sinh x)).sub
      ((((hasDerivAt_id x).const_mul 3).mul
        (Real.hasDerivAt_cosh x))) using 1
    simp only [id_eq]
    dsimp only [h]
    ring
  have hgcont : Continuous g := by
    dsimp only [g]
    fun_prop
  have hgstrict : StrictMonoOn g (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hgcont.continuousOn
    intro x hx
    rw [(hgderiv x).deriv]
    have hx0 : 0 < x := by
      simpa only [interior_Ici, mem_Ioi] using hx
    exact mul_pos hx0 (hhpos hx0)
  have ht : 0 < yoshidaEndpointA / 2 := half_pos yoshidaEndpointA_pos
  have hgt := hgstrict (show (0 : ℝ) ∈ Ici 0 by simp)
    (show yoshidaEndpointA / 2 ∈ Ici 0 by exact ht.le) ht
  have hgtpos : 0 < g (yoshidaEndpointA / 2) := by
    dsimp only [g] at hgt ⊢
    norm_num at hgt
    linarith
  let q : ℝ → ℝ := fun x ↦ x ^ 3 * Real.cosh x / 3 - h x
  have hqderiv (x : ℝ) : HasDerivAt q
      (x * h x + x ^ 3 * Real.sinh x / 3) x := by
    dsimp only [q]
    convert ((((hasDerivAt_id x).pow 3).mul
      (Real.hasDerivAt_cosh x)).div_const 3).sub (hhderiv x) using 1
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat]
    dsimp only [h]
    ring
  have hqcont : Continuous q := by
    dsimp only [q, h]
    fun_prop
  have hqmono : MonotoneOn q (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hqcont.continuousOn
    · intro x _hx
      exact (hqderiv x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hqderiv x).deriv]
      have hx0 : 0 < x := by
        simpa only [interior_Ici, mem_Ioi] using hx
      have hsinh0 : 0 ≤ Real.sinh x := (Real.sinh_pos_iff.mpr hx0).le
      exact add_nonneg (mul_nonneg hx0.le (hhnonneg hx0.le))
        (div_nonneg (mul_nonneg (pow_nonneg hx0.le 3) hsinh0) (by norm_num))
  have hhupper {x : ℝ} (hx : 0 ≤ x) :
      h x ≤ x ^ 3 * Real.cosh x / 3 := by
    have hqval := hqmono (show (0 : ℝ) ∈ Ici 0 by simp)
      (show x ∈ Ici 0 by exact hx) hx
    dsimp only [q] at hqval
    norm_num [h] at hqval
    linarith
  let r : ℝ → ℝ := fun x ↦ x ^ 5 * Real.cosh x / 15 - g x
  have hrderiv (x : ℝ) : HasDerivAt r
      (x ^ 4 * Real.cosh x / 3 + x ^ 5 * Real.sinh x / 15 -
        x * h x) x := by
    dsimp only [r]
    convert ((((hasDerivAt_id x).pow 5).mul
      (Real.hasDerivAt_cosh x)).div_const 15).sub (hgderiv x) using 1
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat]
    ring
  have hrcont : Continuous r := by
    dsimp only [r, g]
    fun_prop
  have hrmono : MonotoneOn r (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hrcont.continuousOn
    · intro x _hx
      exact (hrderiv x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hrderiv x).deriv]
      have hx0 : 0 < x := by
        simpa only [interior_Ici, mem_Ioi] using hx
      have hmul := mul_le_mul_of_nonneg_left (hhupper hx0.le) hx0.le
      have hextra : 0 ≤ x ^ 5 * Real.sinh x / 15 := by positivity
      nlinarith
  have hgupper : g (yoshidaEndpointA / 2) ≤
      (yoshidaEndpointA / 2) ^ 5 *
        Real.cosh (yoshidaEndpointA / 2) / 15 := by
    have hrval := hrmono (show (0 : ℝ) ∈ Ici 0 by simp)
      (show yoshidaEndpointA / 2 ∈ Ici 0 by exact ht.le) ht.le
    dsimp only [r, g] at hrval ⊢
    norm_num at hrval
    linarith
  have hnumerator :
      (yoshidaEndpointA ^ 2 + 12) *
          Real.sinh (yoshidaEndpointA / 2) -
        6 * yoshidaEndpointA * Real.cosh (yoshidaEndpointA / 2) =
          4 * g (yoshidaEndpointA / 2) := by
    dsimp only [g]
    ring
  constructor
  · rw [hnumerator]
    positivity
  · rw [hnumerator]
    calc
      4 * g (yoshidaEndpointA / 2) ≤
          4 * ((yoshidaEndpointA / 2) ^ 5 *
            Real.cosh (yoshidaEndpointA / 2) / 15) := by
        gcongr
      _ = yoshidaEndpointA ^ 5 *
          Real.cosh (yoshidaEndpointA / 2) / 120 := by ring

/-- The endpoint centered degree-two hyperbolic moment is strictly positive. -/
theorem integral_yoshidaEndpoint_cosh_mul_centeredEvenP2_pos :
    0 < ∫ x : ℝ in -1..1,
      Real.cosh (yoshidaEndpointA * x / 2) * centeredEvenP2 x := by
  rw [integral_yoshidaEndpoint_cosh_mul_centeredEvenP2]
  exact div_pos
    (mul_pos (by norm_num) yoshidaEndpoint_cosh_p2_numerator_bounds.1)
    (pow_pos yoshidaEndpointA_pos 3)

/-- A sharp rational upper bound for the endpoint centered degree-two
hyperbolic moment. -/
theorem integral_yoshidaEndpoint_cosh_mul_centeredEvenP2_lt_one_div_two_hundred_forty_five :
    (∫ x : ℝ in -1..1,
      Real.cosh (yoshidaEndpointA * x / 2) * centeredEvenP2 x) <
        (1 / 245 : ℝ) := by
  have hC2le :
      (∫ x : ℝ in -1..1,
        Real.cosh (yoshidaEndpointA * x / 2) * centeredEvenP2 x) ≤
          yoshidaEndpointA ^ 2 *
            Real.cosh (yoshidaEndpointA / 2) / 30 := by
    rw [integral_yoshidaEndpoint_cosh_mul_centeredEvenP2]
    rw [div_le_iff₀ (pow_pos yoshidaEndpointA_pos 3)]
    calc
      4 * ((yoshidaEndpointA ^ 2 + 12) *
            Real.sinh (yoshidaEndpointA / 2) -
          6 * yoshidaEndpointA * Real.cosh (yoshidaEndpointA / 2)) ≤
          4 * (yoshidaEndpointA ^ 5 *
            Real.cosh (yoshidaEndpointA / 2) / 120) := by
        gcongr
        exact yoshidaEndpoint_cosh_p2_numerator_bounds.2
      _ = yoshidaEndpointA ^ 2 *
          Real.cosh (yoshidaEndpointA / 2) / 30 *
            yoshidaEndpointA ^ 3 := by ring
  have haUpper : yoshidaEndpointA < (1733 / 5000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_bounds.2]
  have haSqUpper : yoshidaEndpointA ^ 2 < (1733 / 5000 : ℝ) ^ 2 := by
    have hprod : 0 < ((1733 / 5000 : ℝ) - yoshidaEndpointA) *
        ((1733 / 5000 : ℝ) + yoshidaEndpointA) := by
      apply mul_pos
      · linarith
      · nlinarith [yoshidaEndpointA_pos]
    nlinarith
  have hcosh := cosh_yoshidaEndpointA_half_lt_sixty_one_div_sixty
  have hprodUpper :
      yoshidaEndpointA ^ 2 * Real.cosh (yoshidaEndpointA / 2) <
        (1733 / 5000 : ℝ) ^ 2 * (61 / 60 : ℝ) := by
    calc
      yoshidaEndpointA ^ 2 * Real.cosh (yoshidaEndpointA / 2) <
          yoshidaEndpointA ^ 2 * (61 / 60 : ℝ) := by
        exact mul_lt_mul_of_pos_left hcosh (sq_pos_of_pos yoshidaEndpointA_pos)
      _ < (1733 / 5000 : ℝ) ^ 2 * (61 / 60 : ℝ) := by
        exact mul_lt_mul_of_pos_right haSqUpper (by norm_num)
  have hrat : yoshidaEndpointA ^ 2 *
      Real.cosh (yoshidaEndpointA / 2) / 30 < (1 / 245 : ℝ) := by
    norm_num at hprodUpper ⊢
    nlinarith
  exact hC2le.trans_lt hrat

/-- The odd hyperbolic moment vanishes on the constant and centered
degree-two even modes. -/
theorem integral_sinh_scaled_mul_zero_two_eq_zero
    (a c b : ℝ) :
    (∫ x : ℝ in -1..1,
      Real.sinh (a * x / 2) * (c + b * centeredEvenP2 x)) = 0 := by
  let f : ℝ → ℝ := fun x ↦
    Real.sinh (a * x / 2) * (c + b * centeredEvenP2 x)
  have hfOdd : Function.Odd f := by
    intro x
    dsimp only [f]
    rw [show a * -x / 2 = -(a * x / 2) by ring, Real.sinh_neg]
    unfold centeredEvenP2
    ring
  have hchange := intervalIntegral.integral_comp_neg
    (f := f) (a := (-1 : ℝ)) (b := 1)
  have hneg : (∫ x : ℝ in -1..1, f (-x)) =
      -(∫ x : ℝ in -1..1, f x) := by
    rw [show (fun x : ℝ ↦ f (-x)) = fun x ↦ -f x by
      funext x
      exact hfOdd x,
      intervalIntegral.integral_neg]
  norm_num only [neg_neg] at hchange
  rw [hneg] at hchange
  change (∫ x : ℝ in -1..1, f x) = 0
  linarith

/-- The exact hyperbolic Gram form on the constant and centered degree-two
modes is rank one. -/
theorem yoshidaEndpointHyperbolicQuadratic_zero_two_eq (c b : ℝ) :
    yoshidaEndpointHyperbolicQuadratic
        (fun x ↦ ((c + b * centeredEvenP2 x : ℝ) : ℂ)) =
      2 * yoshidaEndpointA *
        (c * (4 * Real.sinh (yoshidaEndpointA / 2) /
            yoshidaEndpointA) +
          b * (4 * ((yoshidaEndpointA ^ 2 + 12) *
                Real.sinh (yoshidaEndpointA / 2) -
              6 * yoshidaEndpointA *
                Real.cosh (yoshidaEndpointA / 2)) /
            yoshidaEndpointA ^ 3)) ^ 2 := by
  have hC0 : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hC2 : IntervalIntegrable
      (fun x : ℝ ↦
        Real.cosh (yoshidaEndpointA * x / 2) * centeredEvenP2 x)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredEvenP2
    fun_prop
  have hCReal :
      (∫ x : ℝ in -1..1,
        Real.cosh (yoshidaEndpointA * x / 2) *
          (c + b * centeredEvenP2 x)) =
        c * (4 * Real.sinh (yoshidaEndpointA / 2) /
            yoshidaEndpointA) +
          b * (4 * ((yoshidaEndpointA ^ 2 + 12) *
                Real.sinh (yoshidaEndpointA / 2) -
              6 * yoshidaEndpointA *
                Real.cosh (yoshidaEndpointA / 2)) /
            yoshidaEndpointA ^ 3) := by
    rw [show (fun x : ℝ ↦
        Real.cosh (yoshidaEndpointA * x / 2) *
          (c + b * centeredEvenP2 x)) =
        fun x ↦ c * Real.cosh (yoshidaEndpointA * x / 2) +
          b * (Real.cosh (yoshidaEndpointA * x / 2) *
            centeredEvenP2 x) by
      funext x
      ring]
    rw [intervalIntegral.integral_add (hC0.const_mul c) (hC2.const_mul b),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_yoshidaEndpoint_cosh,
      integral_yoshidaEndpoint_cosh_mul_centeredEvenP2]
  have hSReal :
      (∫ x : ℝ in -1..1,
        Real.sinh (yoshidaEndpointA * x / 2) *
          (c + b * centeredEvenP2 x)) = 0 :=
    integral_sinh_scaled_mul_zero_two_eq_zero yoshidaEndpointA c b
  have hCComplex :
      (∫ x : ℝ in -1..1,
        (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) *
          ((c + b * centeredEvenP2 x : ℝ) : ℂ)) =
        ((c * (4 * Real.sinh (yoshidaEndpointA / 2) /
              yoshidaEndpointA) +
            b * (4 * ((yoshidaEndpointA ^ 2 + 12) *
                  Real.sinh (yoshidaEndpointA / 2) -
                6 * yoshidaEndpointA *
                  Real.cosh (yoshidaEndpointA / 2)) /
              yoshidaEndpointA ^ 3) : ℝ) : ℂ) := by
    rw [← hCReal, ← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    norm_num
  have hSComplex :
      (∫ x : ℝ in -1..1,
        (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) *
          ((c + b * centeredEvenP2 x : ℝ) : ℂ)) = 0 := by
    rw [← Complex.ofReal_zero, ← hSReal,
      ← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    norm_num
  unfold yoshidaEndpointHyperbolicQuadratic
  rw [hCComplex, hSComplex, Complex.normSq_ofReal]
  simp only [Complex.normSq_apply, Complex.zero_re, Complex.zero_im,
    zero_mul, add_zero, sub_zero]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenLowHyperbolic
