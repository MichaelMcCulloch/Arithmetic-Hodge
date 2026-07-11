import ArithmeticHodge.Analysis.MultiplicativeWeilGammaIntegral
import ArithmeticHodge.Analysis.MultiplicativeWeilArchimedean

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private theorem summable_inv_odd_pow {x : ℝ} (hx : 1 < x) :
    Summable (fun m : ℕ ↦ ((x : ℂ)⁻¹) ^ (2 * m + 1)) := by
  have hnorm : ‖(x : ℂ)⁻¹ ^ 2‖ < 1 := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (zero_lt_one.trans hx)]
    have hxinv : x⁻¹ < 1 := inv_lt_one₀ (zero_lt_one.trans hx) |>.2 hx
    have hxinv0 : 0 ≤ x⁻¹ := (inv_pos.mpr (zero_lt_one.trans hx)).le
    nlinarith [mul_self_lt_mul_self hxinv0 hxinv]
  have hgeom := summable_geometric_of_norm_lt_one hnorm
  have hmul := hgeom.mul_left ((x : ℂ)⁻¹)
  refine hmul.congr ?_
  intro m
  rw [pow_add, pow_mul]
  ring

private theorem tsum_inv_odd_pow {x : ℝ} (hx : 1 < x) :
    ∑' m : ℕ, ((x : ℂ)⁻¹) ^ (2 * m + 1) =
      (x : ℂ) / ((x : ℂ) ^ 2 - 1) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'
  have hden : (x : ℂ) ^ 2 - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hr : x ^ 2 = 1 := by exact_mod_cast h
    nlinarith [sq_nonneg (x - 1)]
  have hnorm : ‖(x : ℂ)⁻¹ ^ 2‖ < 1 := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (zero_lt_one.trans hx)]
    have hxinv : x⁻¹ < 1 := inv_lt_one₀ (zero_lt_one.trans hx) |>.2 hx
    have hxinv0 : 0 ≤ x⁻¹ := (inv_pos.mpr (zero_lt_one.trans hx)).le
    nlinarith [mul_self_lt_mul_self hxinv0 hxinv]
  calc
    ∑' m : ℕ, ((x : ℂ)⁻¹) ^ (2 * m + 1) =
        ∑' m : ℕ, (x : ℂ)⁻¹ * (((x : ℂ)⁻¹ ^ 2) ^ m) := by
      apply tsum_congr
      intro m
      rw [pow_add, pow_mul]
      ring
    _ = (x : ℂ)⁻¹ * ∑' m : ℕ, (((x : ℂ)⁻¹ ^ 2) ^ m) :=
      tsum_mul_left
    _ = (x : ℂ)⁻¹ * (1 - (x : ℂ)⁻¹ ^ 2)⁻¹ := by
      rw [tsum_geometric_of_norm_lt_one hnorm]
    _ = (x : ℂ) / ((x : ℂ) ^ 2 - 1) := by
      field_simp [hx0, hden]

private theorem tsum_odd_kernel_mul_archNumerator
    (f : BombieriTest) {x : ℝ} (hx : 1 < x) :
    ∑' m : ℕ,
        ((x : ℂ)⁻¹) ^ (2 * m + 1) *
          (f x + transpose (f : ℝ → ℂ) x -
            (2 / (x : ℂ)) * f 1) =
      bombieriArchIntegrand f x := by
  let G : ℂ := f x + transpose (f : ℝ → ℂ) x -
    (2 / (x : ℂ)) * f 1
  have hs := summable_inv_odd_pow hx
  calc
    ∑' m : ℕ, ((x : ℂ)⁻¹) ^ (2 * m + 1) * G =
        (∑' m : ℕ, ((x : ℂ)⁻¹) ^ (2 * m + 1)) * G :=
      hs.tsum_mul_right G
    _ = (x : ℂ) / ((x : ℂ) ^ 2 - 1) * G := by
      rw [tsum_inv_odd_pow hx]
    _ = bombieriArchIntegrand f x := by
      simp only [bombieriArchIntegrand, G]
      ring

#print axioms summable_inv_odd_pow
#print axioms tsum_inv_odd_pow
#print axioms tsum_odd_kernel_mul_archNumerator

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
