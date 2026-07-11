import ArithmeticHodge.Analysis.MultiplicativeWeilGammaIntegral
import ArithmeticHodge.Analysis.MultiplicativeWeilArchimedean
import ArithmeticHodge.Analysis.MultiplicativeWeilTranspose

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private def bombieriArchSeriesNumerator
    (f : BombieriTest) (x : ℝ) : ℂ :=
  f x + transpose (f : ℝ → ℂ) x -
    (2 / (x : ℂ)) * f 1

private def bombieriArchSeriesTerm
    (f : BombieriTest) (m : ℕ) (x : ℝ) : ℂ :=
  ((x : ℂ)⁻¹) ^ (2 * m + 1) *
    bombieriArchSeriesNumerator f x

private def bombieriArchSeriesBound
    (f : BombieriTest) (m : ℕ) (x : ℝ) : ℝ :=
  x⁻¹ ^ (2 * m + 1) * ‖bombieriArchSeriesNumerator f x‖

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
  have hx0 : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'
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

private theorem summable_inv_odd_pow_real {x : ℝ} (hx : 1 < x) :
    Summable (fun m : ℕ ↦ x⁻¹ ^ (2 * m + 1)) := by
  simpa only [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (zero_lt_one.trans hx)] using (summable_inv_odd_pow hx).norm

private theorem tsum_inv_odd_pow_real {x : ℝ} (hx : 1 < x) :
    ∑' m : ℕ, x⁻¹ ^ (2 * m + 1) = x / (x ^ 2 - 1) := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hden : x ^ 2 - 1 ≠ 0 := by
    nlinarith [sq_nonneg (x - 1)]
  have hnorm : ‖x⁻¹ ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_pow, abs_inv, abs_of_pos (zero_lt_one.trans hx)]
    have hxinv : x⁻¹ < 1 := inv_lt_one₀ (zero_lt_one.trans hx) |>.2 hx
    have hxinv0 : 0 ≤ x⁻¹ := (inv_pos.mpr (zero_lt_one.trans hx)).le
    nlinarith [mul_self_lt_mul_self hxinv0 hxinv]
  calc
    ∑' m : ℕ, x⁻¹ ^ (2 * m + 1) =
        ∑' m : ℕ, x⁻¹ * ((x⁻¹ ^ 2) ^ m) := by
      apply tsum_congr
      intro m
      rw [pow_add, pow_mul]
      ring
    _ = x⁻¹ * ∑' m : ℕ, ((x⁻¹ ^ 2) ^ m) := tsum_mul_left
    _ = x⁻¹ * (1 - x⁻¹ ^ 2)⁻¹ := by
      rw [tsum_geometric_of_norm_lt_one hnorm]
    _ = x / (x ^ 2 - 1) := by
      field_simp [hx0, hden]

private theorem hasSum_bombieriArchSeriesTerm
    (f : BombieriTest) {x : ℝ} (hx : 1 < x) :
    HasSum (fun m : ℕ ↦ bombieriArchSeriesTerm f m x)
      (bombieriArchIntegrand f x) := by
  have hscalar := (summable_inv_odd_pow hx).hasSum
  rw [tsum_inv_odd_pow hx] at hscalar
  have hmul := hscalar.mul_right (bombieriArchSeriesNumerator f x)
  have hlimit :
      (x : ℂ) / ((x : ℂ) ^ 2 - 1) *
          bombieriArchSeriesNumerator f x =
        bombieriArchIntegrand f x := by
    simp only [bombieriArchSeriesNumerator, bombieriArchIntegrand]
    ring
  rw [← hlimit]
  simpa only [bombieriArchSeriesTerm] using hmul

private theorem bombieriArchSeriesTerm_continuousOn
    (f : BombieriTest) (m : ℕ) :
    ContinuousOn (bombieriArchSeriesTerm f m) (Ioi 1) := by
  have hcast : Continuous (fun x : ℝ ↦ (x : ℂ)) :=
    Complex.ofRealCLM.continuous
  have hinv : ContinuousOn (fun x : ℝ ↦ (x : ℂ)⁻¹) (Ioi 1) :=
    hcast.continuousOn.inv₀ fun x hx ↦
      Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'
  have hcorrection : ContinuousOn
      (fun x : ℝ ↦ (2 / (x : ℂ)) * f 1) (Ioi 1) := by
    simpa only [div_eq_mul_inv] using
      (continuousOn_const.mul hinv).mul continuousOn_const
  have hnumerator : ContinuousOn
      (bombieriArchSeriesNumerator f) (Ioi 1) := by
    exact (f.contDiff.continuous.continuousOn.add
      (BombieriTest.transpose_contDiff f).continuous.continuousOn).sub hcorrection
  exact (hinv.pow (2 * m + 1)).mul hnumerator

private theorem norm_bombieriArchSeriesTerm_eq_bound
    (f : BombieriTest) (m : ℕ) {x : ℝ} (hx : 1 < x) :
    ‖bombieriArchSeriesTerm f m x‖ = bombieriArchSeriesBound f m x := by
  rw [bombieriArchSeriesTerm, bombieriArchSeriesBound, norm_mul,
    norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (zero_lt_one.trans hx)]

private theorem summable_bombieriArchSeriesBound
    (f : BombieriTest) {x : ℝ} (hx : 1 < x) :
    Summable (fun m : ℕ ↦ bombieriArchSeriesBound f m x) := by
  exact (summable_inv_odd_pow_real hx).mul_right
    ‖bombieriArchSeriesNumerator f x‖

private theorem tsum_bombieriArchSeriesBound_eq_norm
    (f : BombieriTest) {x : ℝ} (hx : 1 < x) :
    ∑' m : ℕ, bombieriArchSeriesBound f m x =
      ‖bombieriArchIntegrand f x‖ := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hdenpos : 0 < x ^ 2 - 1 := by
    nlinarith [sq_nonneg (x - 1)]
  calc
    ∑' m : ℕ, bombieriArchSeriesBound f m x =
        ∑' m : ℕ, x⁻¹ ^ (2 * m + 1) *
          ‖bombieriArchSeriesNumerator f x‖ := by
      rfl
    _ =
        (∑' m : ℕ, x⁻¹ ^ (2 * m + 1)) *
          ‖bombieriArchSeriesNumerator f x‖ := tsum_mul_right
    _ = (x / (x ^ 2 - 1)) * ‖bombieriArchSeriesNumerator f x‖ := by
      rw [tsum_inv_odd_pow_real hx]
    _ = ‖bombieriArchIntegrand f x‖ := by
      have harch : bombieriArchIntegrand f x =
          bombieriArchSeriesNumerator f x *
            ((x : ℂ) / ((x : ℂ) ^ 2 - 1)) := by
        simp only [bombieriArchIntegrand, bombieriArchSeriesNumerator]
        ring
      have hcastden : (x : ℂ) ^ 2 - 1 = ((x ^ 2 - 1 : ℝ) : ℂ) := by
        norm_cast
      rw [harch, norm_mul, norm_div, hcastden, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxpos,
        abs_of_pos hdenpos]
      ring

theorem hasSum_integral_bombieriArchSeriesTerm
    (f : BombieriTest) :
    HasSum (fun m : ℕ ↦ ∫ x : ℝ in Ioi 1,
      ((x : ℂ)⁻¹) ^ (2 * m + 1) *
        (f x + transpose (f : ℝ → ℂ) x -
          (2 / (x : ℂ)) * f 1))
      (∫ x : ℝ in Ioi 1, bombieriArchIntegrand f x) := by
  let μ : Measure ℝ := volume.restrict (Ioi 1)
  have hmeas (m : ℕ) :
      AEStronglyMeasurable (bombieriArchSeriesTerm f m) μ := by
    exact (bombieriArchSeriesTerm_continuousOn f m).aestronglyMeasurable
      measurableSet_Ioi
  have hbound (m : ℕ) : ∀ᵐ x : ℝ ∂μ,
      ‖bombieriArchSeriesTerm f m x‖ ≤ bombieriArchSeriesBound f m x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (norm_bombieriArchSeriesTerm_eq_bound f m hx).le
  have hboundSummable : ∀ᵐ x : ℝ ∂μ,
      Summable (fun m : ℕ ↦ bombieriArchSeriesBound f m x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact summable_bombieriArchSeriesBound f hx
  have hboundIntegrable : Integrable
      (fun x : ℝ ↦ ∑' m : ℕ, bombieriArchSeriesBound f m x) μ := by
    refine (bombieriArchIntegrand_integrable f).norm.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (tsum_bombieriArchSeriesBound_eq_norm f hx).symm
  have hlim : ∀ᵐ x : ℝ ∂μ,
      HasSum (fun m : ℕ ↦ bombieriArchSeriesTerm f m x)
        (bombieriArchIntegrand f x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hasSum_bombieriArchSeriesTerm f hx
  have h := MeasureTheory.hasSum_integral_of_dominated_convergence
    (fun m : ℕ ↦ bombieriArchSeriesBound f m) hmeas hbound
      hboundSummable hboundIntegrable hlim
  simpa only [bombieriArchSeriesTerm, bombieriArchSeriesNumerator] using h

theorem tsum_integral_bombieriArchSeriesTerm
    (f : BombieriTest) :
    ∑' m : ℕ, ∫ x : ℝ in Ioi 1,
      ((x : ℂ)⁻¹) ^ (2 * m + 1) *
        (f x + transpose (f : ℝ → ℂ) x -
          (2 / (x : ℂ)) * f 1) =
      ∫ x : ℝ in Ioi 1, bombieriArchIntegrand f x :=
  (hasSum_integral_bombieriArchSeriesTerm f).tsum_eq

#print axioms hasSum_integral_bombieriArchSeriesTerm
#print axioms tsum_integral_bombieriArchSeriesTerm

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
