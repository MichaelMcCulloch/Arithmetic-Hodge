import ArithmeticHodge.Analysis.MultiplicativeWeilZeroPowerSummability

set_option autoImplicit false

open Complex Filter Real Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- A fixed power of `log (x+2)` is absorbed by a half power of `x` for
`x ≥ 1`, with an explicit (deliberately coarse) constant. -/
theorem log_add_two_pow_le_const_mul_sqrt
    (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    Real.log (x + 2) ^ m ≤
      (2 * (m + 1 : ℝ)) ^ m * 3 ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
  let e : ℝ := 1 / (2 * (m + 1 : ℝ))
  have he : 0 < e := by
    dsimp only [e]
    positivity
  have hbase : 1 ≤ x + 2 := by linarith
  have hlog0 : 0 ≤ Real.log (x + 2) := Real.log_nonneg hbase
  have hlog := Real.log_le_rpow_div (show 0 ≤ x + 2 by linarith) he
  have hpow := pow_le_pow_left₀ hlog0 hlog m
  have hem : e * m ≤ 1 / 2 := by
    dsimp only [e]
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hden : 0 < 2 * ((m : ℝ) + 1) := by positivity
    field_simp
    nlinarith
  have hxp : (x + 2) ^ (e * m) ≤ (x + 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase hem
  have hxthree : x + 2 ≤ 3 * x := by linarith
  have hsqrt : (x + 2) ^ (1 / 2 : ℝ) ≤
      3 ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
    calc
      (x + 2) ^ (1 / 2 : ℝ) ≤ (3 * x) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by linarith) hxthree (by norm_num)
      _ = 3 ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (zero_le_one.trans hx)]
  calc
    Real.log (x + 2) ^ m ≤ (((x + 2) ^ e) / e) ^ m := hpow
    _ = (2 * (m + 1 : ℝ)) ^ m * (x + 2) ^ (e * m) := by
      rw [div_pow, ← Real.rpow_natCast ((x + 2) ^ e) m,
        ← Real.rpow_mul (by positivity)]
      have heinv : e⁻¹ = 2 * (m + 1 : ℝ) := by
        dsimp only [e]
        field_simp
      rw [div_eq_mul_inv, ← inv_pow, heinv]
      ring
    _ ≤ (2 * (m + 1 : ℝ)) ^ m * (x + 2) ^ (1 / 2 : ℝ) := by
      gcongr
    _ ≤ (2 * (m + 1 : ℝ)) ^ m *
        (3 ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by
      gcongr
    _ = _ := by ring

/-- The logarithmically weighted inverse square is bounded by an inverse
`3/2` power once `x ≥ 1`. -/
theorem log_add_two_pow_mul_inv_sq_le
    (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    Real.log (x + 2) ^ m * x⁻¹ ^ 2 ≤
      ((2 * (m + 1 : ℝ)) ^ m * 3 ^ (1 / 2 : ℝ)) *
        x⁻¹ ^ (3 / 2 : ℝ) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlog := log_add_two_pow_le_const_mul_sqrt m hx
  have hmul := mul_le_mul_of_nonneg_right hlog (sq_nonneg x⁻¹)
  have hrpowMul : x ^ (1 / 2 : ℝ) * x ^ (3 / 2 : ℝ) = x ^ 2 := by
    rw [← Real.rpow_add hx0]
    norm_num [Real.rpow_two]
  have hcore : x ^ (1 / 2 : ℝ) * x⁻¹ ^ 2 =
      x⁻¹ ^ (3 / 2 : ℝ) := by
    rw [Real.inv_rpow hx0.le]
    have hxpow : x ^ (3 / 2 : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos hx0 _).ne'
    field_simp [hx0.ne', hxpow]
    simpa only [pow_two] using hrpowMul
  calc
    Real.log (x + 2) ^ m * x⁻¹ ^ 2 ≤
        ((2 * (m + 1 : ℝ)) ^ m * 3 ^ (1 / 2 : ℝ) *
          x ^ (1 / 2 : ℝ)) * x⁻¹ ^ 2 := hmul
    _ = ((2 * (m + 1 : ℝ)) ^ m * 3 ^ (1 / 2 : ℝ)) *
        x⁻¹ ^ (3 / 2 : ℝ) := by
      rw [← hcore]
      ring

/-- Every polynomial logarithmic weight remains summable against the
inverse-square exact zeta-zero divisor. -/
theorem ZetaZeroEnumeration.summable_log_norm_add_two_pow_mul_inv_sq
    (zeros : ZetaZeroEnumeration) (m : ℕ) :
    Summable (fun k ↦
      Real.log (‖(zeros.zero k).val‖ + 2) ^ m *
        ‖(zeros.zero k).val‖⁻¹ ^ 2) := by
  let p : ℝ := 3 / 2
  let a : ℕ → ℝ := fun k ↦ ‖(zeros.zero k).val‖⁻¹ ^ p
  have ha : Summable a := by
    simpa only [a, p] using
      zeros.summable_inv_norm_rpow (3 / 2) (by norm_num)
  have heventSmall : ∀ᶠ k : ℕ in cofinite, a k < 1 :=
    ha.tendsto_cofinite_zero.eventually (Iio_mem_nhds zero_lt_one)
  have heventNorm : ∀ᶠ k : ℕ in cofinite,
      1 ≤ ‖(zeros.zero k).val‖ := by
    filter_upwards [heventSmall] with k hk
    have hnorm0 : 0 < ‖(zeros.zero k).val‖ := by
      apply norm_pos_iff.mpr
      intro hzero
      have hpos := (zeros.zero k).re_pos
      rw [hzero] at hpos
      norm_num at hpos
    have hinvNonneg : 0 ≤ ‖(zeros.zero k).val‖⁻¹ := inv_nonneg.mpr hnorm0.le
    have hinvlt : ‖(zeros.zero k).val‖⁻¹ < 1 := by
      have := (Real.rpow_lt_one_iff' hinvNonneg (by norm_num : (0 : ℝ) < p)).mp hk
      exact this
    exact (inv_lt_one₀ hnorm0).mp hinvlt |>.le
  apply (ha.mul_left
    ((2 * (m + 1 : ℝ)) ^ m * 3 ^ (1 / 2 : ℝ))).of_norm_bounded_eventually
  filter_upwards [heventNorm] with k hk
  have hterm0 : 0 ≤ Real.log (‖(zeros.zero k).val‖ + 2) ^ m *
      ‖(zeros.zero k).val‖⁻¹ ^ 2 := by
    apply mul_nonneg
    · exact pow_nonneg (Real.log_nonneg (by
        linarith [norm_nonneg ((zeros.zero k).val)])) _
    · exact sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hterm0]
  simpa only [a, p] using log_add_two_pow_mul_inv_sq_le m hk

/-- The same logarithmically weighted inverse-square estimate holds after
reflecting every zero through `rho ↦ 1 - rho`. -/
theorem ZetaZeroEnumeration.summable_log_one_sub_norm_add_two_pow_mul_inv_sq
    (zeros : ZetaZeroEnumeration) (m : ℕ) :
    Summable (fun k ↦
      Real.log (‖1 - (zeros.zero k).val‖ + 2) ^ m *
        ‖1 - (zeros.zero k).val‖⁻¹ ^ 2) := by
  simpa only [ZetaZeroEnumeration.oneSub,
    oneSubNontrivialZetaZero_val] using
      zeros.oneSub.summable_log_norm_add_two_pow_mul_inv_sq m

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
