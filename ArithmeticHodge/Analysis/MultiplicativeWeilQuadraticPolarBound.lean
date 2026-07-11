import ArithmeticHodge.Analysis.MultiplicativeWeilLogSupport
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticCriticalLine

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions SchwartzMap FourierTransform

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private theorem sq_setIntegral_norm_le_length_mul_setIntegral_normSq
    (F : SchwartzMap ℝ ℂ) {l r : ℝ} (hlr : l ≤ r) :
    (∫ u : ℝ in Set.Icc l r, ‖F u‖) ^ 2 ≤
      (r - l) * ∫ u : ℝ in Set.Icc l r, Complex.normSq (F u) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc l r)
  have hconst : MemLp (fun _ : ℝ ↦ (1 : ℝ)) 2 μ := memLp_const 1
  have hF : MemLp (fun u : ℝ ↦ ‖F u‖) 2 μ :=
    MemLp.mono_measure Measure.restrict_le_self (F.memLp 2).norm
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (p := 2) (q := 2) Real.HolderConjugate.two_two
      (by simpa using hconst) (by simpa using hF)
  simp at hholder
  have hlen : μ.real Set.univ = r - l := by
    simp [μ, hlr]
  have hsq : (∫ u : ℝ, ‖F u‖ ^ (2 : ℕ) ∂μ) =
      ∫ u : ℝ, Complex.normSq (F u) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with u
    rw [Complex.normSq_eq_norm_sq]
  rw [hlen, hsq] at hholder
  have hA : 0 ≤ ∫ u : ℝ, ‖F u‖ ∂μ :=
    integral_nonneg fun _ ↦ norm_nonneg _
  have hB : 0 ≤ ∫ u : ℝ, Complex.normSq (F u) ∂μ :=
    integral_nonneg fun _ ↦ Complex.normSq_nonneg _
  have hlen0 : 0 ≤ r - l := sub_nonneg.mpr hlr
  have hsqrt : 0 ≤
      (r - l) ^ ((2 : ℝ)⁻¹) *
        (∫ u : ℝ, Complex.normSq (F u) ∂μ) ^ ((2 : ℝ)⁻¹) :=
    mul_nonneg (Real.rpow_nonneg hlen0 _) (Real.rpow_nonneg hB _)
  have hsqle : (∫ u : ℝ, ‖F u‖ ∂μ) ^ 2 ≤
      (((r - l) ^ ((2 : ℝ)⁻¹)) *
        ((∫ u : ℝ, Complex.normSq (F u) ∂μ) ^
          ((2 : ℝ)⁻¹))) ^ 2 := by
    exact (sq_le_sq₀ hA hsqrt).2 hholder
  calc
    (∫ u : ℝ in Set.Icc l r, ‖F u‖) ^ 2 =
        (∫ u : ℝ, ‖F u‖ ∂μ) ^ 2 := rfl
    _ ≤ _ := hsqle
    _ = (r - l) * ∫ u : ℝ, Complex.normSq (F u) ∂μ := by
      rw [mul_pow]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlen0]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
      norm_num
    _ = _ := rfl

private theorem norm_integral_exp_neg_half_mul_le
    (F : SchwartzMap ℝ ℂ) {l r : ℝ}
    (hsupport : ∀ u ∉ Set.Icc l r, F u = 0) :
    ‖∫ u : ℝ, (Real.exp (-u / 2) : ℂ) * F u‖ ≤
      Real.exp (-l / 2) * ∫ u : ℝ in Set.Icc l r, ‖F u‖ := by
  have hzero : ∀ u, u ∉ Set.Icc l r →
      (Real.exp (-u / 2) : ℂ) * F u = 0 := by
    intro u hu
    simp [hsupport u hu]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc
    ‖∫ u : ℝ in Set.Icc l r, (Real.exp (-u / 2) : ℂ) * F u‖ ≤
        ∫ u : ℝ in Set.Icc l r,
          ‖(Real.exp (-u / 2) : ℂ) * F u‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ u : ℝ in Set.Icc l r, Real.exp (-u / 2) * ‖F u‖ := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ ∫ u : ℝ in Set.Icc l r, Real.exp (-l / 2) * ‖F u‖ := by
      apply setIntegral_mono_on
      · exact (by fun_prop : Continuous (fun u : ℝ ↦
            Real.exp (-u / 2) * ‖F u‖)).continuousOn.integrableOn_compact isCompact_Icc
      · exact (by fun_prop : Continuous (fun u : ℝ ↦
            Real.exp (-l / 2) * ‖F u‖)).continuousOn.integrableOn_compact isCompact_Icc
      · exact measurableSet_Icc
      · intro u hu
        exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by linarith [hu.1])) (norm_nonneg _)
    _ = _ := by rw [MeasureTheory.integral_const_mul]

private theorem norm_integral_exp_half_mul_le
    (F : SchwartzMap ℝ ℂ) {l r : ℝ}
    (hsupport : ∀ u ∉ Set.Icc l r, F u = 0) :
    ‖∫ u : ℝ, (Real.exp (u / 2) : ℂ) * F u‖ ≤
      Real.exp (r / 2) * ∫ u : ℝ in Set.Icc l r, ‖F u‖ := by
  have hzero : ∀ u, u ∉ Set.Icc l r →
      (Real.exp (u / 2) : ℂ) * F u = 0 := by
    intro u hu
    simp [hsupport u hu]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc
    ‖∫ u : ℝ in Set.Icc l r, (Real.exp (u / 2) : ℂ) * F u‖ ≤
        ∫ u : ℝ in Set.Icc l r,
          ‖(Real.exp (u / 2) : ℂ) * F u‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ u : ℝ in Set.Icc l r, Real.exp (u / 2) * ‖F u‖ := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ ∫ u : ℝ in Set.Icc l r, Real.exp (r / 2) * ‖F u‖ := by
      apply setIntegral_mono_on
      · exact (by fun_prop : Continuous (fun u : ℝ ↦
            Real.exp (u / 2) * ‖F u‖)).continuousOn.integrableOn_compact isCompact_Icc
      · exact (by fun_prop : Continuous (fun u : ℝ ↦
            Real.exp (r / 2) * ‖F u‖)).continuousOn.integrableOn_compact isCompact_Icc
      · exact measurableSet_Icc
      · intro u hu
        exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by linarith [hu.2])) (norm_nonneg _)
    _ = _ := by rw [MeasureTheory.integral_const_mul]

private theorem mellin_one_eq_integral_exp_neg_half_mul_logPullback
    (g : BombieriTest) :
    mellin (g : ℝ → ℂ) 1 =
      ∫ u : ℝ, (Real.exp (-u / 2) : ℂ) *
        g.logarithmicPullbackSchwartz (1 / 2) u := by
  calc
    mellin (g : ℝ → ℂ) 1 =
        𝓕 (g.logarithmicPullbackSchwartz 1) 0 := by
      simpa using bombieriMellin_vertical_eq_fourier g 1 0
    _ = ∫ u : ℝ, g.logarithmicPullbackSchwartz 1 u := by
      rw [SchwartzMap.fourier_coe, fourier_real_eq]
      simp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [BombieriTest.logarithmicPullbackSchwartz_apply,
        BombieriTest.logarithmicPullback]
      rw [show -1 * u = -u / 2 + (-(1 / 2) * u) by ring,
        Real.exp_add]
      push_cast
      ring

private theorem mellin_zero_eq_integral_exp_half_mul_logPullback
    (g : BombieriTest) :
    mellin (g : ℝ → ℂ) 0 =
      ∫ u : ℝ, (Real.exp (u / 2) : ℂ) *
        g.logarithmicPullbackSchwartz (1 / 2) u := by
  calc
    mellin (g : ℝ → ℂ) 0 =
        𝓕 (g.logarithmicPullbackSchwartz 0) 0 := by
      simpa using bombieriMellin_vertical_eq_fourier g 0 0
    _ = ∫ u : ℝ, g.logarithmicPullbackSchwartz 0 u := by
      rw [SchwartzMap.fourier_coe, fourier_real_eq]
      simp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [BombieriTest.logarithmicPullbackSchwartz_apply,
        BombieriTest.logarithmicPullback, zero_mul, neg_zero, Real.exp_zero,
        Complex.ofReal_one, one_mul]
      have hweight : (Real.exp (u / 2) : ℂ) *
          (Real.exp (-(1 / 2) * u) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.exp_add]
        rw [show u / 2 + -(1 / 2) * u = 0 by ring]
        simp
      rw [← mul_assoc, hweight, one_mul]

theorem bombieriQuadratic_polar_re_lower_of_support
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b) :
    -4 * Real.log (b / a) * Real.cosh (Real.log (b / a) / 2) *
        ∫ u : ℝ, Complex.normSq (g.logarithmicPullbackSchwartz (1 / 2) u) ≤
      (mellin (bombieriQuadraticTest g : ℝ → ℂ) 1 +
        mellin (bombieriQuadraticTest g : ℝ → ℂ) 0).re := by
  let F : SchwartzMap ℝ ℂ := g.logarithmicPullbackSchwartz (1 / 2)
  let l : ℝ := -Real.log b
  let r : ℝ := -Real.log a
  let δ : ℝ := Real.log (b / a)
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hratio : 1 ≤ b / a := (one_le_div₀ ha).2 hab
  have hδ0 : 0 ≤ δ := Real.log_nonneg hratio
  have hlr : l ≤ r := by
    dsimp [l, r]
    exact neg_le_neg (Real.log_le_log ha hab)
  have hwidth : r - l = δ := by
    dsimp [l, r, δ]
    rw [Real.log_div hb.ne' ha.ne']
    ring
  have hsupportF : ∀ u ∉ Set.Icc l r, F u = 0 := by
    intro u hu
    exact logarithmicPullbackSchwartz_eq_zero_outside g ha hsupport (by simpa [l, r] using hu)
  let L : ℝ := ∫ u : ℝ in Set.Icc l r, ‖F u‖
  let N : ℝ := ∫ u : ℝ, Complex.normSq (F u)
  have hL0 : 0 ≤ L := by
    exact integral_nonneg fun _ ↦ norm_nonneg _
  have hN0 : 0 ≤ N := by
    exact integral_nonneg fun _ ↦ Complex.normSq_nonneg _
  have hNset : (∫ u : ℝ in Set.Icc l r, Complex.normSq (F u)) = N := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    simp [hsupportF u hu]
  have hL2 : L ^ 2 ≤ δ * N := by
    have h := sq_setIntegral_norm_le_length_mul_setIntegral_normSq F hlr
    rw [hwidth, hNset] at h
    exact h
  have hM1 : ‖mellin (g : ℝ → ℂ) 1‖ ≤ Real.exp (-l / 2) * L := by
    rw [mellin_one_eq_integral_exp_neg_half_mul_logPullback]
    exact norm_integral_exp_neg_half_mul_le F hsupportF
  have hM0 : ‖mellin (g : ℝ → ℂ) 0‖ ≤ Real.exp (r / 2) * L := by
    rw [mellin_zero_eq_integral_exp_half_mul_logPullback]
    exact norm_integral_exp_half_mul_le F hsupportF
  have hprod :
      ‖mellin (g : ℝ → ℂ) 1‖ * ‖mellin (g : ℝ → ℂ) 0‖ ≤
        Real.exp (δ / 2) * δ * N := by
    calc
      ‖mellin (g : ℝ → ℂ) 1‖ * ‖mellin (g : ℝ → ℂ) 0‖ ≤
          (Real.exp (-l / 2) * L) * (Real.exp (r / 2) * L) := by
        exact mul_le_mul hM1 hM0 (norm_nonneg _)
          (mul_nonneg (Real.exp_nonneg _) hL0)
      _ = Real.exp (δ / 2) * L ^ 2 := by
        rw [show Real.exp (-l / 2) * L * (Real.exp (r / 2) * L) =
            (Real.exp (-l / 2) * Real.exp (r / 2)) * L ^ 2 by ring]
        rw [← Real.exp_add]
        rw [show -l / 2 + r / 2 = δ / 2 by linarith [hwidth]]
      _ ≤ Real.exp (δ / 2) * (δ * N) :=
        mul_le_mul_of_nonneg_left hL2 (Real.exp_nonneg _)
      _ = Real.exp (δ / 2) * δ * N := by ring
  have hpolar :
      -2 * (‖mellin (g : ℝ → ℂ) 1‖ * ‖mellin (g : ℝ → ℂ) 0‖) ≤
        (mellin (bombieriQuadraticTest g : ℝ → ℂ) 1 +
          mellin (bombieriQuadraticTest g : ℝ → ℂ) 0).re := by
    rw [bombieriQuadratic_polar_eq_two_re]
    simp only [ofReal_re]
    let z : ℂ := mellin (g : ℝ → ℂ) 1 *
      starRingEnd ℂ (mellin (g : ℝ → ℂ) 0)
    have hz : -‖z‖ ≤ z.re := (abs_le.mp (Complex.abs_re_le_norm z)).1
    have hznorm : ‖z‖ =
        ‖mellin (g : ℝ → ℂ) 1‖ * ‖mellin (g : ℝ → ℂ) 0‖ := by
      simp [z]
    rw [hznorm] at hz
    change -(‖mellin (g : ℝ → ℂ) 1‖ * ‖mellin (g : ℝ → ℂ) 0‖) ≤
      (mellin (g : ℝ → ℂ) 1 *
        starRingEnd ℂ (mellin (g : ℝ → ℂ) 0)).re at hz
    linarith
  have hexp_cosh : 2 * Real.exp (δ / 2) ≤ 4 * Real.cosh (δ / 2) := by
    rw [Real.cosh_eq]
    have hneg : 0 ≤ Real.exp (-(δ / 2)) := Real.exp_nonneg _
    linarith
  have hmass : 0 ≤ δ * N := mul_nonneg hδ0 hN0
  have hcoef :
      2 * Real.exp (δ / 2) * (δ * N) ≤
        4 * Real.cosh (δ / 2) * (δ * N) :=
    mul_le_mul_of_nonneg_right hexp_cosh hmass
  change -4 * δ * Real.cosh (δ / 2) * N ≤ _
  calc
    -4 * δ * Real.cosh (δ / 2) * N =
        -(4 * Real.cosh (δ / 2) * (δ * N)) := by ring
    _ ≤ -(2 * Real.exp (δ / 2) * (δ * N)) := neg_le_neg hcoef
    _ = -2 * (Real.exp (δ / 2) * δ * N) := by ring
    _ ≤ -2 *
        (‖mellin (g : ℝ → ℂ) 1‖ * ‖mellin (g : ℝ → ℂ) 0‖) := by
      linarith
    _ ≤ _ := hpolar

end


end ArithmeticHodge.Analysis.MultiplicativeWeil
