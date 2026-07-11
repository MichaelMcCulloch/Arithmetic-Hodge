import ArithmeticHodge.Analysis.MultiplicativeWeilDigammaIntegral

set_option autoImplicit false

open Complex Filter MeasureTheory Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private theorem abs_bombieriDigammaKernel_sub_inv_le
    (n : ℕ) (v : ℝ) :
    |bombieriDigammaKernel (n + 1) v - ((n + 1 : ℕ) : ℝ)⁻¹| ≤
      (1 + v ^ 2) / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  simp only [bombieriDigammaKernel, Nat.cast_add, Nat.cast_one]
  let m : ℝ := n + 1
  change |(4 * m + 1) / ((2 * m + 1 / 2) ^ 2 + v ^ 2) - m⁻¹| ≤
    (1 + v ^ 2) / m ^ 2
  have hm : 1 ≤ m := by simp [m]
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hden : 0 < (2 * m + 1 / 2) ^ 2 + v ^ 2 := by positivity
  have hnonpos :
      (4 * m + 1) / ((2 * m + 1 / 2) ^ 2 + v ^ 2) - m⁻¹ ≤ 0 := by
    rw [sub_nonpos, div_le_iff₀ hden]
    field_simp
    nlinarith [sq_nonneg v]
  rw [abs_of_nonpos hnonpos]
  rw [div_eq_mul_inv (1 + v ^ 2), div_eq_mul_inv]
  have hmq : 0 ≤ m * v ^ 2 := mul_nonneg hm0.le (sq_nonneg v)
  have hm2q : 0 ≤ m ^ 2 * v ^ 2 :=
    mul_nonneg (sq_nonneg m) (sq_nonneg v)
  have hq2 : 0 ≤ (v ^ 2) ^ 2 := sq_nonneg (v ^ 2)
  field_simp [hm0.ne']
  nlinarith

private theorem summable_bombieriDigammaKernel_sub_inv
    (v : ℝ) :
    Summable (fun n : ℕ ↦
      (bombieriDigammaKernel (n + 1) v : ℂ) -
        (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)) := by
  have hp : Summable (fun n : ℕ ↦
      1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa only [one_div] using
      (summable_nat_add_iff 1).2
        (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
  have hmajor : Summable (fun n : ℕ ↦
      (1 + v ^ 2) / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    refine (hp.mul_left (1 + v ^ 2)).congr ?_
    intro n
    simp only [one_mul, div_eq_mul_inv]
  apply hmajor.of_norm_bounded
  intro n
  rw [← Complex.ofReal_inv, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  exact abs_bombieriDigammaKernel_sub_inv_le n v

private theorem bombieriMellin_one_add_sq_norm_integrable
    (f : BombieriTest) :
    Integrable (fun v : ℝ ↦
      (1 + v ^ 2) *
        ‖mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)‖) := by
  let c : ℝ := 2 * Real.pi
  let F : SchwartzMap ℝ ℂ :=
    FourierTransform.fourier (f.logarithmicPullbackSchwartz (1 / 2))
  have hc : c ≠ 0 := by positivity
  have hscaled := (F.integrable_pow_mul volume 2).comp_div hc
  have hsqF : Integrable (fun v : ℝ ↦ v ^ 2 * ‖F (v / c)‖) := by
    refine (hscaled.const_mul (c ^ 2)).congr ?_
    filter_upwards [] with v
    simp only [Real.norm_eq_abs, sq_abs]
    field_simp [hc]
  have hsqM : Integrable (fun v : ℝ ↦ v ^ 2 *
      ‖mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)‖) := by
    refine hsqF.congr ?_
    filter_upwards [] with v
    rw [bombieriMellin_vertical_eq_fourier]
  have hzero := (f.mellin_verticalIntegrable (1 / 2)).norm
  refine (hzero.add hsqM).congr ?_
  filter_upwards [] with v
  simp only [Pi.add_apply]
  ring

private def bombieriDigammaSeriesIntegrand
    (f : BombieriTest) (n : ℕ) (v : ℝ) : ℂ :=
  ((bombieriDigammaKernel (n + 1) v : ℂ) -
      (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)) *
    mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)

private theorem bombieriDigammaSeriesIntegrand_integrable
    (f : BombieriTest) (n : ℕ) :
    Integrable (bombieriDigammaSeriesIntegrand f n) := by
  let r : ℂ := (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)
  let M : ℝ → ℂ := fun v ↦
    mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)
  have hK : Integrable (fun v : ℝ ↦
      (bombieriDigammaKernel (n + 1) v : ℂ) * M v) := by
    simpa only [M] using
      bombieriDigammaKernel_mul_mellin_integrable f (n + 1)
  have hM : Integrable M := by
    simpa only [M] using f.mellin_verticalIntegrable (1 / 2)
  refine (hK.sub (hM.const_mul r)).congr ?_
  filter_upwards [] with v
  simp only [bombieriDigammaSeriesIntegrand, M, r, Pi.sub_apply]
  ring

private theorem summable_integral_norm_bombieriDigammaSeriesIntegrand
    (f : BombieriTest) :
    Summable (fun n : ℕ ↦
      ∫ v : ℝ, ‖bombieriDigammaSeriesIntegrand f n v‖) := by
  let W : ℝ → ℝ := fun v ↦
    (1 + v ^ 2) *
      ‖mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)‖
  let C : ℝ := ∫ v : ℝ, W v
  have hW : Integrable W := by
    simpa only [W] using bombieriMellin_one_add_sq_norm_integrable f
  have hC : 0 ≤ C := integral_nonneg fun v ↦ by
    exact mul_nonneg (by positivity) (norm_nonneg _)
  have hp : Summable (fun n : ℕ ↦
      (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    exact (summable_nat_add_iff 1).2
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
  have hmajor : Summable (fun n : ℕ ↦
      (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * C) := hp.mul_right C
  apply hmajor.of_nonneg_of_le
  · intro n
    exact integral_nonneg fun v ↦ norm_nonneg _
  · intro n
    have hmajorInt : Integrable (fun v : ℝ ↦
        (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * W v) :=
      hW.const_mul _
    calc
      (∫ v : ℝ, ‖bombieriDigammaSeriesIntegrand f n v‖) ≤
          ∫ v : ℝ, (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * W v := by
        apply integral_mono (bombieriDigammaSeriesIntegrand_integrable f n).norm
          hmajorInt
        intro v
        simp only [bombieriDigammaSeriesIntegrand, norm_mul]
        rw [← Complex.ofReal_inv, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
        calc
          |bombieriDigammaKernel (n + 1) v -
                ((n + 1 : ℕ) : ℝ)⁻¹| *
              ‖mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)‖ ≤
              ((1 + v ^ 2) / (((n + 1 : ℕ) : ℝ) ^ 2)) *
                ‖mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)‖ :=
            mul_le_mul_of_nonneg_right
              (abs_bombieriDigammaKernel_sub_inv_le n v) (norm_nonneg _)
          _ = (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * W v := by
            simp only [W, div_eq_mul_inv]
            ring
      _ = (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * C := by
        rw [MeasureTheory.integral_const_mul]

private theorem integral_tsum_bombieriDigammaSeriesIntegrand
    (f : BombieriTest) :
    ∫ v : ℝ, ∑' n : ℕ, bombieriDigammaSeriesIntegrand f n v =
      ∑' n : ℕ, ∫ v : ℝ, bombieriDigammaSeriesIntegrand f n v := by
  exact (MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun n ↦ bombieriDigammaSeriesIntegrand_integrable f n)
    (summable_integral_norm_bombieriDigammaSeriesIntegrand f)).symm

private theorem bombieriDigammaSeries_integrable
    (f : BombieriTest) :
    Integrable (fun v : ℝ ↦
      ∑' n : ℕ, bombieriDigammaSeriesIntegrand f n v) := by
  let W : ℝ → ℝ := fun v ↦
    (1 + v ^ 2) *
      ‖mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)‖
  let p : ℕ → ℝ := fun n ↦ (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
  let S : ℝ := ∑' n : ℕ, p n
  have hW : Integrable W := by
    simpa only [W] using bombieriMellin_one_add_sq_norm_integrable f
  have hp : Summable p := by
    exact (summable_nat_add_iff 1).2
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
  have hS : 0 ≤ S := tsum_nonneg fun n ↦ by positivity
  have hsF (v : ℝ) :
      Summable (fun n : ℕ ↦ bombieriDigammaSeriesIntegrand f n v) := by
    simpa only [bombieriDigammaSeriesIntegrand] using
      (summable_bombieriDigammaKernel_sub_inv v).mul_right
        (mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I))
  have hmeas : AEStronglyMeasurable (fun v : ℝ ↦
      ∑' n : ℕ, bombieriDigammaSeriesIntegrand f n v) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun N ↦ (Finset.range N).aestronglyMeasurable_fun_sum fun n _ ↦
        (bombieriDigammaSeriesIntegrand_integrable f n).1)
    filter_upwards [] with v
    exact (hsF v).hasSum.tendsto_sum_nat
  refine (hW.const_mul S).mono' hmeas ?_
  filter_upwards [] with v
  have hWnonneg : 0 ≤ W v :=
    mul_nonneg (by positivity) (norm_nonneg _)
  have hterm (n : ℕ) :
      ‖bombieriDigammaSeriesIntegrand f n v‖ ≤ p n * W v := by
    simp only [bombieriDigammaSeriesIntegrand, norm_mul]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    calc
      |bombieriDigammaKernel (n + 1) v - ((n + 1 : ℕ) : ℝ)⁻¹| *
          ‖mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)‖ ≤
          ((1 + v ^ 2) / (((n + 1 : ℕ) : ℝ) ^ 2)) *
            ‖mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)‖ :=
        mul_le_mul_of_nonneg_right
          (abs_bombieriDigammaKernel_sub_inv_le n v) (norm_nonneg _)
      _ = p n * W v := by
        simp only [p, W, div_eq_mul_inv]
        ring
  calc
    ‖∑' n : ℕ, bombieriDigammaSeriesIntegrand f n v‖ ≤
        ∑' n : ℕ, ‖bombieriDigammaSeriesIntegrand f n v‖ :=
      norm_tsum_le_tsum_norm (hsF v).norm
    _ ≤ ∑' n : ℕ, p n * W v :=
      (hsF v).norm.tsum_le_tsum hterm (hp.mul_right (W v))
    _ = S * W v := by rw [tsum_mul_right]

private theorem bombieriDigamma_series_integral
    (f : BombieriTest) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          (∑' n : ℕ,
              ((bombieriDigammaKernel (n + 1) v : ℂ) -
                (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) *
            mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) =
      ∑' n : ℕ,
        (mellin (bombieriCauchyWeight f (2 * (n + 1) + 1 / 2))
            (1 / 2 : ℝ) -
          (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * f 1) := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hpoint (v : ℝ) :
      (∑' n : ℕ,
          ((bombieriDigammaKernel (n + 1) v : ℂ) -
            (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) *
        mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) =
        ∑' n : ℕ, bombieriDigammaSeriesIntegrand f n v := by
    rw [← (summable_bombieriDigammaKernel_sub_inv v).tsum_mul_right]
    apply tsum_congr
    intro n
    rfl
  calc
    c * ∫ v : ℝ,
          (∑' n : ℕ,
              ((bombieriDigammaKernel (n + 1) v : ℂ) -
                (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) *
            mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) =
        c * ∫ v : ℝ,
          ∑' n : ℕ, bombieriDigammaSeriesIntegrand f n v := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      exact hpoint v
    _ = c * ∑' n : ℕ,
          ∫ v : ℝ, bombieriDigammaSeriesIntegrand f n v := by
      rw [integral_tsum_bombieriDigammaSeriesIntegrand f]
    _ = ∑' n : ℕ,
        (mellin (bombieriCauchyWeight f (2 * (n + 1) + 1 / 2))
            (1 / 2 : ℝ) -
          (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * f 1) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      simpa only [c, bombieriDigammaSeriesIntegrand] using
        bombieriDigammaKernel_sub_integral f n

private theorem digamma_quarter_vertical_re_mul_mellin_eq
    (f : BombieriTest) (v : ℝ) :
    ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) *
        mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) =
      -((bombieriDigammaKernel 0 v : ℂ) *
          mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) +
        (Real.eulerMascheroniConstant : ℂ) *
          mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) +
        (∑' n : ℕ,
            ((bombieriDigammaKernel (n + 1) v : ℂ) -
              (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) *
          mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)) := by
  have hc := summable_bombieriDigammaKernel_sub_inv v
  have habs : Summable (fun n : ℕ ↦
      |bombieriDigammaKernel (n + 1) v - ((n + 1 : ℕ) : ℝ)⁻¹|) := by
    simpa only [← Complex.ofReal_inv, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using hc.norm
  have hreal : Summable (fun n : ℕ ↦
      bombieriDigammaKernel (n + 1) v - ((n + 1 : ℕ) : ℝ)⁻¹) :=
    habs.of_abs
  have hcast :
      ((↑(∑' n : ℕ,
          (bombieriDigammaKernel (n + 1) v - ((n + 1 : ℕ) : ℝ)⁻¹)) : ℂ)) =
        ∑' n : ℕ,
          ((bombieriDigammaKernel (n + 1) v : ℂ) -
            (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)) := by
    change Complex.ofRealCLM (∑' n : ℕ,
        (bombieriDigammaKernel (n + 1) v - ((n + 1 : ℕ) : ℝ)⁻¹)) = _
    calc
      _ = ∑' n : ℕ, Complex.ofRealCLM
          (bombieriDigammaKernel (n + 1) v - ((n + 1 : ℕ) : ℝ)⁻¹) :=
        Complex.ofRealCLM.map_tsum hreal
      _ = _ := by
        apply tsum_congr
        intro n
        simp only [Complex.ofRealCLM_apply, map_sub, Complex.ofReal_inv]
  have hdig :
      ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) =
        -((bombieriDigammaKernel 0 v : ℂ) +
          (Real.eulerMascheroniConstant : ℂ) +
          ∑' n : ℕ,
            ((bombieriDigammaKernel (n + 1) v : ℂ) -
              (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) := by
    rw [digamma_quarter_vertical_re_eq]
    push_cast
    rfl
  rw [hdig]
  ring

private theorem digamma_quarter_vertical_re_mul_mellin_integrable
    (f : BombieriTest) :
    Integrable (fun v : ℝ ↦
      ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) *
        mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)) := by
  let M : ℝ → ℂ := fun v ↦
    mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)
  let A : ℝ → ℂ := fun v ↦
    (bombieriDigammaKernel 0 v : ℂ) * M v
  let B : ℝ → ℂ := fun v ↦
    (Real.eulerMascheroniConstant : ℂ) * M v
  let C : ℝ → ℂ := fun v ↦
    (∑' n : ℕ,
        ((bombieriDigammaKernel (n + 1) v : ℂ) -
          (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) * M v
  have hA : Integrable A := by
    simpa only [A, M] using bombieriDigammaKernel_mul_mellin_integrable f 0
  have hM : Integrable M := by
    simpa only [M] using f.mellin_verticalIntegrable (1 / 2)
  have hB : Integrable B := by
    simpa only [B] using hM.const_mul (Real.eulerMascheroniConstant : ℂ)
  have hpoint (v : ℝ) : C v =
      ∑' n : ℕ, bombieriDigammaSeriesIntegrand f n v := by
    simp only [C]
    rw [← (summable_bombieriDigammaKernel_sub_inv v).tsum_mul_right]
    apply tsum_congr
    intro n
    rfl
  have hC : Integrable C :=
    (bombieriDigammaSeries_integrable f).congr
      (Filter.Eventually.of_forall fun v ↦ (hpoint v).symm)
  refine (((hA.add hB).add hC).neg).congr ?_
  filter_upwards [] with v
  simp only [Pi.add_apply, Pi.neg_apply, A, B, C, M]
  exact (digamma_quarter_vertical_re_mul_mellin_eq f v).symm

private theorem bombieri_digamma_integral
    (f : BombieriTest) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) *
            mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) =
      -(mellin (bombieriCauchyWeight f (1 / 2)) (1 / 2 : ℝ) +
        (Real.eulerMascheroniConstant : ℂ) * f 1 +
        ∑' n : ℕ,
          (mellin (bombieriCauchyWeight f (2 * (n + 1) + 1 / 2))
              (1 / 2 : ℝ) -
            (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * f 1)) := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let M : ℝ → ℂ := fun v ↦
    mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)
  let A : ℝ → ℂ := fun v ↦
    (bombieriDigammaKernel 0 v : ℂ) * M v
  let B : ℝ → ℂ := fun v ↦
    (Real.eulerMascheroniConstant : ℂ) * M v
  let C : ℝ → ℂ := fun v ↦
    (∑' n : ℕ,
        ((bombieriDigammaKernel (n + 1) v : ℂ) -
          (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) * M v
  have hA : Integrable A := by
    simpa only [A, M] using bombieriDigammaKernel_mul_mellin_integrable f 0
  have hM : Integrable M := by
    simpa only [M] using f.mellin_verticalIntegrable (1 / 2)
  have hB : Integrable B := by
    simpa only [B] using hM.const_mul (Real.eulerMascheroniConstant : ℂ)
  have hpoint (v : ℝ) : C v =
      ∑' n : ℕ, bombieriDigammaSeriesIntegrand f n v := by
    simp only [C]
    rw [← (summable_bombieriDigammaKernel_sub_inv v).tsum_mul_right]
    apply tsum_congr
    intro n
    rfl
  have hC : Integrable C :=
    (bombieriDigammaSeries_integrable f).congr
      (Filter.Eventually.of_forall fun v ↦ (hpoint v).symm)
  calc
    c * ∫ v : ℝ,
          ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) * M v =
        c * ∫ v : ℝ, -(A v + B v + C v) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      simpa only [A, B, C, M] using
        digamma_quarter_vertical_re_mul_mellin_eq f v
    _ = -(c * (∫ v : ℝ, A v) + c * (∫ v : ℝ, B v) +
          c * (∫ v : ℝ, C v)) := by
      rw [MeasureTheory.integral_neg]
      have hAB : (∫ v : ℝ, A v + B v) =
          (∫ v : ℝ, A v) + ∫ v : ℝ, B v :=
        MeasureTheory.integral_add hA hB
      have hABC : (∫ v : ℝ, A v + B v + C v) =
          ((∫ v : ℝ, A v) + ∫ v : ℝ, B v) +
            ∫ v : ℝ, C v := by
        calc
          (∫ v : ℝ, A v + B v + C v) =
              (∫ v : ℝ, A v + B v) + ∫ v : ℝ, C v := by
            simpa only [Pi.add_apply] using
              MeasureTheory.integral_add (hA.add hB) hC
          _ = _ := by rw [hAB]
      rw [hABC]
      ring
    _ = -(mellin (bombieriCauchyWeight f (1 / 2)) (1 / 2 : ℝ) +
        (Real.eulerMascheroniConstant : ℂ) * f 1 +
        ∑' n : ℕ,
          (mellin (bombieriCauchyWeight f (2 * (n + 1) + 1 / 2))
              (1 / 2 : ℝ) -
            (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * f 1)) := by
      have hAn : c * (∫ v : ℝ, A v) =
          mellin (bombieriCauchyWeight f (1 / 2)) (1 / 2 : ℝ) := by
        simpa only [c, A, M, Nat.cast_zero, mul_zero, zero_add] using
          bombieriDigammaKernel_integral f 0
      have hBn : c * (∫ v : ℝ, B v) =
          (Real.eulerMascheroniConstant : ℂ) * f 1 := by
        rw [show (∫ v : ℝ, B v) =
            (Real.eulerMascheroniConstant : ℂ) * ∫ v : ℝ, M v by
          simpa only [B] using MeasureTheory.integral_const_mul
            (Real.eulerMascheroniConstant : ℂ) M]
        calc
          c * ((Real.eulerMascheroniConstant : ℂ) * ∫ v : ℝ, M v) =
              (Real.eulerMascheroniConstant : ℂ) *
                (c * ∫ v : ℝ, M v) := by ring
          _ = (Real.eulerMascheroniConstant : ℂ) * f 1 := by
            rw [show c * ∫ v : ℝ, M v = f 1 by
              simpa only [c, M] using normalized_integral_mellin_eq_apply_one f]
      have hCn : c * (∫ v : ℝ, C v) =
          ∑' n : ℕ,
            (mellin (bombieriCauchyWeight f (2 * (n + 1) + 1 / 2))
                (1 / 2 : ℝ) -
              (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * f 1) := by
        simpa only [c, C, M] using bombieriDigamma_series_integral f
      rw [hAn, hBn, hCn]

#print axioms abs_bombieriDigammaKernel_sub_inv_le
#print axioms summable_bombieriDigammaKernel_sub_inv
#print axioms bombieriMellin_one_add_sq_norm_integrable
#print axioms bombieriDigammaSeriesIntegrand_integrable
#print axioms summable_integral_norm_bombieriDigammaSeriesIntegrand
#print axioms integral_tsum_bombieriDigammaSeriesIntegrand
#print axioms bombieriDigammaSeries_integrable
#print axioms bombieriDigamma_series_integral
#print axioms digamma_quarter_vertical_re_mul_mellin_eq
#print axioms digamma_quarter_vertical_re_mul_mellin_integrable
#print axioms bombieri_digamma_integral

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
