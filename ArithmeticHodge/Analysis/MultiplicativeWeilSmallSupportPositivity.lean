import ArithmeticHodge.Analysis.MultiplicativeWeilDigammaLower
import ArithmeticHodge.Analysis.MultiplicativeWeilLogSupport
import ArithmeticHodge.Analysis.CompactSupportLogUncertainty
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticPolarBound
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticReality

set_option autoImplicit false

open Complex MeasureTheory Real Set Topology TopologicalSpace Filter
open scoped ContDiff Distributions SchwartzMap FourierTransform

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private theorem exists_small_width_coefficient
    (C₁ C₃ : ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ Real.exp (-4) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        C₁ + 4 * δ * Real.cosh (δ / 2) <
          (1 / 2 : ℝ) *
            (Real.log (1 / δ) -
              Real.log (Real.log (Real.exp 1 / δ)) - C₃) := by
  let H : ℝ → ℝ := fun x ↦
    (1 / 2 : ℝ) * (x - Real.log 2 - Real.log x - C₃) -
      C₁ - 4 * Real.exp (1 / 2)
  have hsub : Tendsto (fun x : ℝ ↦ x - Real.log x) atTop atTop := by
    exact (Asymptotics.IsEquivalent.refl.sub_isLittleO
      Real.isLittleO_log_id_atTop).symm.tendsto_atTop tendsto_id
  have hH : Tendsto H atTop atTop := by
    have hmul : Tendsto (fun x : ℝ ↦ (1 / 2 : ℝ) * (x - Real.log x))
        atTop atTop := Tendsto.const_mul_atTop (by norm_num) hsub
    have hadd := tendsto_atTop_add_const_right atTop
      ((-((1 / 2 : ℝ) * Real.log 2) - (1 / 2 : ℝ) * C₃) -
        C₁ - 4 * Real.exp (1 / 2)) hmul
    convert hadd using 1
    funext x
    dsimp [H]
    ring
  have hev : ∀ᶠ x : ℝ in atTop, 1 ≤ H x := (tendsto_atTop.1 hH) 1
  obtain ⟨T, hT⟩ := (eventually_atTop.1 hev)
  let T' : ℝ := max T 4
  let δ₀ : ℝ := Real.exp (-T')
  refine ⟨δ₀, Real.exp_pos _, ?_, ?_⟩
  · dsimp [δ₀]
    exact Real.exp_le_exp.mpr (neg_le_neg (le_max_right T 4))
  intro δ hδ hδle
  let x : ℝ := Real.log (1 / δ)
  have hδlt1 : δ < 1 :=
    hδle.trans_lt ((show δ₀ ≤ Real.exp (-4) by
      dsimp [δ₀]
      exact Real.exp_le_exp.mpr (neg_le_neg (le_max_right T 4))).trans_lt
        (Real.exp_lt_one_iff.mpr (by norm_num)))
  have hx_eq : x = -Real.log δ := by
    dsimp [x]
    rw [one_div, Real.log_inv]
  have hlogδ : Real.log δ ≤ -T' := by
    have h := Real.log_le_log hδ hδle
    simpa [δ₀] using h
  have hxT' : T' ≤ x := by rw [hx_eq]; linarith
  have hxT : T ≤ x := (le_max_left T 4).trans hxT'
  have hx4 : 4 ≤ x := (le_max_right T 4).trans hxT'
  have hHx : 1 ≤ H x := hT x hxT
  have hxpos : 0 < x := by linarith
  have hlog_inner : Real.log (Real.log (Real.exp 1 / δ)) =
      Real.log (1 + x) := by
    congr 1
    dsimp [x]
    rw [Real.log_div (Real.exp_ne_zero 1) hδ.ne', Real.log_exp,
      one_div, Real.log_inv]
    ring
  have hlog_one_add : Real.log (1 + x) ≤ Real.log 2 + Real.log x := by
    have hle : 1 + x ≤ 2 * x := by linarith
    calc
      Real.log (1 + x) ≤ Real.log (2 * x) :=
        Real.log_le_log (by linarith) hle
      _ = Real.log 2 + Real.log x := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxpos.ne']
  have hδle1 : δ ≤ 1 := hδlt1.le
  have hcosh : Real.cosh (δ / 2) ≤ Real.exp (1 / 2) := by
    rw [Real.cosh_eq]
    have h₁ : Real.exp (δ / 2) ≤ Real.exp (1 / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have h₂ : Real.exp (-(δ / 2)) ≤ Real.exp (1 / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hpolar : 4 * δ * Real.cosh (δ / 2) ≤ 4 * Real.exp (1 / 2) := by
    calc
      4 * δ * Real.cosh (δ / 2) ≤ 4 * 1 * Real.exp (1 / 2) := by
        gcongr
      _ = 4 * Real.exp (1 / 2) := by ring
  dsimp [H] at hHx
  rw [show Real.log (1 / δ) = x by rfl, hlog_inner]
  nlinarith

private theorem logPullback_normSq_integral_pos
    (g : BombieriTest) (hg : g ≠ 0) :
    0 < ∫ u : ℝ,
      Complex.normSq (g.logarithmicPullbackSchwartz (1 / 2) u) := by
  let F : SchwartzMap ℝ ℂ := g.logarithmicPullbackSchwartz (1 / 2)
  let h : ℝ → ℝ := fun u ↦ Complex.normSq (F u)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, g x ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hg
    ext y
    simpa using hall y
  have hxpos : 0 < x := by
    have hxmem := g.tsupport_subset
      (subset_tsupport g (Function.mem_support.mpr hx))
    simpa [positiveHalfLine] using hxmem
  have hFne : F (-Real.log x) ≠ 0 := by
    dsimp [F]
    unfold BombieriTest.logarithmicPullback
    rw [neg_mul, neg_neg, Real.exp_log hxpos]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hx
  have hcont : Continuous h :=
    Complex.continuous_normSq.comp F.continuous
  have hcompact : HasCompactSupport h := by
    have hFcompact := g.logarithmicPullback_hasCompactSupport (1 / 2)
    exact hFcompact.comp_left (by simp)
  have hnonneg : 0 ≤ h := fun u ↦ Complex.normSq_nonneg (F u)
  have hnonzero : h (-Real.log x) ≠ 0 :=
    Complex.normSq_eq_zero.not.mpr hFne
  simpa [h, F] using
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hcompact hnonneg hnonzero

private theorem support_ratio_gt_one_of_ne_zero
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b) (hg : g ≠ 0) :
    1 < b / a := by
  have hratio : 1 ≤ b / a := (one_le_div₀ ha).2 hab
  refine lt_of_le_of_ne hratio ?_
  intro heq
  have hba : b = a := by
    apply (div_eq_one_iff_eq ha.ne').mp
    exact heq.symm
  have hFsupport : ∀ u ∉ Set.Icc (-Real.log b) (-Real.log a),
      g.logarithmicPullbackSchwartz (1 / 2) u = 0 :=
    fun u hu ↦ logarithmicPullbackSchwartz_eq_zero_outside g ha hsupport hu
  have hmass0 : (∫ u : ℝ,
      Complex.normSq (g.logarithmicPullbackSchwartz (1 / 2) u)) = 0 := by
    have hsingleton : Set.Icc (-Real.log b) (-Real.log a) =
        {-Real.log a} := by
      rw [hba]
      simp
    have hzero : ∀ u ∉ Set.Icc (-Real.log b) (-Real.log a),
        Complex.normSq (g.logarithmicPullbackSchwartz (1 / 2) u) = 0 := by
      intro u hu
      rw [hFsupport u hu, Complex.normSq_zero]
    calc
      (∫ u : ℝ,
          Complex.normSq (g.logarithmicPullbackSchwartz (1 / 2) u)) =
          ∫ u : ℝ in Set.Icc (-Real.log b) (-Real.log a),
            Complex.normSq (g.logarithmicPullbackSchwartz (1 / 2) u) :=
        (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
      _ = ∫ u : ℝ in {-Real.log a},
            Complex.normSq (g.logarithmicPullbackSchwartz (1 / 2) u) := by
        rw [hsingleton]
      _ = 0 := by simp
  exact (logPullback_normSq_integral_pos g hg).ne' hmass0

private theorem logarithmicPullback_centered_support
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b) :
    let δ := Real.log (b / a)
    let c := (-Real.log b - Real.log a) / 2
    ∀ u ∉ Set.Icc (c - δ / 2) (c + δ / 2),
      g.logarithmicPullbackSchwartz (1 / 2) u = 0 := by
  dsimp only
  intro u hu
  apply logarithmicPullbackSchwartz_eq_zero_outside g ha hsupport
  intro horig
  apply hu
  have hb : 0 < b := ha.trans_le hab
  have hwidth : Real.log (b / a) = Real.log b - Real.log a := by
    rw [Real.log_div hb.ne' ha.ne']
  rw [hwidth]
  constructor <;> linarith [horig.1, horig.2]

private theorem integrable_log_weight_normSq_schwartz
    (H : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ ↦
      Real.log (max 1 |ξ|) * Complex.normSq (H ξ)) := by
  have hzero : Integrable (fun ξ : ℝ ↦ ‖H ξ‖) := H.integrable.norm
  have hone : Integrable (fun ξ : ℝ ↦ |ξ| * ‖H ξ‖) := by
    simpa [Real.norm_eq_abs] using H.integrable_pow_mul volume 1
  have hlinear : Integrable (fun ξ : ℝ ↦ (1 + |ξ|) * ‖H ξ‖) := by
    simpa [add_mul] using hzero.add hone
  have hdom : Integrable (fun ξ : ℝ ↦ ((1 + |ξ|) * ‖H ξ‖) * ‖H ξ‖) :=
    hlinear.mul_bdd (c := SchwartzMap.seminorm ℝ 0 0 H)
      H.continuous.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ ↦ by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
          SchwartzMap.norm_le_seminorm ℝ H ξ)
  apply hdom.mono
    (((continuous_const.max continuous_abs).log fun ξ ↦
      ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 |ξ|))).mul
      (Complex.continuous_normSq.comp H.continuous)).aestronglyMeasurable
  filter_upwards with ξ
  change ‖Real.log (max 1 |ξ|) * Complex.normSq (H ξ)‖ ≤
    ‖((1 + |ξ|) * ‖H ξ‖) * ‖H ξ‖‖
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.log_nonneg (le_max_left _ _))
      (Complex.normSq_nonneg _)), Complex.normSq_eq_norm_sq]
  have hdom_nonneg : 0 ≤ ((1 + |ξ|) * ‖H ξ‖) * ‖H ξ‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hdom_nonneg]
  have hlog : Real.log (max 1 |ξ|) ≤ 1 + |ξ| :=
    (Real.log_le_self (le_trans (abs_nonneg _) (le_max_right _ _))).trans
      (max_le_add_of_nonneg (by positivity) (abs_nonneg ξ))
  nlinarith [sq_nonneg ‖H ξ‖]

private theorem integrable_scaled_log_weight_normSq_schwartz
    (H : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ ↦
      Real.log (max 1 |(2 * Real.pi) * ξ|) * Complex.normSq (H ξ)) := by
  let c : ℝ := 2 * Real.pi
  have hc : 1 ≤ c := by
    dsimp [c]
    nlinarith [Real.pi_gt_three]
  have hzero : Integrable (fun ξ : ℝ ↦ ‖H ξ‖) := H.integrable.norm
  have hone : Integrable (fun ξ : ℝ ↦ |ξ| * ‖H ξ‖) := by
    simpa [Real.norm_eq_abs] using H.integrable_pow_mul volume 1
  have hlinear : Integrable (fun ξ : ℝ ↦ (1 + |ξ|) * ‖H ξ‖) := by
    simpa [add_mul] using hzero.add hone
  have hdom0 : Integrable (fun ξ : ℝ ↦ ((1 + |ξ|) * ‖H ξ‖) * ‖H ξ‖) :=
    hlinear.mul_bdd (c := SchwartzMap.seminorm ℝ 0 0 H)
      H.continuous.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ ↦ by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
          SchwartzMap.norm_le_seminorm ℝ H ξ)
  have hdom : Integrable (fun ξ : ℝ ↦
      c * (((1 + |ξ|) * ‖H ξ‖) * ‖H ξ‖)) := hdom0.const_mul c
  apply hdom.mono
    (((continuous_const.max
      ((continuous_const.mul continuous_id).abs)).log fun ξ ↦
        ne_of_gt (lt_of_lt_of_le zero_lt_one
          (le_max_left 1 |c * ξ|))).mul
      (Complex.continuous_normSq.comp H.continuous)).aestronglyMeasurable
  filter_upwards with ξ
  change ‖Real.log (max 1 |(2 * Real.pi) * ξ|) *
      Complex.normSq (H ξ)‖ ≤
    ‖c * (((1 + |ξ|) * ‖H ξ‖) * ‖H ξ‖)‖
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.log_nonneg (le_max_left _ _))
      (Complex.normSq_nonneg _)), Complex.normSq_eq_norm_sq]
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hdom_nonneg : 0 ≤ c * (((1 + |ξ|) * ‖H ξ‖) * ‖H ξ‖) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hdom_nonneg]
  have hmax : max 1 |c * ξ| ≤ c * (1 + |ξ|) := by
    rw [abs_mul, abs_of_nonneg hc0]
    apply max_le
    · nlinarith [abs_nonneg ξ]
    · nlinarith [abs_nonneg ξ]
  have hlog : Real.log (max 1 |c * ξ|) ≤ c * (1 + |ξ|) :=
    (Real.log_le_self (le_trans (abs_nonneg _) (le_max_right _ _))).trans hmax
  nlinarith [sq_nonneg ‖H ξ‖]

private theorem fourier_log_weight_le_normalized_mellin_log_weight
    (g : BombieriTest) :
    (∫ ξ : ℝ, Real.log (max 1 |ξ|) *
        Complex.normSq
          (FourierTransform.fourier
            (g.logarithmicPullbackSchwartz (1 / 2)) ξ)) ≤
      (1 / (2 * Real.pi)) * ∫ v : ℝ,
        Real.log (max 1 |v|) *
          Complex.normSq
            (mellin (g : ℝ → ℂ)
              ((1 / 2 : ℝ) + v * Complex.I)) := by
  let c : ℝ := 2 * Real.pi
  let H : SchwartzMap ℝ ℂ :=
    FourierTransform.fourier (g.logarithmicPullbackSchwartz (1 / 2))
  let G : ℝ → ℝ := fun v ↦
    Real.log (max 1 |v|) *
      Complex.normSq
        (mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I))
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hcone : 1 ≤ c := by
    dsimp [c]
    nlinarith [Real.pi_gt_three]
  have hscale : (1 / c) * (∫ v : ℝ, G v) =
      ∫ ξ : ℝ, G (c * ξ) := by
    rw [MeasureTheory.Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.mpr hcpos)]
    simp only [one_div, smul_eq_mul]
  have hGc (ξ : ℝ) : G (c * ξ) =
      Real.log (max 1 |c * ξ|) * Complex.normSq (H ξ) := by
    dsimp [G, H]
    rw [bombieriMellin_vertical_eq_fourier]
    congr 2
    dsimp [c]
    field_simp
  have hbase : Integrable (fun ξ : ℝ ↦
      Real.log (max 1 |ξ|) * Complex.normSq (H ξ)) :=
    integrable_log_weight_normSq_schwartz H
  have hscaled : Integrable (fun ξ : ℝ ↦
      Real.log (max 1 |c * ξ|) * Complex.normSq (H ξ)) := by
    simpa only [c] using integrable_scaled_log_weight_normSq_schwartz H
  have hmono : (∫ ξ : ℝ,
      Real.log (max 1 |ξ|) * Complex.normSq (H ξ)) ≤
      ∫ ξ : ℝ,
        Real.log (max 1 |c * ξ|) * Complex.normSq (H ξ) := by
    apply MeasureTheory.integral_mono hbase hscaled
    intro ξ
    have habs : |ξ| ≤ |c * ξ| := by
      rw [abs_mul, abs_of_pos hcpos]
      exact le_mul_of_one_le_left (abs_nonneg ξ) hcone
    exact mul_le_mul_of_nonneg_right
      (Real.log_le_log (by positivity) (max_le_max_left 1 habs))
      (Complex.normSq_nonneg _)
  change (∫ ξ : ℝ,
      Real.log (max 1 |ξ|) * Complex.normSq (H ξ)) ≤
    (1 / c) * ∫ v : ℝ, G v
  calc
    (∫ ξ : ℝ,
        Real.log (max 1 |ξ|) * Complex.normSq (H ξ)) ≤
        ∫ ξ : ℝ,
          Real.log (max 1 |c * ξ|) * Complex.normSq (H ξ) := hmono
    _ = ∫ ξ : ℝ, G (c * ξ) := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      exact (hGc ξ).symm
    _ = (1 / c) * ∫ v : ℝ, G v := hscale.symm

private theorem bombieriArchTerm_quadratic_re_lower
    (g : BombieriTest) (C : ℝ)
    (hkernel : ∀ v : ℝ,
      (1 / 2 : ℝ) * Real.log (max 1 |v|) - C ≤
        (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re -
          Real.log Real.pi) :
    (1 / 2 : ℝ) *
        (∫ ξ : ℝ, Real.log (max 1 |ξ|) *
          Complex.normSq
            (FourierTransform.fourier
              (g.logarithmicPullbackSchwartz (1 / 2)) ξ)) -
      C * ∫ u : ℝ,
        Complex.normSq (g.logarithmicPullbackSchwartz (1 / 2) u) ≤
      (bombieriArchTerm (bombieriQuadraticTest g)).re := by
  let c : ℝ := 2 * Real.pi
  let F : SchwartzMap ℝ ℂ := g.logarithmicPullbackSchwartz (1 / 2)
  let H : SchwartzMap ℝ ℂ := FourierTransform.fourier F
  let Q : ℝ → ℝ := fun v ↦ Complex.normSq
    (mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I))
  let W : ℝ → ℝ := fun v ↦ Real.log (max 1 |v|) * Q v
  let K : ℝ → ℝ := fun v ↦
    (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re -
      Real.log Real.pi
  let L : ℝ → ℝ := fun v ↦ ((1 / 2 : ℝ) * Real.log (max 1 |v|) - C) * Q v
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hcne : c ≠ 0 := hcpos.ne'
  have hQ : Integrable Q := by
    have hH : Integrable (fun ξ : ℝ ↦ Complex.normSq (H ξ)) := by
      have hm := (MeasureTheory.memLp_two_iff_integrable_sq_norm
        H.continuous.aestronglyMeasurable).mp (H.memLp 2 volume)
      simpa only [Complex.normSq_eq_norm_sq] using hm
    have hs := hH.comp_div hcne
    apply hs.congr
    filter_upwards with v
    dsimp [Q, H, F]
    rw [bombieriMellin_vertical_eq_fourier]
  have hW : Integrable W := by
    have hs := (integrable_scaled_log_weight_normSq_schwartz H).comp_div hcne
    apply hs.congr
    filter_upwards with v
    dsimp [W, Q, H, F, c]
    rw [bombieriMellin_vertical_eq_fourier]
    congr 2
    field_simp
  have hL : Integrable L := by
    dsimp only [L]
    have hhalfW : Integrable (fun v ↦ (1 / 2 : ℝ) * W v) := hW.const_mul _
    have hCQ : Integrable (fun v ↦ C * Q v) := hQ.const_mul _
    apply (hhalfW.sub hCQ).congr
    filter_upwards with v
    dsimp [W]
    ring
  have hK : Integrable (fun v ↦ K v * Q v) := by
    have hcomplex := bombieriCriticalArchKernel_integrable (bombieriQuadraticTest g)
    have hcomplex' : Integrable (fun v : ℝ ↦ ((K v * Q v : ℝ) : ℂ)) := by
      apply hcomplex.congr
      filter_upwards with v
      dsimp [K, Q]
      rw [mellin_bombieriQuadraticTest_critical_eq_normSq]
      push_cast
      ring
    simpa using hcomplex'.re
  have hint : (∫ v : ℝ, L v) ≤ ∫ v : ℝ, K v * Q v := by
    apply MeasureTheory.integral_mono hL hK
    intro v
    exact mul_le_mul_of_nonneg_right (hkernel v) (Complex.normSq_nonneg _)
  have harch : (bombieriArchTerm (bombieriQuadraticTest g)).re =
      (1 / c) * ∫ v : ℝ, K v * Q v := by
    have hintegral :
        (∫ v : ℝ, ((K v : ℝ) : ℂ) * ((Q v : ℝ) : ℂ)) =
          ((∫ v : ℝ, K v * Q v : ℝ) : ℂ) := by
      calc
        (∫ v : ℝ, ((K v : ℝ) : ℂ) * ((Q v : ℝ) : ℂ)) =
            ∫ v : ℝ, ((K v * Q v : ℝ) : ℂ) := by
          apply integral_congr_ae
          filter_upwards [] with v
          push_cast
          ring
        _ = _ := integral_complex_ofReal
    rw [bombieriArchTerm_quadratic_eq_critical_normSq_integral]
    change (((1 / c : ℝ) : ℂ) *
      ∫ v : ℝ, ((K v : ℝ) : ℂ) * ((Q v : ℝ) : ℂ)).re = _
    rw [hintegral]
    simp
  have hQnorm : (1 / c) * ∫ v : ℝ, Q v =
      ∫ u : ℝ, Complex.normSq (F u) := by
    dsimp [c, Q, F]
    exact mellin_critical_normSq_integral_eq_logPullback_normSq g
  have hWbound : (∫ ξ : ℝ,
      Real.log (max 1 |ξ|) * Complex.normSq (H ξ)) ≤
      (1 / c) * ∫ v : ℝ, W v := by
    simpa only [c, H, F, W, Q] using
      fourier_log_weight_le_normalized_mellin_log_weight g
  have hLint : (∫ v : ℝ, L v) =
      (1 / 2 : ℝ) * (∫ v : ℝ, W v) - C * (∫ v : ℝ, Q v) := by
    have hhalfW : Integrable (fun v ↦ (1 / 2 : ℝ) * W v) := hW.const_mul _
    have hCQ : Integrable (fun v ↦ C * Q v) := hQ.const_mul _
    calc
      (∫ v : ℝ, L v) = ∫ v : ℝ, (1 / 2 : ℝ) * W v - C * Q v := by
        apply integral_congr_ae
        filter_upwards [] with v
        dsimp [L, W]
        ring
      _ = _ := MeasureTheory.integral_sub hhalfW hCQ
      _ = _ := by rw [integral_const_mul, integral_const_mul]
  have hLnorm : (1 / c) * ∫ v : ℝ, L v =
      (1 / 2 : ℝ) * ((1 / c) * ∫ v : ℝ, W v) -
        C * ((1 / c) * ∫ v : ℝ, Q v) := by
    rw [hLint]
    ring
  change (1 / 2 : ℝ) *
      (∫ ξ : ℝ, Real.log (max 1 |ξ|) * Complex.normSq (H ξ)) -
    C * ∫ u : ℝ, Complex.normSq (F u) ≤ _
  rw [harch, ← hQnorm]
  calc
    (1 / 2 : ℝ) *
        (∫ ξ : ℝ, Real.log (max 1 |ξ|) * Complex.normSq (H ξ)) -
        C * ((1 / c) * ∫ v : ℝ, Q v) ≤
      (1 / 2 : ℝ) * ((1 / c) * ∫ v : ℝ, W v) -
        C * ((1 / c) * ∫ v : ℝ, Q v) := by
      gcongr
    _ = (1 / c) * ∫ v : ℝ, L v := hLnorm.symm
    _ ≤ (1 / c) * ∫ v : ℝ, K v * Q v := by
      exact mul_le_mul_of_nonneg_left hint (by positivity)

theorem exists_support_ratio_bombieriQuadratic_strictPos :
    ∃ R₀ : ℝ, 1 < R₀ ∧ R₀ < 2 ∧
      ∀ (g : BombieriTest) {a b : ℝ},
        0 < a → a ≤ b → tsupport g ⊆ Set.Icc a b →
        b / a ≤ R₀ → g ≠ 0 →
        (bombieriFunctional (bombieriQuadraticTest g)).im = 0 ∧
          0 < (bombieriFunctional (bombieriQuadraticTest g)).re := by
  obtain ⟨C₁, hC₁, hkernel⟩ :=
    exists_bombieriCriticalGammaKernel_log_lower
  obtain ⟨C₃, hC₃, huncertainty⟩ :=
    ArithmeticHodge.Analysis.exists_fourier_log_weight_lower_of_intervalSupport
  obtain ⟨δ₀, hδ₀, hδ₀small, hcoefficient⟩ :=
    exists_small_width_coefficient C₁ C₃
  let R₀ : ℝ := min (Real.exp δ₀) (3 / 2)
  have hR₀one : 1 < R₀ := by
    dsimp [R₀]
    exact lt_min (by simpa using (Real.exp_lt_exp.mpr hδ₀)) (by norm_num)
  have hR₀two : R₀ < 2 := by
    exact (min_le_right (Real.exp δ₀) (3 / 2 : ℝ)).trans_lt (by norm_num)
  refine ⟨R₀, hR₀one, hR₀two, ?_⟩
  intro g a b ha hab hsupport hratio hg
  refine ⟨bombieriFunctional_bombieriQuadraticTest_im_eq_zero g, ?_⟩
  have hb : 0 < b := ha.trans_le hab
  have hratioPos : 0 < b / a := div_pos hb ha
  have hratioOne : 1 < b / a :=
    support_ratio_gt_one_of_ne_zero g ha hab hsupport hg
  have hratioExp : b / a ≤ Real.exp δ₀ :=
    hratio.trans (min_le_left (Real.exp δ₀) (3 / 2 : ℝ))
  let δ : ℝ := Real.log (b / a)
  let c : ℝ := (-Real.log b - Real.log a) / 2
  let F : SchwartzMap ℝ ℂ := g.logarithmicPullbackSchwartz (1 / 2)
  let A : ℝ := ∫ u : ℝ, Complex.normSq (F u)
  let J : ℝ := ∫ ξ : ℝ,
    Real.log (max 1 |ξ|) *
      Complex.normSq (FourierTransform.fourier F ξ)
  let B : ℝ := Real.log (1 / δ) -
    Real.log (Real.log (Real.exp 1 / δ)) - C₃
  let p : ℝ := 4 * δ * Real.cosh (δ / 2)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact Real.log_pos hratioOne
  have hδle : δ ≤ δ₀ := by
    dsimp [δ]
    have hlog := Real.log_le_log hratioPos hratioExp
    simpa using hlog
  have hδsmall : δ ≤ Real.exp (-4) := hδle.trans hδ₀small
  have hsupportF : ∀ u ∉ Set.Icc (c - δ / 2) (c + δ / 2), F u = 0 := by
    simpa only [c, δ, F] using
      logarithmicPullback_centered_support g ha hab hsupport
  have hA : 0 < A := by
    simpa only [A, F] using logPullback_normSq_integral_pos g hg
  have hJ : B * A ≤ J := by
    simpa only [B, A, J, F] using
      huncertainty F c δ hδpos hδsmall hsupportF
  have harch : (1 / 2 : ℝ) * J - C₁ * A ≤
      (bombieriArchTerm (bombieriQuadraticTest g)).re := by
    simpa only [J, A, F] using
      bombieriArchTerm_quadratic_re_lower g C₁ hkernel
  have hpolar : -p * A ≤
      (mellin (bombieriQuadraticTest g : ℝ → ℂ) 1 +
        mellin (bombieriQuadraticTest g : ℝ → ℂ) 0).re := by
    simpa only [p, A, F, neg_mul] using
      bombieriQuadratic_polar_re_lower_of_support g ha hab hsupport
  have hpolar' : -p * A ≤
      (mellin (bombieriQuadraticTest g : ℝ → ℂ) 1).re +
        (mellin (bombieriQuadraticTest g : ℝ → ℂ) 0).re := by
    simpa only [add_re] using hpolar
  have hcoef : C₁ + p < (1 / 2 : ℝ) * B := by
    simpa only [p, B] using hcoefficient δ hδpos hδle
  have hcoefA : (C₁ + p) * A < ((1 / 2 : ℝ) * B) * A :=
    mul_lt_mul_of_pos_right hcoef hA
  have hJhalf : (1 / 2 : ℝ) * (B * A) ≤ (1 / 2 : ℝ) * J :=
    mul_le_mul_of_nonneg_left hJ (by norm_num)
  have hratioTwo : b / a < 2 := hratio.trans_lt hR₀two
  rw [bombieriFunctional_quadratic_eq_polar_add_arch_of_support_ratio_lt_two
    g ha hab hsupport hratioTwo]
  simp only [add_re]
  nlinarith [hpolar', hJhalf]

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
