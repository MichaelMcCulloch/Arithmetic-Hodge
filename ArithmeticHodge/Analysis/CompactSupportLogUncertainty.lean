/-
  A compact-support logarithmic uncertainty estimate for Schwartz functions.

  The proof combines a support-sensitive L1--L2 estimate, Plancherel, and a
  low-frequency cutoff at Bombieri's logarithmic scale.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option autoImplicit false

open scoped FourierTransform Real
open MeasureTheory Set

namespace ArithmeticHodge.Analysis

noncomputable section

private theorem l1_sq_le_delta_mul_l2 (F : SchwartzMap ℝ ℂ) (c δ : ℝ) (hδ : 0 < δ)
    (hs : ∀ u ∉ Set.Icc (c - δ / 2) (c + δ / 2), F u = 0) :
    (∫ u : ℝ, ‖F u‖) ^ 2 ≤ δ * ∫ u : ℝ, Complex.normSq (F u) := by
  let I : Set ℝ := Set.Icc (c - δ / 2) (c + δ / 2)
  have hends : c - δ / 2 ≤ c + δ / 2 := by linarith
  have hvol : MeasureTheory.volume.real I = δ := by
    dsimp [I]
    rw [Real.volume_real_Icc_of_le hends]
    ring
  have hL1_support : (∫ u in I, ‖F u‖) = ∫ u : ℝ, ‖F u‖ := by
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    rw [hs u hu, norm_zero]
  have hL2_support : (∫ u in I, ‖F u‖ ^ 2) = ∫ u : ℝ, ‖F u‖ ^ 2 := by
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    rw [hs u hu, norm_zero, zero_pow]
    norm_num
  have hcs := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    Real.HolderConjugate.two_two
    ((F.memLp (ENNReal.ofReal (2 : ℝ)) MeasureTheory.volume).restrict I)
    (MeasureTheory.memLp_const (1 : ℂ) :
      MeasureTheory.MemLp (fun _ : ℝ ↦ (1 : ℂ)) (ENNReal.ofReal (2 : ℝ))
        (MeasureTheory.volume.restrict I))
  have hcs' : (∫ u in I, ‖F u‖) ≤
      Real.sqrt (∫ u in I, ‖F u‖ ^ 2) * Real.sqrt δ := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    simpa [Real.rpow_two, hvol] using hcs
  rw [← hL1_support]
  simp only [Complex.normSq_eq_norm_sq]
  rw [← hL2_support]
  calc
    (∫ u in I, ‖F u‖) ^ 2 ≤
        (Real.sqrt (∫ u in I, ‖F u‖ ^ 2) * Real.sqrt δ) ^ 2 :=
      (sq_le_sq₀ (MeasureTheory.integral_nonneg fun _ ↦ norm_nonneg _) (by positivity)).2 hcs'
    _ = δ * ∫ u in I, ‖F u‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (MeasureTheory.integral_nonneg fun _ ↦ sq_nonneg _),
        Real.sq_sqrt hδ.le]
      ring

private theorem fourier_normSq_le_delta_mul_l2
    (F : SchwartzMap ℝ ℂ) (c δ ξ : ℝ) (hδ : 0 < δ)
    (hs : ∀ u ∉ Set.Icc (c - δ / 2) (c + δ / 2), F u = 0) :
    Complex.normSq (FourierTransform.fourier F ξ) ≤
      δ * ∫ u : ℝ, Complex.normSq (F u) := by
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖FourierTransform.fourier F ξ‖ ^ 2 ≤ (∫ u : ℝ, ‖F u‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (MeasureTheory.integral_nonneg fun _ ↦ norm_nonneg _)).2
        (by simpa [SchwartzMap.norm_toLp_one] using
          SchwartzMap.norm_fourier_apply_le_toLp_one F ξ)
    _ ≤ _ := l1_sq_le_delta_mul_l2 F c δ hδ hs

private theorem low_band_normSq_le (F : SchwartzMap ℝ ℂ) (c δ K : ℝ)
    (hδ : 0 < δ) (hK : 0 ≤ K)
    (hs : ∀ u ∉ Set.Icc (c - δ / 2) (c + δ / 2), F u = 0) :
    (∫ ξ in Set.Icc (-K) K, Complex.normSq (FourierTransform.fourier F ξ)) ≤
      2 * K * δ * ∫ u : ℝ, Complex.normSq (F u) := by
  let A : ℝ := ∫ u : ℝ, Complex.normSq (F u)
  have hA : 0 ≤ A := MeasureTheory.integral_nonneg fun _ ↦ Complex.normSq_nonneg _
  have hpoint (ξ : ℝ) : Complex.normSq (FourierTransform.fourier F ξ) ≤ δ * A :=
    by simpa [A] using fourier_normSq_le_delta_mul_l2 F c δ ξ hδ hs
  have hb := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (f := fun ξ : ℝ ↦ Complex.normSq (FourierTransform.fourier F ξ))
    (s := Set.Icc (-K) K) (C := δ * A) (measure_Icc_lt_top (μ := MeasureTheory.volume))
    (fun ξ _ ↦ by simpa [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)] using hpoint ξ)
  rw [Real.norm_eq_abs, abs_of_nonneg (MeasureTheory.integral_nonneg fun _ ↦
    Complex.normSq_nonneg _), Real.volume_real_Icc_of_le (by linarith)] at hb
  dsimp [A] at hb ⊢
  nlinarith

private theorem integrable_log_weight_fourier_normSq (F : SchwartzMap ℝ ℂ) :
    MeasureTheory.Integrable (fun ξ : ℝ ↦
      Real.log (max 1 |ξ|) * Complex.normSq (FourierTransform.fourier F ξ)) := by
  let H : SchwartzMap ℝ ℂ := FourierTransform.fourier F
  have hzero : MeasureTheory.Integrable (fun ξ : ℝ ↦ ‖H ξ‖) := H.integrable.norm
  have hone : MeasureTheory.Integrable (fun ξ : ℝ ↦ |ξ| * ‖H ξ‖) := by
    simpa [Real.norm_eq_abs] using H.integrable_pow_mul MeasureTheory.volume 1
  have hlinear : MeasureTheory.Integrable (fun ξ : ℝ ↦ (1 + |ξ|) * ‖H ξ‖) := by
    simpa [add_mul] using hzero.add hone
  have hdom : MeasureTheory.Integrable (fun ξ : ℝ ↦ ((1 + |ξ|) * ‖H ξ‖) * ‖H ξ‖) :=
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
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.log_nonneg (le_max_left _ _))
    (Complex.normSq_nonneg _)), Complex.normSq_eq_norm_sq, Real.norm_eq_abs]
  have hdom_nonneg : 0 ≤ ((1 + |ξ|) * ‖H ξ‖) * ‖H ξ‖ := by positivity
  rw [abs_of_nonneg hdom_nonneg]
  have hlog : Real.log (max 1 |ξ|) ≤ 1 + |ξ| :=
    (Real.log_le_self (le_trans (abs_nonneg _) (le_max_right _ _))).trans (max_le_add_of_nonneg
      (by positivity) (abs_nonneg ξ))
  change Real.log (max 1 |ξ|) * ‖H ξ‖ ^ 2 ≤ ((1 + |ξ|) * ‖H ξ‖) * ‖H ξ‖
  calc
    Real.log (max 1 |ξ|) * ‖H ξ‖ ^ 2 ≤ (1 + |ξ|) * ‖H ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hlog (sq_nonneg _)
    _ = _ := by ring

private theorem integrable_fourier_normSq (F : SchwartzMap ℝ ℂ) :
    MeasureTheory.Integrable (fun ξ : ℝ ↦
      Complex.normSq (FourierTransform.fourier F ξ)) := by
  let H : SchwartzMap ℝ ℂ := FourierTransform.fourier F
  have h := (MeasureTheory.memLp_two_iff_integrable_sq_norm
    H.continuous.aestronglyMeasurable).mp (H.memLp 2 MeasureTheory.volume)
  simpa only [Complex.normSq_eq_norm_sq] using h

private theorem logK_uncertainty_lower (F : SchwartzMap ℝ ℂ) (c δ K : ℝ)
    (hδ : 0 < δ) (hK : 1 < K)
    (hs : ∀ u ∉ Set.Icc (c - δ / 2) (c + δ / 2), F u = 0) :
    Real.log K * (1 - 2 * K * δ) * (∫ u : ℝ, Complex.normSq (F u)) ≤
      ∫ ξ : ℝ, Real.log (max 1 |ξ|) *
        Complex.normSq (FourierTransform.fourier F ξ) := by
  let S : Set ℝ := Set.Icc (-K) K
  let q : ℝ → ℝ := fun ξ ↦ Complex.normSq (FourierTransform.fourier F ξ)
  let w : ℝ → ℝ := fun ξ ↦ Real.log (max 1 |ξ|) * q ξ
  have hq : MeasureTheory.Integrable q := by
    simpa [q] using integrable_fourier_normSq F
  have hw : MeasureTheory.Integrable w := by
    simpa [w, q] using integrable_log_weight_fourier_normSq F
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK.le
  have htail_weight : Real.log K * (∫ ξ in Sᶜ, q ξ) ≤ ∫ ξ : ℝ, w ξ := by
    calc
      Real.log K * (∫ ξ in Sᶜ, q ξ) =
          ∫ ξ in Sᶜ, Real.log K * q ξ := by rw [MeasureTheory.integral_const_mul]
      _ ≤ ∫ ξ in Sᶜ, w ξ := by
        apply MeasureTheory.setIntegral_mono_on (hq.const_mul _).integrableOn hw.integrableOn
          measurableSet_Icc.compl
        intro ξ hξ
        have hnot : ξ ∉ S := hξ
        have habs : K < |ξ| := by
          apply lt_of_not_ge
          intro hle
          exact hnot ((abs_le.mp hle) : ξ ∈ Set.Icc (-K) K)
        have honeabs : 1 ≤ |ξ| := hK.le.trans habs.le
        dsimp [w, q]
        rw [max_eq_right honeabs]
        exact mul_le_mul_of_nonneg_right (Real.log_le_log (by positivity) habs.le)
          (Complex.normSq_nonneg _)
      _ ≤ _ := MeasureTheory.setIntegral_le_integral hw
        (Filter.Eventually.of_forall fun ξ ↦
          mul_nonneg (Real.log_nonneg (le_max_left _ _)) (Complex.normSq_nonneg _))
  have htail : (∫ ξ in Sᶜ, q ξ) =
      (∫ u : ℝ, Complex.normSq (F u)) - ∫ ξ in S, q ξ := by
    rw [MeasureTheory.setIntegral_compl measurableSet_Icc hq]
    congr 1
    simpa [q] using (show (∫ ξ : ℝ, Complex.normSq (FourierTransform.fourier F ξ)) =
      ∫ u : ℝ, Complex.normSq (F u) from by
        simpa only [Complex.normSq_eq_norm_sq] using SchwartzMap.integral_norm_sq_fourier F)
  have hlow : (∫ ξ in S, q ξ) ≤
      2 * K * δ * ∫ u : ℝ, Complex.normSq (F u) := by
    simpa [S, q] using low_band_normSq_le F c δ K hδ (zero_le_one.trans hK.le) hs
  rw [htail] at htail_weight
  have hA : 0 ≤ ∫ u : ℝ, Complex.normSq (F u) :=
    MeasureTheory.integral_nonneg fun _ ↦ Complex.normSq_nonneg _
  calc
    Real.log K * (1 - 2 * K * δ) * (∫ u : ℝ, Complex.normSq (F u)) ≤
        Real.log K * ((∫ u : ℝ, Complex.normSq (F u)) - ∫ ξ in S, q ξ) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hlogK
      nlinarith
    _ ≤ _ := htail_weight

private theorem bombieri_scale_properties {δ : ℝ} (hδ : 0 < δ)
    (hsmall : δ ≤ Real.exp (-4)) :
    let K := 1 / (δ * Real.log (Real.exp 1 / δ))
    1 < K ∧
      Real.log (1 / δ) - Real.log (Real.log (Real.exp 1 / δ)) - 2 ≤
        Real.log K * (1 - 2 * K * δ) := by
  let L : ℝ := Real.log (1 / δ)
  let Q : ℝ := Real.log (Real.exp 1 / δ)
  let K : ℝ := 1 / (δ * Q)
  have hδlt : δ < 1 := hsmall.trans_lt (Real.exp_lt_one_iff.mpr (by norm_num))
  have hlogδ : Real.log δ ≤ -4 :=
    (Real.log_le_iff_le_exp hδ).mpr hsmall
  have hL : 4 ≤ L := by
    dsimp [L]
    rw [one_div, Real.log_inv]
    linarith
  have hQeq : Q = 1 + L := by
    dsimp [Q, L]
    rw [Real.log_div (Real.exp_ne_zero 1) hδ.ne', Real.log_exp, one_div, Real.log_inv]
    ring
  have hQpos : 0 < Q := by rw [hQeq]; linarith
  have hQone : 1 ≤ Q := by rw [hQeq]; linarith
  have hinvpos : 0 < δ⁻¹ := inv_pos.mpr hδ
  have hinvne : δ⁻¹ ≠ 1 := by
    intro heq
    have : δ = 1 := by
      calc δ = (δ⁻¹)⁻¹ := by simp
        _ = 1 := by rw [heq, inv_one]
    linarith
  have hQlt : Q < δ⁻¹ := by
    rw [hQeq]
    have h := Real.log_lt_sub_one_of_pos hinvpos hinvne
    dsimp [L]
    rw [one_div]
    linarith
  have hδQpos : 0 < δ * Q := mul_pos hδ hQpos
  have hδQ : δ * Q < 1 := by
    have := mul_lt_mul_of_pos_left hQlt hδ
    simpa [hδ.ne'] using this
  have hK : 1 < K := by
    dsimp [K]
    exact (one_lt_div hδQpos).mpr hδQ
  have hlogK : Real.log K = L - Real.log Q := by
    dsimp [K, L]
    simp only [one_div, Real.log_inv]
    rw [Real.log_mul hδ.ne' hQpos.ne']
    ring
  have hKδ : 2 * K * δ = 2 / Q := by
    dsimp [K]
    field_simp [hδ.ne', hQpos.ne']
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQone
  have hB_le_Q : L - Real.log Q ≤ Q := by linarith [hQeq]
  have hcoef : L - Real.log Q - 2 ≤
      (L - Real.log Q) * (1 - 2 / Q) := by
    have heq : (L - Real.log Q) * (1 - 2 / Q) =
        ((L - Real.log Q) * (Q - 2)) / Q := by
      field_simp [hQpos.ne']
    rw [heq]
    apply (le_div_iff₀ hQpos).mpr
    nlinarith
  dsimp only
  change 1 < K ∧ L - Real.log Q - 2 ≤ Real.log K * (1 - 2 * K * δ)
  refine ⟨hK, ?_⟩
  rw [hlogK, hKδ]
  exact hcoef

private theorem fourier_log_weight_lower_of_intervalSupport_C_two
    (F : SchwartzMap ℝ ℂ) (c δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ Real.exp (-4))
    (hs : ∀ u ∉ Set.Icc (c - δ / 2) (c + δ / 2), F u = 0) :
    (Real.log (1 / δ) - Real.log (Real.log (Real.exp 1 / δ)) - 2) *
        ∫ u : ℝ, Complex.normSq (F u) ≤
      ∫ ξ : ℝ, Real.log (max 1 |ξ|) *
        Complex.normSq (FourierTransform.fourier F ξ) := by
  let K : ℝ := 1 / (δ * Real.log (Real.exp 1 / δ))
  have hscale := bombieri_scale_properties hδ hsmall
  change 1 < K ∧
      Real.log (1 / δ) - Real.log (Real.log (Real.exp 1 / δ)) - 2 ≤
        Real.log K * (1 - 2 * K * δ) at hscale
  have hA : 0 ≤ ∫ u : ℝ, Complex.normSq (F u) :=
    MeasureTheory.integral_nonneg fun _ ↦ Complex.normSq_nonneg _
  calc
    (Real.log (1 / δ) - Real.log (Real.log (Real.exp 1 / δ)) - 2) *
        ∫ u : ℝ, Complex.normSq (F u) ≤
      (Real.log K * (1 - 2 * K * δ)) *
        ∫ u : ℝ, Complex.normSq (F u) :=
      mul_le_mul_of_nonneg_right hscale.2 hA
    _ ≤ _ := logK_uncertainty_lower F c δ K hδ hscale.1 hs

/-- A Schwartz function supported on a sufficiently short interval has a
uniform logarithmically weighted Fourier norm-square lower bound. -/
theorem exists_fourier_log_weight_lower_of_intervalSupport :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : SchwartzMap ℝ ℂ) (c δ : ℝ),
      0 < δ →
      δ ≤ Real.exp (-4) →
      (∀ u ∉ Set.Icc (c - δ / 2) (c + δ / 2), F u = 0) →
      (Real.log (1 / δ) - Real.log (Real.log (Real.exp 1 / δ)) - C) *
          ∫ u : ℝ, Complex.normSq (F u) ≤
        ∫ ξ : ℝ,
          Real.log (max 1 |ξ|) *
            Complex.normSq (FourierTransform.fourier F ξ) := by
  refine ⟨2, by norm_num, ?_⟩
  intro F c δ hδ hsmall hs
  exact fourier_log_weight_lower_of_intervalSupport_C_two F c δ hδ hsmall hs

end

end ArithmeticHodge.Analysis
