import ArithmeticHodge.Analysis.EntireFunction.Order
import GammaLowerScratch
import ZetaOutsideStripScratch

open Complex Real Filter Topology

namespace ArithmeticHodge.Analysis.EntireFunction

noncomputable def zetaOrderRegularized (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) * (Complex.Gammaℝ s)⁻¹

theorem differentiable_zetaOrderRegularized :
    Differentiable ℂ zetaOrderRegularized := by
  unfold zetaOrderRegularized
  exact ((((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add (differentiable_const 1)).mul
      Complex.differentiable_Gammaℝ_inv)

theorem zetaOrderRegularized_eq_of_im_ne_zero
    (s : ℂ) (hs : s.im ≠ 0) :
    zetaOrderRegularized s = s * (s - 1) * riemannZeta s := by
  have hs₀ : s ≠ 0 := by
    intro h
    subst s
    exact hs rfl
  have hs₁ : s ≠ 1 := by
    intro h
    subst s
    exact hs rfl
  have hGamma : Complex.Gammaℝ s ≠ 0 := by
    intro hΓ
    rw [Complex.Gammaℝ_eq_zero_iff] at hΓ
    obtain ⟨n, hsn⟩ := hΓ
    apply hs
    simpa using congr_arg Complex.im hsn
  have hcompleted : completedRiemannZeta s =
      Complex.Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs₀]
    field_simp
  have hnumerator :
      s * (s - 1) * completedRiemannZeta₀ s + 1 =
        s * (s - 1) * completedRiemannZeta s := by
    have h₁s : 1 - s ≠ 0 := sub_ne_zero.mpr hs₁.symm
    rw [completedRiemannZeta_eq]
    field_simp [hs₀, h₁s]
    ring
  rw [zetaOrderRegularized, hnumerator, hcompleted]
  field_simp

theorem norm_completedRiemannZeta₀_le_rpow_scratch
    (r : ℝ) (hr : 26 ≤ r) (s : ℂ) (hs : ‖s‖ ≤ r) :
    ‖completedRiemannZeta₀ s‖ ≤ (r + 10) ^ (r + 10) := by
  have hmax : maxModulus completedRiemannZeta₀ r ≤
      (r + 10) ^ (r + 10) := by
    let z : ℂ := (24 : ℕ)
    have hz_re : (1 : ℝ) ≤ (completedRiemannZeta₀ z).re := by
      simpa [z] using completedZeta₀_even_re_lower 0
    have hz_radius : ‖z‖ ≤ r := by
      dsimp [z]
      norm_num
      linarith
    have hM_one : (1 : ℝ) ≤ maxModulus completedRiemannZeta₀ r :=
      hz_re.trans ((Complex.re_le_norm _).trans
        (norm_le_maxModulus completedRiemannZeta₀
          differentiable_completedZeta₀ z r (by linarith) hz_radius))
    have hlog := log_maxModulus_completedZeta_le r (by linarith)
    calc
      maxModulus completedRiemannZeta₀ r
          = Real.exp (Real.log (maxModulus completedRiemannZeta₀ r)) :=
            (Real.exp_log (lt_of_lt_of_le zero_lt_one hM_one)).symm
      _ ≤ Real.exp ((r + 10) * Real.log (r + 10)) := Real.exp_le_exp.mpr hlog
      _ = (r + 10) ^ (r + 10) := by
        rw [Real.rpow_def_of_pos (by linarith)]
        congr 1
        ring_nf
  exact (norm_le_maxModulus completedRiemannZeta₀
    differentiable_completedZeta₀ s r (by linarith) hs).trans hmax

theorem norm_zetaOrderNumerator_le_rpow_scratch
    (r : ℝ) (hr : 26 ≤ r) (s : ℂ) (hs : ‖s‖ ≤ r) :
    ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖ ≤
      (r + 10) ^ (r + 13) := by
  let R : ℝ := r + 10
  let L : ℝ := R ^ R
  have hr₀ : 0 ≤ r := by linarith
  have hR₁ : (1 : ℝ) ≤ R := by dsimp [R]; linarith
  have hRpos : 0 < R := zero_lt_one.trans_le hR₁
  have hL₁ : (1 : ℝ) ≤ L := Real.one_le_rpow hR₁ (by dsimp [R]; linarith)
  have hLambda : ‖completedRiemannZeta₀ s‖ ≤ L := by
    simpa [R, L] using norm_completedRiemannZeta₀_le_rpow_scratch r hr s hs
  have hs₁ : ‖s - 1‖ ≤ r + 1 := by
    calc
      ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ r + 1 := by norm_num; linarith
  have hcoeff : r * (r + 1) + 1 ≤ R ^ 3 := by
    calc
      r * (r + 1) + 1 ≤ R * R + R := by
        gcongr <;> dsimp [R] <;> linarith
      _ ≤ R ^ 3 := by
        nlinarith [hR₁, sq_nonneg R, mul_nonneg (sq_nonneg R) hRpos.le]
  have hnorm : ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖ ≤
      (r * (r + 1) + 1) * L := by
    calc
      ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖
          ≤ ‖s * (s - 1) * completedRiemannZeta₀ s‖ + ‖(1 : ℂ)‖ :=
            norm_add_le _ _
      _ = ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖ + 1 := by
        norm_num [norm_mul]
      _ ≤ r * (r + 1) * L + 1 := by gcongr
      _ ≤ (r * (r + 1) + 1) * L := by nlinarith
  calc
    ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖
        ≤ (r * (r + 1) + 1) * L := hnorm
    _ ≤ R ^ 3 * L := mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = (r + 10) ^ (r + 13) := by
      calc
        R ^ 3 * L = R ^ 3 * R ^ R := by rfl
        _ = R ^ (3 : ℝ) * R ^ R :=
          congrArg (fun x : ℝ ↦ x * R ^ R) (Real.rpow_natCast R 3).symm
        _ = R ^ ((3 : ℝ) + R) := (Real.rpow_add hRpos (3 : ℝ) R).symm
        _ = (r + 10) ^ (r + 13) := by
          dsimp [R]
          congr 1
          ring_nf

theorem norm_zetaOrderRegularized_le_exp_quadratic_scratch
    (σ₁ σ₂ : ℝ) (hσ : σ₁ ≤ σ₂) :
    ∃ D K : ℝ, 0 < D ∧ 0 < K ∧
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 4 ≤ |s.im| →
        ‖zetaOrderRegularized s‖ ≤ D * Real.exp (K * |s.im| ^ 2) := by
  obtain ⟨A, C, hA, hC, hGamma⟩ :=
    ArithmeticHodge.Analysis.norm_Gammaℝ_inv_stirling_upper_bound_scratch σ₁ σ₂ hσ
  let M : ℝ := max |σ₁| |σ₂|
  let Q : ℝ := M + 35
  let K : ℝ := (1 + Q / 4) ^ 2 + A / 4 + Real.pi / 16
  have hM : 0 ≤ M := le_trans (abs_nonneg σ₁) (le_max_left _ _)
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hK : 0 < K := by
    dsimp [K]
    have hsq : 0 < (1 + Q / 4) ^ 2 := sq_pos_of_pos (by positivity)
    positivity
  refine ⟨C, K, hC, hK, fun s hs₁ hs₂ ht ↦ ?_⟩
  let T : ℝ := |s.im|
  let r : ℝ := T + M + 22
  let U : ℝ := T + M + 32
  let V : ℝ := T + Q
  have hT : 4 ≤ T := by simpa [T] using ht
  have hT_pos : 0 < T := by linarith
  have hr : 26 ≤ r := by dsimp [r]; linarith
  have hre_abs : |s.re| ≤ M := by
    apply abs_le.mpr
    constructor
    · calc
        -M ≤ -|σ₁| := neg_le_neg (le_max_left _ _)
        _ ≤ σ₁ := neg_abs_le σ₁
        _ ≤ s.re := hs₁
    · calc
        s.re ≤ σ₂ := hs₂
        _ ≤ |σ₂| := le_abs_self σ₂
        _ ≤ M := le_max_right _ _
  have hs_norm : ‖s‖ ≤ r := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ M + T := by gcongr
      _ ≤ r := by dsimp [r]; linarith
  have hnum_raw := norm_zetaOrderNumerator_le_rpow_scratch r hr s hs_norm
  have hU : 0 < U := by dsimp [U]; linarith
  have hV : 0 < V := by dsimp [V]; linarith
  have hr_base : r + 10 = U := by dsimp [r, U]; ring
  have hr_exp : r + 13 = V := by dsimp [r, V, Q]; ring
  have hUV : U ≤ V := by dsimp [U, V, Q]; linarith
  have hnum : ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖ ≤
      Real.exp (V ^ 2) := by
    calc
      ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖
          ≤ (r + 10) ^ (r + 13) := hnum_raw
      _ = Real.exp (Real.log U * V) := by
        rw [hr_base, hr_exp, Real.rpow_def_of_pos hU]
      _ ≤ Real.exp (V ^ 2) := by
        apply Real.exp_le_exp.mpr
        calc
          Real.log U * V ≤ U * V :=
            mul_le_mul_of_nonneg_right (Real.log_le_self hU.le) hV.le
          _ ≤ V * V := mul_le_mul_of_nonneg_right hUV hV.le
          _ = V ^ 2 := by ring
  have hGamma := hGamma s hs₁ hs₂ ht
  have hpow : T ^ A ≤ Real.exp (A * T) := by
    rw [Real.rpow_def_of_pos hT_pos]
    apply Real.exp_le_exp.mpr
    calc
      Real.log T * A ≤ T * A :=
        mul_le_mul_of_nonneg_right (Real.log_le_self hT_pos.le) hA
      _ = A * T := by ring
  have hV_linear : V ≤ (1 + Q / 4) * T := by
    have hQ_le : Q ≤ Q / 4 * T := by
      have := mul_nonneg hQ.le (show 0 ≤ T - 4 by linarith)
      nlinarith
    dsimp [V]
    linarith
  have hV_sq : V ^ 2 ≤ (1 + Q / 4) ^ 2 * T ^ 2 := by
    calc
      V ^ 2 ≤ ((1 + Q / 4) * T) ^ 2 :=
        (sq_le_sq₀ hV.le (mul_nonneg (by positivity) hT_pos.le)).mpr hV_linear
      _ = (1 + Q / 4) ^ 2 * T ^ 2 := by ring
  have hT_quad : T ≤ T ^ 2 / 4 := by
    have := mul_nonneg hT_pos.le (show 0 ≤ T - 4 by linarith)
    nlinarith
  have hA_term : A * T ≤ (A / 4) * T ^ 2 := by
    calc
      A * T ≤ A * (T ^ 2 / 4) := mul_le_mul_of_nonneg_left hT_quad hA
      _ = (A / 4) * T ^ 2 := by ring
  have hpi_term : Real.pi / 4 * T ≤ (Real.pi / 16) * T ^ 2 := by
    calc
      Real.pi / 4 * T ≤ Real.pi / 4 * (T ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left hT_quad (by positivity)
      _ = (Real.pi / 16) * T ^ 2 := by ring
  have hexponent :
      V ^ 2 + A * T + Real.pi / 4 * T ≤ K * T ^ 2 := by
    calc
      V ^ 2 + A * T + Real.pi / 4 * T
          ≤ (1 + Q / 4) ^ 2 * T ^ 2 + (A / 4) * T ^ 2 +
              (Real.pi / 16) * T ^ 2 := by gcongr
      _ = K * T ^ 2 := by dsimp [K]; ring
  rw [zetaOrderRegularized]
  calc
    ‖(s * (s - 1) * completedRiemannZeta₀ s + 1) * (Complex.Gammaℝ s)⁻¹‖
        = ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖ *
            ‖(Complex.Gammaℝ s)⁻¹‖ := norm_mul _ _
    _ ≤ Real.exp (V ^ 2) *
          (C * T ^ A * Real.exp (Real.pi / 4 * T)) := by gcongr
    _ ≤ Real.exp (V ^ 2) *
          (C * Real.exp (A * T) * Real.exp (Real.pi / 4 * T)) := by gcongr
    _ = C * Real.exp (V ^ 2 + A * T + Real.pi / 4 * T) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ ≤ C * Real.exp (K * T ^ 2) := by gcongr
    _ = C * Real.exp (K * |s.im| ^ 2) := by rfl

theorem zetaOrderRegularized_vertical_strip_growth_scratch
    (a b : ℝ) (hab : a < b) :
    ∃ c < Real.pi / (b - a), ∃ B,
      zetaOrderRegularized =O[
        comap (_root_.abs ∘ Complex.im) atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo a b)]
        fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
  obtain ⟨D, K, hD, hK, hquad⟩ :=
    norm_zetaOrderRegularized_le_exp_quadratic_scratch a b hab.le
  let c : ℝ := Real.pi / (2 * (b - a))
  have hwidth : 0 < b - a := sub_pos.mpr hab
  have hc : 0 < c := by dsimp [c]; positivity
  have hc_lt : c < Real.pi / (b - a) := by
    have hfull : 0 < Real.pi / (b - a) := div_pos Real.pi_pos hwidth
    have hc_half : c = (Real.pi / (b - a)) / 2 := by
      dsimp [c]
      field_simp
    rw [hc_half]
    linarith
  have hdom : ∀ᶠ T : ℝ in atTop,
      K * T ^ 2 ≤ Real.exp (c * T) := by
    have hsmall :=
      (isLittleO_pow_exp_pos_mul_atTop 2 hc).bound (inv_pos.mpr hK)
    filter_upwards [hsmall] with T hT
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg T),
      abs_of_pos (Real.exp_pos _)] at hT
    calc
      K * T ^ 2 ≤ K * (K⁻¹ * Real.exp (c * T)) :=
        mul_le_mul_of_nonneg_left hT hK.le
      _ = Real.exp (c * T) := by field_simp
  refine ⟨c, hc_lt, 1, Asymptotics.IsBigO.of_bound D ?_⟩
  rw [Filter.eventually_inf_principal, Filter.eventually_comap]
  filter_upwards [hdom, eventually_ge_atTop (4 : ℝ)] with T hdomT hT z hz hstrip
  have hzT : |z.im| = T := by simpa [Function.comp_def] using hz
  have hraw := hquad z hstrip.1.le hstrip.2.le (by simpa [hzT] using hT)
  calc
    ‖zetaOrderRegularized z‖ ≤ D * Real.exp (K * T ^ 2) := by simpa [hzT] using hraw
    _ ≤ D * Real.exp (Real.exp (c * T)) := by gcongr
    _ = D * ‖Real.exp (1 * Real.exp (c * |z.im|))‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hzT]
      simp

theorem zetaOrderRegularized_bounded_on_short_vertical_line_scratch
    (x T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = x → |s.im| ≤ T →
      ‖zetaOrderRegularized s‖ ≤ C := by
  let K : Set ℂ := ({x} : Set ℝ) ×ℂ Set.Icc (-T) T
  have hK : IsCompact K := isCompact_singleton.reProdIm isCompact_Icc
  have hcont : ContinuousOn (fun z : ℂ ↦ ‖zetaOrderRegularized z‖) K :=
    differentiable_zetaOrderRegularized.continuous.norm.continuousOn
  obtain ⟨M, hM⟩ := bddAbove_def.mp (hK.bddAbove_image hcont)
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun s hsx hsT ↦ ?_⟩
  have hsK : s ∈ K := by
    constructor
    · simpa using hsx
    · exact abs_le.mp hsT
  exact (hM _ (Set.mem_image_of_mem _ hsK)).trans (le_max_right _ _)

theorem norm_le_linear_abs_im_on_vertical_line_order_scratch
    (x : ℝ) (s : ℂ) (hs : s.re = x) (ht : 2 ≤ |s.im|) :
    ‖s‖ ≤ (1 + |x| / 2) * |s.im| := by
  calc
    ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ = |x| + |s.im| := by rw [hs]
    _ ≤ (1 + |x| / 2) * |s.im| := by
      have := mul_nonneg (abs_nonneg x) (show 0 ≤ |s.im| - 2 by linarith)
      nlinarith

noncomputable def zetaOrderPLNormalized (p : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  zetaOrderRegularized s * (s - (p : ℂ))⁻¹ ^ N

theorem zetaOrderPLNormalized_diffContOnCl_scratch
    (p a b : ℝ) (N : ℕ) (hp : p < a) :
    DiffContOnCl ℂ (zetaOrderPLNormalized p N)
      (Complex.re ⁻¹' Set.Ioo a b) := by
  let S : Set ℂ := Complex.re ⁻¹' Set.Ioo a b
  have hclosure : closure S ⊆ Complex.re ⁻¹' Set.Icc a b := by
    apply closure_minimal
    · intro z hz
      exact ⟨hz.1.le, hz.2.le⟩
    · exact isClosed_Icc.preimage Complex.continuous_re
  have hne : ∀ z ∈ closure S, z - (p : ℂ) ≠ 0 := by
    intro z hz hzero
    have hzstrip := hclosure hz
    have hre := congr_arg Complex.re hzero
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith [hzstrip.1]
  apply DifferentiableOn.diffContOnCl
  unfold zetaOrderPLNormalized
  exact differentiable_zetaOrderRegularized.differentiableOn.mul
    (((differentiable_id.sub_const (p : ℂ)).differentiableOn.inv hne).pow N)

theorem zetaOrderPLNormalized_vertical_strip_growth_scratch
    (p a b : ℝ) (N : ℕ) (hp : p + 1 ≤ a) (hab : a < b) :
    ∃ c < Real.pi / (b - a), ∃ B,
      zetaOrderPLNormalized p N =O[
        comap (_root_.abs ∘ Complex.im) atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo a b)]
        fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
  obtain ⟨c, hc, B, hG⟩ := zetaOrderRegularized_vertical_strip_growth_scratch a b hab
  refine ⟨c, hc, B, ?_⟩
  apply (Asymptotics.IsBigO.of_bound 1 ?_).trans hG
  rw [Filter.eventually_inf_principal]
  exact Filter.Eventually.of_forall (fun z hstrip ↦ by
    have hdist : 1 ≤ ‖z - (p : ℂ)‖ := by
      calc
        1 ≤ (z - (p : ℂ)).re := by
          simp only [Complex.sub_re, Complex.ofReal_re]
          linarith [hstrip.1]
        _ ≤ |(z - (p : ℂ)).re| := le_abs_self _
        _ ≤ ‖z - (p : ℂ)‖ := Complex.abs_re_le_norm _
    have hinv : ‖(z - (p : ℂ))⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hdist
    calc
      ‖zetaOrderPLNormalized p N z‖ =
          ‖zetaOrderRegularized z‖ * ‖(z - (p : ℂ))⁻¹‖ ^ N := by
            simp only [zetaOrderPLNormalized, norm_mul, norm_pow]
      _ ≤ ‖zetaOrderRegularized z‖ * 1 := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) hinv
      _ = 1 * ‖zetaOrderRegularized z‖ := by ring)

theorem norm_zetaOrderPLNormalized_on_large_vertical_line_scratch
    (p x A C : ℝ) (N : ℕ) (_hA : 0 ≤ A) (hN : A + 2 ≤ (N : ℝ))
    (s : ℂ) (hsx : s.re = x) (ht : 2 ≤ |s.im|)
    (hζ : ‖riemannZeta s‖ ≤ C * |s.im| ^ A) :
    ‖zetaOrderPLNormalized p N s‖ ≤
      C * (1 + |x| / 2) * (1 + |x - 1| / 2) := by
  let T : ℝ := |s.im|
  let k₀ : ℝ := 1 + |x| / 2
  let k₁ : ℝ := 1 + |x - 1| / 2
  have hT : 2 ≤ T := by simpa [T] using ht
  have hT_pos : 0 < T := by linarith
  have him : s.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    norm_num at ht
  have hreg := zetaOrderRegularized_eq_of_im_ne_zero s him
  have hs_norm : ‖s‖ ≤ k₀ * T := by
    simpa [k₀, T] using norm_le_linear_abs_im_on_vertical_line_order_scratch x s hsx ht
  have hs_sub_norm : ‖s - 1‖ ≤ k₁ * T := by
    have hre : (s - 1).re = x - 1 := by simp [hsx]
    have him_abs : |(s - 1).im| = |s.im| := by simp
    have := norm_le_linear_abs_im_on_vertical_line_order_scratch
      (x - 1) (s - 1) hre (by simpa [him_abs] using ht)
    simpa [k₁, T, him_abs] using this
  have hdist : T ≤ ‖s - (p : ℂ)‖ := by
    calc
      T = |(s - (p : ℂ)).im| := by simp [T]
      _ ≤ ‖s - (p : ℂ)‖ := Complex.abs_im_le_norm _
  have hdist_pos : 0 < ‖s - (p : ℂ)‖ := hT_pos.trans_le hdist
  have hT_pow : T ^ (A + 2) ≤ T ^ N := by
    calc
      T ^ (A + 2) ≤ T ^ (N : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hN
      _ = T ^ N := Real.rpow_natCast T N
  have hden_pow : T ^ N ≤ ‖s - (p : ℂ)‖ ^ N :=
    pow_le_pow_left₀ hT_pos.le hdist N
  have hratio :
      T ^ (A + 2) * (‖s - (p : ℂ)‖ ^ N)⁻¹ ≤ 1 := by
    calc
      T ^ (A + 2) * (‖s - (p : ℂ)‖ ^ N)⁻¹
          ≤ T ^ N * (‖s - (p : ℂ)‖ ^ N)⁻¹ := by gcongr
      _ ≤ ‖s - (p : ℂ)‖ ^ N *
          (‖s - (p : ℂ)‖ ^ N)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ (pow_ne_zero N hdist_pos.ne')
  have hpoly : T ^ A * T * T = T ^ (A + 2) := by
    calc
      T ^ A * T * T = T ^ A * T ^ (1 : ℝ) * T ^ (1 : ℝ) := by
        simp only [Real.rpow_one]
      _ = T ^ (A + 1) * T ^ (1 : ℝ) :=
        congrArg (fun y : ℝ ↦ y * T ^ (1 : ℝ))
          (Real.rpow_add hT_pos A 1).symm
      _ = T ^ ((A + 1) + 1) := (Real.rpow_add hT_pos (A + 1) 1).symm
      _ = T ^ (A + 2) := by ring_nf
  have hζ_nonneg : 0 ≤ C * T ^ A :=
    (norm_nonneg (riemannZeta s)).trans (by simpa [T] using hζ)
  have hC : 0 ≤ C := by
    have hpw : 0 < T ^ A := Real.rpow_pos_of_pos hT_pos A
    nlinarith
  rw [zetaOrderPLNormalized, hreg]
  calc
    ‖(s * (s - 1) * riemannZeta s) * (s - (p : ℂ))⁻¹ ^ N‖ =
        ‖s‖ * ‖s - 1‖ * ‖riemannZeta s‖ *
          (‖s - (p : ℂ)‖ ^ N)⁻¹ := by
            simp only [norm_mul, norm_pow, norm_inv, inv_pow]
    _ ≤ (k₀ * T) * (k₁ * T) * (C * T ^ A) *
          (‖s - (p : ℂ)‖ ^ N)⁻¹ := by
            gcongr
    _ = C * k₀ * k₁ *
          (T ^ (A + 2) * (‖s - (p : ℂ)‖ ^ N)⁻¹) := by
            rw [← hpoly]
            ring
    _ ≤ C * k₀ * k₁ * 1 := by
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = C * (1 + |x| / 2) * (1 + |x - 1| / 2) := by
      simp [k₀, k₁]

theorem norm_zetaOrderPLNormalized_le_regularized_scratch
    (p : ℝ) (N : ℕ) (z : ℂ) (hp : p + 1 ≤ z.re) :
    ‖zetaOrderPLNormalized p N z‖ ≤ ‖zetaOrderRegularized z‖ := by
  have hdist : 1 ≤ ‖z - (p : ℂ)‖ := by
    calc
      1 ≤ (z - (p : ℂ)).re := by
        simp only [Complex.sub_re, Complex.ofReal_re]
        linarith
      _ ≤ |(z - (p : ℂ)).re| := le_abs_self _
      _ ≤ ‖z - (p : ℂ)‖ := Complex.abs_re_le_norm _
  have hinv : ‖(z - (p : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hdist
  calc
    ‖zetaOrderPLNormalized p N z‖ =
        ‖zetaOrderRegularized z‖ * ‖(z - (p : ℂ))⁻¹‖ ^ N := by
          simp only [zetaOrderPLNormalized, norm_mul, norm_pow]
    _ ≤ ‖zetaOrderRegularized z‖ * 1 := by
      gcongr
      exact pow_le_one₀ (norm_nonneg _) hinv
    _ = ‖zetaOrderRegularized z‖ := mul_one _

theorem zetaOrderPLNormalized_mul_pow_scratch
    (p : ℝ) (N : ℕ) (z : ℂ) (hz : z - (p : ℂ) ≠ 0) :
    zetaOrderPLNormalized p N z * (z - (p : ℂ)) ^ N =
      zetaOrderRegularized z := by
  rw [zetaOrderPLNormalized, mul_assoc, ← mul_pow,
    inv_mul_cancel₀ hz, one_pow, mul_one]

theorem zeta_vertical_strip_bound_repaired_scratch
    (σ₁ σ₂ : ℝ) (_hσ : σ₁ ≤ σ₂) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 2 ≤ |s.im| →
        ‖riemannZeta s‖ ≤ C * |s.im| ^ A := by
  let a : ℝ := min σ₁ (-1)
  let b : ℝ := max σ₂ 2
  let p : ℝ := a - 1
  have ha_le : a ≤ σ₁ := min_le_left _ _
  have ha_neg : a < 0 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hb_ge : σ₂ ≤ b := le_max_left _ _
  have hb_one : 1 < b := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hab : a < b :=
    lt_of_le_of_lt (min_le_right _ _) (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
  obtain ⟨A, Cₗ, hA, hCₗ, hleft⟩ :=
    ArithmeticHodge.Analysis.riemannZeta_polynomial_bound_of_re_le_neg
      a a le_rfl ha_neg
  obtain ⟨Cᵣ, hCᵣ, hright⟩ :=
    riemannZeta_dirichlet_uniform_bound b hb_one
  let N : ℕ := ⌈A + 2⌉₊
  have hN : A + 2 ≤ (N : ℝ) := Nat.le_ceil _
  have hN₂ : (2 : ℝ) ≤ N := by linarith
  obtain ⟨Cₐ, hCₐ, hshort_a⟩ :=
    zetaOrderRegularized_bounded_on_short_vertical_line_scratch a 2
  obtain ⟨Cb, hCb, hshort_b⟩ :=
    zetaOrderRegularized_bounded_on_short_vertical_line_scratch b 2
  let L : ℝ := Cₗ * (1 + |a| / 2) * (1 + |a - 1| / 2)
  let R : ℝ := Cᵣ * (1 + |b| / 2) * (1 + |b - 1| / 2)
  have hL : 0 < L := by dsimp [L]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  let C₀ : ℝ := max Cₐ (max Cb (max L R))
  have hC₀ : 0 < C₀ := hCₐ.trans_le (by exact le_max_left _ _)
  have hboundary_a : ∀ z : ℂ, z.re = a →
      ‖zetaOrderPLNormalized p N z‖ ≤ C₀ := by
    intro z hz
    by_cases ht_small : |z.im| ≤ 2
    · calc
        ‖zetaOrderPLNormalized p N z‖ ≤ ‖zetaOrderRegularized z‖ :=
          norm_zetaOrderPLNormalized_le_regularized_scratch p N z (by
            dsimp [p]
            linarith)
        _ ≤ Cₐ := hshort_a z hz ht_small
        _ ≤ C₀ := le_max_left _ _
    · have ht : 2 ≤ |z.im| := (not_le.mp ht_small).le
      have hlarge := norm_zetaOrderPLNormalized_on_large_vertical_line_scratch
        p a A Cₗ N hA hN z hz ht (hleft z (by linarith) (by linarith) ht)
      calc
        ‖zetaOrderPLNormalized p N z‖ ≤ L := by simpa [L] using hlarge
        _ ≤ max L R := le_max_left _ _
        _ ≤ max Cb (max L R) := le_max_right _ _
        _ ≤ C₀ := le_max_right _ _
  have hboundary_b : ∀ z : ℂ, z.re = b →
      ‖zetaOrderPLNormalized p N z‖ ≤ C₀ := by
    intro z hz
    by_cases ht_small : |z.im| ≤ 2
    · calc
        ‖zetaOrderPLNormalized p N z‖ ≤ ‖zetaOrderRegularized z‖ :=
          norm_zetaOrderPLNormalized_le_regularized_scratch p N z (by
            dsimp [p]
            linarith)
        _ ≤ Cb := hshort_b z hz ht_small
        _ ≤ max Cb (max L R) := le_max_left _ _
        _ ≤ C₀ := le_max_right _ _
    · have ht : 2 ≤ |z.im| := (not_le.mp ht_small).le
      have hζ : ‖riemannZeta z‖ ≤ Cᵣ * |z.im| ^ (0 : ℝ) := by
        simpa using hright z (by linarith)
      have hlarge := norm_zetaOrderPLNormalized_on_large_vertical_line_scratch
        p b 0 Cᵣ N (by norm_num) (by linarith) z hz ht hζ
      calc
        ‖zetaOrderPLNormalized p N z‖ ≤ R := by simpa [R] using hlarge
        _ ≤ max L R := le_max_right _ _
        _ ≤ max Cb (max L R) := le_max_right _ _
        _ ≤ C₀ := le_max_right _ _
  have hfd : DiffContOnCl ℂ (zetaOrderPLNormalized p N)
      (Complex.re ⁻¹' Set.Ioo a b) :=
    zetaOrderPLNormalized_diffContOnCl_scratch p a b N (by dsimp [p]; linarith)
  have hgrowth := zetaOrderPLNormalized_vertical_strip_growth_scratch
    p a b N (by dsimp [p]; linarith) hab
  have hnormalized : ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖zetaOrderPLNormalized p N z‖ ≤ C₀ := by
    intro z hza hzb
    exact PhragmenLindelof.vertical_strip hfd hgrowth hboundary_a hboundary_b hza hzb
  let M : ℝ := max |σ₁ - p| |σ₂ - p|
  let k : ℝ := 1 + M / 2
  have hM : 0 ≤ M := (abs_nonneg (σ₁ - p)).trans (le_max_left _ _)
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨(N : ℝ), C₀ * k ^ N, by positivity, by positivity,
    fun s hs₁ hs₂ ht ↦ ?_⟩
  let T : ℝ := |s.im|
  have hT : 2 ≤ T := by simpa [T] using ht
  have hT_pos : 0 < T := by linarith
  have him : s.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    norm_num at ht
  have hsp : s - (p : ℂ) ≠ 0 := by
    intro h
    have hi := congr_arg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
    exact him hi
  have hF := hnormalized s (ha_le.trans hs₁) (hs₂.trans hb_ge)
  have hmul := zetaOrderPLNormalized_mul_pow_scratch p N s hsp
  have hreg := zetaOrderRegularized_eq_of_im_ne_zero s him
  have hs_norm_lower : 1 ≤ ‖s‖ := by
    calc
      1 ≤ T := by linarith
      _ ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hs_sub_norm_lower : 1 ≤ ‖s - 1‖ := by
    calc
      1 ≤ T := by linarith
      _ = |(s - 1).im| := by simp [T]
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hζG : ‖riemannZeta s‖ ≤ ‖zetaOrderRegularized s‖ := by
    rw [hreg, norm_mul, norm_mul]
    calc
      ‖riemannZeta s‖ = 1 * 1 * ‖riemannZeta s‖ := by ring
      _ ≤ ‖s‖ * ‖s - 1‖ * ‖riemannZeta s‖ := by gcongr
  have hG : ‖zetaOrderRegularized s‖ ≤
      C₀ * ‖s - (p : ℂ)‖ ^ N := by
    rw [← hmul, norm_mul, norm_pow]
    gcongr
  have hre_abs : |s.re - p| ≤ M := by
    apply abs_le.mpr
    constructor
    · calc
        -M ≤ -|σ₁ - p| := neg_le_neg (le_max_left _ _)
        _ ≤ σ₁ - p := neg_abs_le _
        _ ≤ s.re - p := by linarith
    · calc
        s.re - p ≤ σ₂ - p := by linarith
        _ ≤ |σ₂ - p| := le_abs_self _
        _ ≤ M := le_max_right _ _
  have hsp_upper : ‖s - (p : ℂ)‖ ≤ k * T := by
    calc
      ‖s - (p : ℂ)‖ ≤ |(s - (p : ℂ)).re| +
          |(s - (p : ℂ)).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |s.re - p| + T := by simp [T]
      _ ≤ M + T := by gcongr
      _ ≤ k * T := by
        dsimp [k]
        have := mul_nonneg hM (show 0 ≤ T - 2 by linarith)
        nlinarith
  calc
    ‖riemannZeta s‖ ≤ ‖zetaOrderRegularized s‖ := hζG
    _ ≤ C₀ * ‖s - (p : ℂ)‖ ^ N := hG
    _ ≤ C₀ * (k * T) ^ N := by gcongr
    _ = (C₀ * k ^ N) * T ^ (N : ℝ) := by
      rw [mul_pow, Real.rpow_natCast]
      ring
    _ = (C₀ * k ^ N) * |s.im| ^ (N : ℝ) := by rfl

#print axioms zeta_vertical_strip_bound_repaired_scratch

end ArithmeticHodge.Analysis.EntireFunction
