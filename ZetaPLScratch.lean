import ArithmeticHodge.Analysis.EntireFunction.Order
import ArithmeticHodge.Analysis.ZetaProduct
import ArithmeticHodge.Analysis.ComplexStirling
import GammaLowerScratch
import ZetaOutsideStripScratch

open Complex Real Filter Topology

namespace ArithmeticHodge.Analysis

noncomputable def zetaRegularized (s : ℂ) : ℂ :=
  2 * xiFunction s * (Complex.Gammaℝ s)⁻¹

theorem differentiable_zetaRegularized :
    Differentiable ℂ zetaRegularized := by
  unfold zetaRegularized
  exact ((differentiable_const (c := (2 : ℂ))).mul differentiable_xiFunction).mul
    Complex.differentiable_Gammaℝ_inv

theorem zetaRegularized_eq (s : ℂ) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1)
    (hΓ : Complex.Gammaℝ s ≠ 0) :
    zetaRegularized s = s * (s - 1) * riemannZeta s := by
  have hcompleted : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs₀]
    field_simp
  rw [zetaRegularized, xiFunction_eq_mul_completedZeta s hs₀ hs₁, hcompleted]
  field_simp

theorem zetaRegularized_eq_of_im_ne_zero (s : ℂ) (hs : s.im ≠ 0) :
    zetaRegularized s = s * (s - 1) * riemannZeta s := by
  apply zetaRegularized_eq s
  · intro h
    subst s
    exact hs rfl
  · intro h
    subst s
    exact hs rfl
  · intro hΓ
    rw [Complex.Gammaℝ_eq_zero_iff] at hΓ
    obtain ⟨n, hsn⟩ := hΓ
    apply hs
    simpa using congr_arg Complex.im hsn

theorem complex_Gamma_stirling_lower_bound
    (σ₁ σ₂ : ℝ) (hσ : σ₁ ≤ σ₂) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 2 ≤ |s.im| →
        |s.im| ^ (-A) * Real.exp (-(Real.pi / 2) * |s.im|) ≤
          ‖Complex.Gamma s‖ := by
  obtain ⟨D, _hD_pos, hD⟩ := complex_stirling_bound σ₁ σ₂ hσ
  let A : ℝ := max 0 (1 / 2 + D - σ₁)
  refine ⟨A, le_max_left _ _, fun s hs₁ hs₂ ht => ?_⟩
  let T : ℝ := |s.im|
  let L : ℝ := Real.log T
  have hT : 2 ≤ T := by simpa [T] using ht
  have hT_pos : 0 < T := by linarith
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by linarith)
  have him_ne : s.im ≠ 0 := by
    intro him
    rw [him, abs_zero] at ht
    norm_num at ht
  have hGamma_ne : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hsm
    apply him_ne
    simpa using congr_arg Complex.im hsm
  have hGamma_pos : 0 < ‖Complex.Gamma s‖ := norm_pos_iff.mpr hGamma_ne
  have hstirling := hD s hs₁ hs₂ ht
  have herror₀ := (abs_le.mp hstirling).1
  have herror : -D * L ≤
      Real.log ‖Complex.Gamma s‖ -
        ((s.re - 1 / 2) * L - T * (Real.pi / 2)) := by
    dsimp [T, L]
    nlinarith
  have hcoeff : -A ≤ s.re - 1 / 2 - D := by
    have hA : 1 / 2 + D - σ₁ ≤ A := le_max_right _ _
    linarith
  have hlog :
      (-A) * L - (Real.pi / 2) * T ≤
        Real.log ‖Complex.Gamma s‖ := by
    calc
      (-A) * L - (Real.pi / 2) * T
          ≤ (s.re - 1 / 2 - D) * L - (Real.pi / 2) * T := by
            gcongr
      _ ≤ Real.log ‖Complex.Gamma s‖ := by linarith
  calc
    |s.im| ^ (-A) * Real.exp (-(Real.pi / 2) * |s.im|)
        = Real.exp ((-A) * L - (Real.pi / 2) * T) := by
          rw [Real.rpow_def_of_pos (by simpa [T] using hT_pos), ← Real.exp_add]
          dsimp [T, L]
          congr 1
          ring_nf
    _ ≤ Real.exp (Real.log ‖Complex.Gamma s‖) := Real.exp_le_exp.mpr hlog
    _ = ‖Complex.Gamma s‖ := Real.exp_log hGamma_pos

theorem norm_xiFunction_le_rpow_scratch
    (r : ℝ) (hr : 26 ≤ r) (s : ℂ) (hs : ‖s‖ ≤ r) :
    ‖xiFunction s‖ ≤ (r + 10) ^ (r + 13) := by
  have hmax : EntireFunction.maxModulus completedRiemannZeta₀ r ≤
      (r + 10) ^ (r + 10) := by
    let z : ℂ := (24 : ℕ)
    have hz_re : (1 : ℝ) ≤ (completedRiemannZeta₀ z).re := by
      simpa [z] using EntireFunction.completedZeta₀_even_re_lower 0
    have hz_radius : ‖z‖ ≤ r := by
      dsimp [z]
      norm_num
      linarith
    have hM_one : (1 : ℝ) ≤ EntireFunction.maxModulus completedRiemannZeta₀ r :=
      hz_re.trans ((Complex.re_le_norm _).trans
        (EntireFunction.norm_le_maxModulus completedRiemannZeta₀
          differentiable_completedZeta₀ z r (by linarith) hz_radius))
    have hlog := EntireFunction.log_maxModulus_completedZeta_le r (by linarith)
    calc
      EntireFunction.maxModulus completedRiemannZeta₀ r
          = Real.exp (Real.log (EntireFunction.maxModulus completedRiemannZeta₀ r)) :=
            (Real.exp_log (lt_of_lt_of_le zero_lt_one hM_one)).symm
      _ ≤ Real.exp ((r + 10) * Real.log (r + 10)) := Real.exp_le_exp.mpr hlog
      _ = (r + 10) ^ (r + 10) := by
        rw [Real.rpow_def_of_pos (by linarith)]
        congr 1
        ring_nf
  let R := r + 10
  let L := R ^ R
  have hr₀ : 0 ≤ r := by linarith
  have hR₁ : (1 : ℝ) ≤ R := by dsimp [R]; linarith
  have hRpos : 0 < R := zero_lt_one.trans_le hR₁
  have hL₁ : (1 : ℝ) ≤ L := Real.one_le_rpow hR₁ (by dsimp [R]; linarith)
  have hLambda : ‖completedRiemannZeta₀ s‖ ≤ L := by
    calc
      ‖completedRiemannZeta₀ s‖ ≤ EntireFunction.maxModulus completedRiemannZeta₀ r :=
        EntireFunction.norm_le_maxModulus completedRiemannZeta₀
          differentiable_completedZeta₀ s r (by linarith) hs
      _ ≤ (r + 10) ^ (r + 10) := hmax
      _ = L := by rfl
  have hs₁ : ‖s - 1‖ ≤ r + 1 := by
    calc
      ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ r + 1 := by norm_num; linarith
  have hcoeff : (1 / 2 : ℝ) * r * (r + 1) + 1 / 2 ≤ R ^ 3 := by
    have hfirst : (1 / 2 : ℝ) * r * (r + 1) ≤ (1 / 2 : ℝ) * R ^ 3 := by
      calc
        (1 / 2 : ℝ) * r * (r + 1) = (1 / 2 : ℝ) * r * (r + 1) * 1 := by ring
        _ ≤ (1 / 2 : ℝ) * R * R * R := by
          gcongr <;> dsimp [R] <;> linarith
        _ = (1 / 2 : ℝ) * R ^ 3 := by ring
    have hhalf : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) * R ^ 3 := by
      calc
        (1 / 2 : ℝ) = (1 / 2 : ℝ) * 1 := by ring
        _ ≤ (1 / 2 : ℝ) * R ^ 3 :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ hR₁) (by norm_num)
    linarith
  have hnorm : ‖xiFunction s‖ ≤
      ((1 / 2 : ℝ) * r * (r + 1) + 1 / 2) * L := by
    rw [xiFunction]
    calc
      ‖(1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + 1 / 2‖
          ≤ ‖(1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s‖ +
              ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
      _ = (1 / 2 : ℝ) * ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖ + 1 / 2 := by
        norm_num [norm_mul]
      _ ≤ (1 / 2 : ℝ) * r * (r + 1) * L + 1 / 2 := by gcongr
      _ ≤ ((1 / 2 : ℝ) * r * (r + 1) + 1 / 2) * L := by nlinarith
  calc
    ‖xiFunction s‖ ≤ ((1 / 2 : ℝ) * r * (r + 1) + 1 / 2) * L := hnorm
    _ ≤ R ^ 3 * L := mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = (r + 10) ^ (r + 13) := by
      calc
        R ^ 3 * L = R ^ 3 * R ^ R := by rfl
        _ = R ^ (3 : ℝ) * R ^ R :=
          congrArg (fun x : ℝ => x * R ^ R) (Real.rpow_natCast R 3).symm
        _ = R ^ ((3 : ℝ) + R) := (Real.rpow_add hRpos (3 : ℝ) R).symm
        _ = (r + 10) ^ (r + 13) := by
          dsimp [R]
          congr 1
          ring_nf

theorem norm_zetaRegularized_le_exp_quadratic_scratch
    (σ₁ σ₂ : ℝ) (hσ : σ₁ ≤ σ₂) :
    ∃ D K : ℝ, 0 < D ∧ 0 < K ∧
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 4 ≤ |s.im| →
        ‖zetaRegularized s‖ ≤ D * Real.exp (K * |s.im| ^ 2) := by
  obtain ⟨A, C, hA, hC, hGamma⟩ :=
    norm_Gammaℝ_inv_stirling_upper_bound_scratch σ₁ σ₂ hσ
  let M : ℝ := max |σ₁| |σ₂|
  let Q : ℝ := M + 35
  let K : ℝ := (1 + Q / 4) ^ 2 + A / 4 + Real.pi / 16
  have hM : 0 ≤ M := le_trans (abs_nonneg σ₁) (le_max_left _ _)
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hK : 0 < K := by
    dsimp [K]
    have hsq : 0 < (1 + Q / 4) ^ 2 := sq_pos_of_pos (by positivity)
    positivity
  refine ⟨2 * C, K, by positivity, hK, fun s hs₁ hs₂ ht ↦ ?_⟩
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
  have hxi_raw := norm_xiFunction_le_rpow_scratch r hr s hs_norm
  have hU : 0 < U := by dsimp [U]; linarith
  have hV : 0 < V := by dsimp [V]; linarith
  have hr_base : r + 10 = U := by dsimp [r, U]; ring
  have hr_exp : r + 13 = V := by dsimp [r, V, Q]; ring
  have hUV : U ≤ V := by dsimp [U, V, Q]; linarith
  have hxi : ‖xiFunction s‖ ≤ Real.exp (V ^ 2) := by
    calc
      ‖xiFunction s‖ ≤ (r + 10) ^ (r + 13) := hxi_raw
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
  rw [zetaRegularized]
  calc
    ‖2 * xiFunction s * (Complex.Gammaℝ s)⁻¹‖
        = 2 * ‖xiFunction s‖ * ‖(Complex.Gammaℝ s)⁻¹‖ := by
          norm_num [norm_mul]
    _ ≤ 2 * Real.exp (V ^ 2) *
          (C * T ^ A * Real.exp (Real.pi / 4 * T)) := by
            gcongr
    _ ≤ 2 * Real.exp (V ^ 2) *
          (C * Real.exp (A * T) * Real.exp (Real.pi / 4 * T)) := by
            gcongr
    _ = (2 * C) * Real.exp
          (V ^ 2 + A * T + Real.pi / 4 * T) := by
            rw [Real.exp_add, Real.exp_add]
            ring
    _ ≤ (2 * C) * Real.exp (K * T ^ 2) := by
      gcongr
    _ = (2 * C) * Real.exp (K * |s.im| ^ 2) := by rfl

theorem zetaRegularized_vertical_strip_growth_scratch
    (a b : ℝ) (hab : a < b) :
    ∃ c < Real.pi / (b - a), ∃ B,
      zetaRegularized =O[
        comap (_root_.abs ∘ Complex.im) atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo a b)]
        fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
  obtain ⟨D, K, hD, hK, hquad⟩ :=
    norm_zetaRegularized_le_exp_quadratic_scratch a b hab.le
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
    ‖zetaRegularized z‖ ≤ D * Real.exp (K * T ^ 2) := by simpa [hzT] using hraw
    _ ≤ D * Real.exp (Real.exp (c * T)) := by
      gcongr
    _ = D * ‖Real.exp (1 * Real.exp (c * |z.im|))‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hzT]
      simp

theorem zetaRegularized_bounded_on_short_vertical_line_scratch
    (x T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = x → |s.im| ≤ T →
      ‖zetaRegularized s‖ ≤ C := by
  let K : Set ℂ := ({x} : Set ℝ) ×ℂ Set.Icc (-T) T
  have hK : IsCompact K := isCompact_singleton.reProdIm isCompact_Icc
  have hcont : ContinuousOn (fun z : ℂ ↦ ‖zetaRegularized z‖) K :=
    differentiable_zetaRegularized.continuous.norm.continuousOn
  obtain ⟨M, hM⟩ := bddAbove_def.mp (hK.bddAbove_image hcont)
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun s hsx hsT ↦ ?_⟩
  have hsK : s ∈ K := by
    constructor
    · simpa using hsx
    · exact (abs_le.mp hsT)
  exact (hM _ (Set.mem_image_of_mem _ hsK)).trans (le_max_right _ _)

theorem norm_le_linear_abs_im_on_vertical_line_scratch
    (x : ℝ) (s : ℂ) (hs : s.re = x) (ht : 2 ≤ |s.im|) :
    ‖s‖ ≤ (1 + |x| / 2) * |s.im| := by
  calc
    ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ = |x| + |s.im| := by rw [hs]
    _ ≤ (1 + |x| / 2) * |s.im| := by
      have := mul_nonneg (abs_nonneg x) (show 0 ≤ |s.im| - 2 by linarith)
      nlinarith

noncomputable def zetaPLNormalized (p : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  zetaRegularized s * (s - (p : ℂ))⁻¹ ^ N

theorem zetaPLNormalized_diffContOnCl_scratch
    (p a b : ℝ) (N : ℕ) (hp : p < a) :
    DiffContOnCl ℂ (zetaPLNormalized p N) (Complex.re ⁻¹' Set.Ioo a b) := by
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
  unfold zetaPLNormalized
  exact differentiable_zetaRegularized.differentiableOn.mul
    (((differentiable_id.sub_const (p : ℂ)).differentiableOn.inv hne).pow N)

theorem zetaPLNormalized_vertical_strip_growth_scratch
    (p a b : ℝ) (N : ℕ) (hp : p + 1 ≤ a) (hab : a < b) :
    ∃ c < Real.pi / (b - a), ∃ B,
      zetaPLNormalized p N =O[
        comap (_root_.abs ∘ Complex.im) atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo a b)]
        fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
  obtain ⟨c, hc, B, hG⟩ := zetaRegularized_vertical_strip_growth_scratch a b hab
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
      ‖zetaPLNormalized p N z‖ =
          ‖zetaRegularized z‖ * ‖(z - (p : ℂ))⁻¹‖ ^ N := by
            simp only [zetaPLNormalized, norm_mul, norm_pow]
      _ ≤ ‖zetaRegularized z‖ * 1 := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) hinv
      _ = 1 * ‖zetaRegularized z‖ := by ring)

end ArithmeticHodge.Analysis
