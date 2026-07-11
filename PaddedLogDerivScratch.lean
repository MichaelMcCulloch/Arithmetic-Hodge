import ArithmeticHodge.Analysis.EntireFunction.Hadamard

open Complex Filter Topology Metric Set Polynomial

namespace ArithmeticHodge.Analysis.EntireFunction

noncomputable def zeroLogDerivTerm (zeros : ℕ → ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  if zeros n = 0 then 0 else 1 / (z - zeros n) + 1 / zeros n

theorem hadamard_logDeriv_padded (m : ℕ) (a b : ℂ) (zeros : ℕ → ℂ)
    (hconv : Summable (fun n => (‖zeros n‖⁻¹) ^ (2 : ℝ)))
    (z : ℂ) (hz : z ≠ 0) (hzn : ∀ n, zeros n ≠ 0 → z ≠ zeros n) :
    let f := fun z => z ^ m * Complex.exp (a + b * z) *
      ∏' n, weierstraßElementary 1 (z / zeros n)
    deriv f z / f z = (m : ℂ) / z + b +
      ∑' n, zeroLogDerivTerm zeros z n := by
  intro f
  -- We decompose f = f₁ * f₂ * f₃ where:
  --   f₁(z) = z^m,  f₂(z) = exp(a + bz),  f₃(z) = ∏' n, E₁(z/aₙ)
  set f₁ : ℂ → ℂ := fun z => z ^ m with hf₁_def
  set f₂ : ℂ → ℂ := fun z => Complex.exp (a + b * z) with hf₂_def
  set f₃ : ℂ → ℂ := fun z => ∏' n, weierstraßElementary 1 (z / zeros n) with hf₃_def
  -- Key nonvanishing conditions
  have hf₁_ne : f₁ z ≠ 0 := pow_ne_zero m hz
  have hf₂_ne : f₂ z ≠ 0 := Complex.exp_ne_zero _
  have hf₃_ne : f₃ z ≠ 0 := by
    simp only [hf₃_def]
    have hconv' : Summable (fun n => (‖zeros n‖⁻¹) ^ ((1 : ℕ) + 1 : ℝ)) := by
      convert hconv using 2; norm_num
    apply tprod_weierstraßElementary_ne_zero zeros 1 hconv' z
    intro n
    by_cases h0 : zeros n = 0
    · simp [h0]
    · exact fun heq => absurd (div_eq_one_iff_eq h0 |>.mp heq) (hzn n h0)
  have hf_eq : f = fun z => f₁ z * f₂ z * f₃ z := by ext; rfl
  -- Log derivative of f₁: d/dz log(z^m) = m/z
  have hlogderiv₁ : deriv f₁ z / f₁ z = (m : ℂ) / z := by
    simp only [hf₁_def]
    rcases m with _ | m
    · simp
    · have hd : HasDerivAt (fun z : ℂ => z ^ (m + 1))
          ((↑(m + 1) : ℂ) * z ^ m) z := hasDerivAt_pow (m + 1) z
      rw [hd.deriv]
      rw [Nat.cast_succ]
      field_simp
      ring
  -- Log derivative of f₂: d/dz(a + bz) = b, so d/dz exp(a+bz)/exp(a+bz) = b
  have hlogderiv₂ : deriv f₂ z / f₂ z = b := by
    have h_lin : HasDerivAt (fun z => a + b * z) b z := by
      have := (hasDerivAt_const z a).add ((hasDerivAt_const z b).mul (hasDerivAt_id z))
      simp at this
      exact this
    have hd : HasDerivAt f₂ (Complex.exp (a + b * z) * b) z :=
      h_lin.cexp
    rw [hd.deriv]
    simp only [hf₂_def]
    have hne : Complex.exp (a + b * z) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  -- Log derivative of f₃: ∑' n, (1/(z - aₙ) + 1/aₙ)
  have hlogderiv₃ : deriv f₃ z / f₃ z =
      ∑' n, zeroLogDerivTerm zeros z n := by
    -- Use logDeriv_tprod_eq_tsum from Mathlib
    have hconv' : Summable (fun n => (‖zeros n‖⁻¹) ^ ((1 : ℕ) + 1 : ℝ)) := by
      convert hconv using 2; norm_num
    -- Set up the factors
    set fac : ℕ → ℂ → ℂ := fun n w => weierstraßElementary 1 (w / zeros n)
    have hf₃_eq : f₃ = fun w => ∏' n, fac n w := by ext w; rfl
    set s := ball (0 : ℂ) (‖z‖ + 1)
    have hs_open : IsOpen s := isOpen_ball
    have hz_s : z ∈ s := mem_ball_zero_iff.mpr (by linarith)
    -- Each factor is nonzero at z
    have hfne : ∀ n, fac n z ≠ 0 := by
      intro n
      by_cases ha : zeros n = 0
      · simp [fac, ha, weierstraßElementary_zero]
      · exact weierstraßElementary_ne_zero 1 _ (by
          intro heq
          exact hzn n ha (div_eq_one_iff_eq ha |>.mp heq))
    -- Each factor is differentiable on s
    have hfd : ∀ n, DifferentiableOn ℂ (fac n) s := fun n =>
      ((weierstraßElementary_differentiable 1).comp (differentiable_id.div_const _)).differentiableOn
    -- MultipliableLocallyUniformlyOn
    have hmlu : MultipliableLocallyUniformlyOn fac s :=
      multipliableLocallyUniformlyOn_weierstraß zeros 1 hconv' s hs_open
    -- Product nonzero
    have hprod_ne : ∏' n, fac n z ≠ 0 := hf₃_ne
    -- Per-term logDeriv computation
    have hper_term : ∀ n, logDeriv (fac n) z = zeroLogDerivTerm zeros z n := by
      intro n
      by_cases ha : zeros n = 0
      · simp [zeroLogDerivTerm, fac, ha, logDeriv, weierstraßElementary_zero]
      rw [zeroLogDerivTerm, if_neg ha]
      have hza : z / zeros n ≠ 1 := by
        intro heq; exact hzn n ha (div_eq_one_iff_eq ha |>.mp heq)
      have hza_ne : z - zeros n ≠ 0 := sub_ne_zero.mpr (hzn n ha)
      have hE_ne := weierstraßElementary_ne_zero 1 (z / zeros n) hza
      -- Compute deriv via chain rule
      have h_div : HasDerivAt (fun w => w / zeros n) ((zeros n)⁻¹) z := by
        simpa using (hasDerivAt_id z).div_const (zeros n)
      have hcomp : HasDerivAt (fac n)
          (deriv (weierstraßElementary 1) (z / zeros n) * (zeros n)⁻¹) z :=
        (weierstraßElementary_differentiable 1).differentiableAt.hasDerivAt.comp z h_div
      simp only [logDeriv, Pi.div_apply, fac]
      rw [hcomp.deriv]
      -- Eliminate deriv using logDeriv identity: deriv E₁ w / E₁ w = w/(w-1)
      have hld := weierstraßElementary_one_logDeriv (z / zeros n) hza
      -- Rewrite deriv E₁ (z/a) = (z/a)/(z/a - 1) * E₁(z/a)
      have hderiv_eq : deriv (weierstraßElementary 1) (z / zeros n) =
          (z / zeros n) / (z / zeros n - 1) * weierstraßElementary 1 (z / zeros n) :=
        (div_eq_iff hE_ne).mp hld
      rw [hderiv_eq]
      have hza_sub : z / zeros n - 1 ≠ 0 := sub_ne_zero.mpr hza
      field_simp [hE_ne, ha, hza_ne, hza_sub]
      ring
    -- Summability of logDerivs
    have hm_summ : Summable fun n => logDeriv (fac n) z := by
      simp_rw [hper_term]
      -- 1/(z - zeros n) + 1/zeros n = z / (zeros n * (z - zeros n))
      -- For large n, this is O(‖zeros n‖⁻²), summable from hconv
      have hconv_pow : Summable (fun n => ‖zeros n‖⁻¹ ^ 2) := by
        have : (fun n => (‖zeros n‖⁻¹) ^ (2 : ℝ)) = fun n => ‖zeros n‖⁻¹ ^ 2 := by
          ext n; rw [← Real.rpow_natCast]; norm_cast
        rwa [this] at hconv
      apply (hconv_pow.mul_left (2 * ‖z‖)).of_norm_bounded_eventually
      rw [Nat.cofinite_eq_atTop]
      have htend := (Nat.cofinite_eq_atTop ▸ hconv_pow.tendsto_atTop_zero :
        Tendsto (fun n => ‖zeros n‖⁻¹ ^ 2) atTop (nhds 0))
      set c := 1 / (2 * ‖z‖ + 1)
      apply (htend.eventually (Iio_mem_nhds (show (0 : ℝ) < c ^ 2 by positivity))).mono
      intro n hn
      have hinv_lt : ‖zeros n‖⁻¹ < c := lt_of_pow_lt_pow_left₀ 2 (by positivity) hn
      by_cases ha : zeros n = 0
      · simp [zeroLogDerivTerm, ha]
      have hzn_ne : z - zeros n ≠ 0 := sub_ne_zero.mpr (hzn n ha)
      -- ‖zeros n‖ > 2‖z‖ + 1 > 0
      have ha_pos : (0 : ℝ) < ‖zeros n‖ := norm_pos_iff.mpr ha
      have hzn_large : 2 * ‖z‖ + 1 < ‖zeros n‖ := by
        have hc_eq : c = (2 * ‖z‖ + 1)⁻¹ := by simp [c, one_div]
        rw [hc_eq] at hinv_lt
        exact (inv_lt_inv₀ ha_pos (by positivity)).mp hinv_lt
      -- Reverse triangle: ‖z - zeros n‖ ≥ ‖zeros n‖ - ‖z‖ ≥ ‖zeros n‖/2
      have hza_lower : ‖zeros n‖ / 2 ≤ ‖z - zeros n‖ := by
        have h1 : ‖zeros n‖ - ‖z‖ ≤ ‖z - zeros n‖ := by
          have := norm_add_le (zeros n - z) z
          rw [sub_add_cancel] at this
          linarith [norm_sub_rev (zeros n) z]
        linarith
      -- The bound: ‖1/(z-a) + 1/a‖ ≤ 2‖z‖ · ‖a‖⁻²
      rw [zeroLogDerivTerm, if_neg ha]
      rw [show (1 : ℂ) / (z - zeros n) + 1 / zeros n = z / (zeros n * (z - zeros n)) by
        field_simp; ring]
      rw [norm_div, norm_mul]
      have hd_pos : 0 < ‖zeros n‖ * ‖z - zeros n‖ :=
        mul_pos ha_pos (norm_pos_iff.mpr hzn_ne)
      have hd2_pos : 0 < ‖zeros n‖ * (‖zeros n‖ / 2) := by positivity
      calc ‖z‖ / (‖zeros n‖ * ‖z - zeros n‖)
          ≤ ‖z‖ / (‖zeros n‖ * (‖zeros n‖ / 2)) := by
            exact div_le_div_of_nonneg_left (norm_nonneg z) hd2_pos
              (mul_le_mul_of_nonneg_left hza_lower (le_of_lt ha_pos))
          _ = 2 * ‖z‖ * ‖zeros n‖⁻¹ ^ 2 := by
            field_simp
    -- Apply logDeriv_tprod_eq_tsum
    have key := logDeriv_tprod_eq_tsum hs_open hz_s hfne hfd hm_summ hmlu hprod_ne
    -- key : logDeriv (∏' i, fac i ·) z = ∑' i, logDeriv (fac i) z
    -- Convert to deriv/f form
    show logDeriv f₃ z = _
    rw [show f₃ = (∏' i, fac i ·) from hf₃_eq, key]
    exact funext hper_term ▸ rfl
  -- Combine: log derivative of a product f₁·f₂·f₃ is sum of log derivatives
  have hf₁_diff : DifferentiableAt ℂ f₁ z :=
    (differentiable_pow m).differentiableAt
  have hf₂_diff : DifferentiableAt ℂ f₂ z := by
    apply DifferentiableAt.cexp
    exact (differentiableAt_const a).add ((differentiableAt_const b).mul differentiableAt_id)
  have hf₃_diff : DifferentiableAt ℂ f₃ z := by
    simp only [hf₃_def]
    have hconv' : Summable (fun n => (‖zeros n‖⁻¹) ^ ((1 : ℕ) + 1 : ℝ)) := by
      convert hconv using 2; norm_num
    exact (tprod_weierstraßElementary_differentiable zeros 1 hconv').differentiableAt
  rw [hf_eq]
  set g₁₂ : ℂ → ℂ := fun z => f₁ z * f₂ z with hg₁₂_def
  have hg₁₂_diff : DifferentiableAt ℂ g₁₂ z := hf₁_diff.mul hf₂_diff
  have hg₁₂_ne : g₁₂ z ≠ 0 := mul_ne_zero hf₁_ne hf₂_ne
  have hf_eq2 : f = fun z => g₁₂ z * f₃ z := by ext w; simp [hf_eq, g₁₂, f₁, f₂, f₃]
  have hf_val : f z = g₁₂ z * f₃ z := by rw [hf_eq2]
  have hf_ne : f z ≠ 0 := by rw [hf_val]; exact mul_ne_zero hg₁₂_ne hf₃_ne
  have hf_deriv : deriv f z = deriv g₁₂ z * f₃ z + g₁₂ z * deriv f₃ z := by
    rw [hf_eq2]; exact deriv_mul hg₁₂_diff hf₃_diff
  have hg₁₂_deriv : deriv g₁₂ z = deriv f₁ z * f₂ z + f₁ z * deriv f₂ z := by
    exact deriv_mul hf₁_diff hf₂_diff
  have key : deriv f z / f z = deriv f₁ z / f₁ z + deriv f₂ z / f₂ z + deriv f₃ z / f₃ z := by
    rw [hf_deriv, hf_val, hg₁₂_deriv, hg₁₂_def]
    field_simp
  rw [key, hlogderiv₁, hlogderiv₂, hlogderiv₃]

end ArithmeticHodge.Analysis.EntireFunction
