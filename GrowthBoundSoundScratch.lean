import CanonicalProductLowerScratch
import ArithmeticHodge.Analysis.BorelCaratheodory

open Complex Filter Topology Real Set Metric

namespace ArithmeticHodge.Analysis.EntireFunction

set_option autoImplicit false

/-- A direct, reusable form of the finite-order maximum-modulus estimate. -/
theorem log_maxModulus_eventually_le_rpow_of_order_lt
    (f : ℂ → ℂ) (alpha : ℝ)
    (horder : entireOrder f < (alpha : EReal)) :
    ∃ R₀ : ℝ, 1 < R₀ ∧ ∀ r : ℝ, R₀ ≤ r →
      Real.log (maxModulus f r) ≤ r ^ alpha := by
  have hev := eventually_lt_of_limsup_lt horder
  have hbound : ∀ᶠ r in Filter.atTop,
      Real.log (maxModulus f r) ≤ r ^ alpha := by
    apply (hev.and (Filter.eventually_ge_atTop 2)).mono
    intro r ⟨hr_limsup, hr_ge⟩
    have hr_gt1 : (1 : ℝ) < r := by linarith
    have hlogr : 0 < Real.log r := Real.log_pos hr_gt1
    have hr_limsup' :
        Real.log (Real.log (maxModulus f r)) / Real.log r < alpha := by
      exact_mod_cast hr_limsup
    by_cases hlogM : Real.log (maxModulus f r) ≤ 0
    · exact le_trans hlogM
        (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hr_gt1)) alpha)
    · push_neg at hlogM
      rw [show r ^ alpha = Real.exp (alpha * Real.log r) from by
        rw [rpow_def_of_pos (lt_trans zero_lt_one hr_gt1), mul_comm]]
      exact le_of_lt
        ((Real.log_lt_iff_lt_exp hlogM).mp
          ((div_lt_iff₀ hlogr).mp hr_limsup'))
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.mp hbound
  refine ⟨max R₁ 2, by linarith [le_max_right R₁ 2], ?_⟩
  intro r hr
  exact hR₁ r ((le_max_left R₁ 2).trans hr)

/-- On a sphere separated from every zero, the canonical product lower bound
turns a maximum-modulus bound for `f` into an upper bound for `Re g`. -/
theorem re_le_on_canonical_good_sphere
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (m : ℕ) (g : ℂ → ℂ) (a : ℕ → ℂ) (p : ℕ)
    (hfact : ∀ z : ℂ, f z = z ^ m * Complex.exp (g z) *
      ∏' n, weierstraßElementary p (z / a n))
    (beta alpha : ℝ)
    (hp_beta : (p : ℝ) < beta) (hbeta_alpha : beta < alpha)
    (hbeta_q : beta < (p : ℝ) + 1)
    (hsumm : Summable (fun n ↦ ‖a n‖⁻¹ ^ beta))
    (R : ℝ) (hR : 1 ≤ R)
    (hlogMax : Real.log (maxModulus f R) ≤ R ^ alpha)
    (hsep : ∀ w : ℂ, ‖w‖ = R → ∀ n, ‖a n‖⁻¹ ^ alpha ≤ ‖w - a n‖) :
    ∀ w : ℂ, ‖w‖ = R →
      (g w).re ≤
        (canonicalProductLowerConstant a p beta alpha + 1) * R ^ alpha := by
  have hbeta : 0 < beta := lt_of_le_of_lt (Nat.cast_nonneg p) hp_beta
  have halpha : 0 < alpha := hbeta.trans hbeta_alpha
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hconv : Summable (fun n ↦ ‖a n‖⁻¹ ^ ((p : ℝ) + 1)) :=
    summable_inv_norm_rpow_of_le a beta ((p : ℝ) + 1)
      hbeta hbeta_q.le hsumm
  have hK_nonneg : 0 ≤ canonicalProductLowerConstant a p beta alpha :=
    canonicalProductLowerConstant_nonneg a p beta alpha hp_beta hbeta_alpha
  intro w hw
  let P : ℂ := ∏' n, weierstraßElementary p (w / a n)
  have hw_ne : w ≠ 0 := by
    intro hw0
    rw [hw0, norm_zero] at hw
    linarith
  have hne : ∀ n, w / a n ≠ 1 := by
    intro n heq
    have han : a n ≠ 0 := by
      intro han
      simp [han] at heq
    have hwa : w = a n := (div_eq_one_iff_eq han).mp heq
    have hdelta : 0 < ‖a n‖⁻¹ ^ alpha :=
      Real.rpow_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr han)) alpha
    have h := hsep w hw n
    rw [hwa, sub_self, norm_zero] at h
    linarith
  have hP_ne : P ≠ 0 := by
    exact tprod_weierstraßElementary_ne_zero a p hconv w hne
  have hfw_ne : f w ≠ 0 := by
    rw [hfact w]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero m hw_ne)
      (Complex.exp_ne_zero (g w))) hP_ne
  have hnorm_f_le : ‖f w‖ ≤ maxModulus f R :=
    norm_le_maxModulus f hf w R hRpos hw.le
  have hlog_f_le : Real.log ‖f w‖ ≤ R ^ alpha :=
    (Real.log_le_log (norm_pos_iff.mpr hfw_ne) hnorm_f_le).trans hlogMax
  have hP_lower :
      -canonicalProductLowerConstant a p beta alpha * R ^ alpha ≤
        Real.log ‖P‖ := by
    exact canonicalProduct_log_norm_lower_on_good_sphere
      a p beta alpha hp_beta hbeta_alpha hbeta_q hsumm w R hw hR (hsep w hw)
  have hlog_factorization :
      Real.log ‖f w‖ =
        (m : ℝ) * Real.log R + (g w).re + Real.log ‖P‖ := by
    rw [hfact w]
    change Real.log ‖w ^ m * Complex.exp (g w) * P‖ = _
    rw [norm_mul, norm_mul,
      Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr (pow_ne_zero m hw_ne))
        (norm_ne_zero_iff.mpr (Complex.exp_ne_zero (g w))))
        (norm_ne_zero_iff.mpr hP_ne),
      Real.log_mul (norm_ne_zero_iff.mpr (pow_ne_zero m hw_ne))
        (norm_ne_zero_iff.mpr (Complex.exp_ne_zero (g w))),
      norm_pow, Real.log_pow, Complex.norm_exp, Real.log_exp, hw]
  have hmlog_nonneg : 0 ≤ (m : ℝ) * Real.log R :=
    mul_nonneg (Nat.cast_nonneg m) (Real.log_nonneg hR)
  rw [hlog_factorization] at hlog_f_le
  linarith

/-- **Sound real-part growth bound for a canonical factorization.**

The additional exponent `beta` records the genuinely necessary genus data:
`p < beta < alpha`, `beta < p+1`, and the inverse-`beta` power sum of the
zeros converges.  These hypotheses exclude the noncanonical factorization
counterexample to the old `re_bound_of_factorization` statement. -/
theorem re_bound_of_canonical_factorization
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (m : ℕ) (g : ℂ → ℂ) (a : ℕ → ℂ) (p : ℕ)
    (hg_diff : Differentiable ℂ g)
    (hfact : ∀ z : ℂ, f z = z ^ m * Complex.exp (g z) *
      ∏' n, weierstraßElementary p (z / a n))
    (beta alpha : ℝ)
    (hp_beta : (p : ℝ) < beta) (hbeta_alpha : beta < alpha)
    (hbeta_q : beta < (p : ℝ) + 1)
    (hsumm : Summable (fun n ↦ ‖a n‖⁻¹ ^ beta))
    (horder : entireOrder f < (alpha : EReal)) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : ℂ,
      (g z).re ≤ A * (1 + ‖z‖) ^ alpha := by
  have hbeta : 0 < beta := lt_of_le_of_lt (Nat.cast_nonneg p) hp_beta
  have halpha : 0 < alpha := hbeta.trans hbeta_alpha
  have hsumm_alpha : Summable (fun n ↦ ‖a n‖⁻¹ ^ alpha) :=
    summable_inv_norm_rpow_of_le a beta alpha hbeta hbeta_alpha.le hsumm
  obtain ⟨Rₑ, hRₑ, hlogMax⟩ :=
    log_maxModulus_eventually_le_rpow_of_order_lt f alpha horder
  obtain ⟨Rₒ, hRₒ, hgood⟩ :=
    canonicalProduct_exists_good_sphere a alpha hsumm_alpha
  let D : ℝ := max Rₑ Rₒ
  have hD_gt_one : 1 < D := hRₑ.trans_le (le_max_left Rₑ Rₒ)
  have hD_pos : 0 < D := zero_lt_one.trans hD_gt_one
  let K : ℝ := canonicalProductLowerConstant a p beta alpha
  have hK_nonneg : 0 ≤ K := by
    exact canonicalProductLowerConstant_nonneg a p beta alpha hp_beta hbeta_alpha
  let A : ℝ := (K + 1) * (4 * D) ^ alpha
  have hA_pos : 0 < A := by
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos (mul_pos (by norm_num) hD_pos) alpha)
  refine ⟨A, hA_pos, ?_⟩
  intro z
  let r : ℝ := D * (1 + ‖z‖)
  have hfactor_one : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hfactor_pos : 0 < 1 + ‖z‖ := zero_lt_one.trans_le hfactor_one
  have hr_pos : 0 < r := mul_pos hD_pos hfactor_pos
  have hD_le_r : D ≤ r := by
    calc
      D = D * 1 := by ring
      _ ≤ D * (1 + ‖z‖) := mul_le_mul_of_nonneg_left hfactor_one hD_pos.le
      _ = r := rfl
  have hRₑ_le_r : Rₑ ≤ r := (le_max_left Rₑ Rₒ).trans hD_le_r
  have hRₒ_le_r : Rₒ ≤ r := (le_max_right Rₑ Rₒ).trans hD_le_r
  obtain ⟨R, hR_lower, hR_upper, hsep⟩ := hgood r hRₒ_le_r
  have hr_le_R : r ≤ R := by linarith
  have hR_pos : 0 < R := hr_pos.trans_le hr_le_R
  have hR_one : 1 ≤ R := by
    exact le_trans hD_gt_one.le (hD_le_r.trans hr_le_R)
  have hRₑ_le_R : Rₑ ≤ R := hRₑ_le_r.trans hr_le_R
  have hboundary : ∀ w : ℂ, ‖w‖ = R →
      (g w).re ≤ (K + 1) * R ^ alpha := by
    simpa only [K] using re_le_on_canonical_good_sphere
      f hf m g a p hfact beta alpha hp_beta hbeta_alpha hbeta_q hsumm
      R hR_one (hlogMax R hRₑ_le_R)
      (fun w hw n ↦ (hsep w hw n).le)
  have hz_lt_r : ‖z‖ < r := by
    have hone_mul_lt : 1 * (1 + ‖z‖) < D * (1 + ‖z‖) :=
      mul_lt_mul_of_pos_right hD_gt_one hfactor_pos
    dsimp only [r]
    linarith
  have hz_lt_R : ‖z‖ < R := hz_lt_r.trans_le hr_le_R
  have hexp_bound :
      ‖(Complex.exp ∘ g) z‖ ≤ Real.exp ((K + 1) * R ^ alpha) := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      ((Complex.differentiable_exp.comp hg_diff).diffContOnCl)
    · intro w hw
      rw [frontier_ball (0 : ℂ) hR_pos.ne'] at hw
      simp only [Metric.mem_sphere, dist_zero_right] at hw
      simp only [Function.comp_apply, Complex.norm_exp]
      exact Real.exp_le_exp.mpr (hboundary w hw)
    · exact subset_closure (mem_ball_zero_iff.mpr hz_lt_R)
  have hz_re_le : (g z).re ≤ (K + 1) * R ^ alpha := by
    simpa only [Function.comp_apply, Complex.norm_exp, Real.exp_le_exp] using hexp_bound
  have hR_rpow : R ^ alpha ≤ (4 * r) ^ alpha :=
    Real.rpow_le_rpow hR_pos.le hR_upper halpha.le
  have hKR_rpow : (K + 1) * R ^ alpha ≤ (K + 1) * (4 * r) ^ alpha :=
    mul_le_mul_of_nonneg_left hR_rpow (by linarith)
  calc
    (g z).re ≤ (K + 1) * R ^ alpha := hz_re_le
    _ ≤ (K + 1) * (4 * r) ^ alpha := hKR_rpow
    _ = A * (1 + ‖z‖) ^ alpha := by
      have h4D_nonneg : 0 ≤ 4 * D := (mul_pos (by norm_num) hD_pos).le
      have hfactor_nonneg : 0 ≤ 1 + ‖z‖ := hfactor_pos.le
      rw [show 4 * r = (4 * D) * (1 + ‖z‖) by simp only [r]; ring,
        Real.mul_rpow h4D_nonneg hfactor_nonneg]
      simp only [A]
      ring

/-- Borel–Carathéodory upgrades the sound real-part estimate to a norm bound
with the same exponent. -/
theorem canonical_factorization_growth
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (m : ℕ) (g : ℂ → ℂ) (a : ℕ → ℂ) (p : ℕ)
    (hg_diff : Differentiable ℂ g)
    (hfact : ∀ z : ℂ, f z = z ^ m * Complex.exp (g z) *
      ∏' n, weierstraßElementary p (z / a n))
    (beta alpha : ℝ)
    (hp_beta : (p : ℝ) < beta) (hbeta_alpha : beta < alpha)
    (hbeta_q : beta < (p : ℝ) + 1)
    (hsumm : Summable (fun n ↦ ‖a n‖⁻¹ ^ beta))
    (horder : entireOrder f < (alpha : EReal)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖g z‖ ≤ C * (1 + ‖z‖) ^ alpha := by
  have hbeta : 0 < beta := lt_of_le_of_lt (Nat.cast_nonneg p) hp_beta
  have halpha : 0 < alpha := hbeta.trans hbeta_alpha
  obtain ⟨B, hB_pos, h_re⟩ := re_bound_of_canonical_factorization
    f hf m g a p hg_diff hfact beta alpha hp_beta hbeta_alpha hbeta_q hsumm horder
  let C₀ : ℝ := 2 * B * 3 ^ alpha + 3 * ‖g 0‖
  refine ⟨max C₀ 1, lt_max_of_lt_right one_pos, ?_⟩
  intro z
  let R : ℝ := 2 * (1 + ‖z‖)
  have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  have hR_pos : 0 < R := by positivity
  have hz_R : z ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  have hR_sub : 0 < R - ‖z‖ := by linarith
  have h_maps : MapsTo g (Metric.ball 0 R)
      {w : ℂ | w.re ≤ B * (1 + R) ^ alpha} := by
    intro w hw
    simp only [mem_setOf_eq]
    have hw_norm : ‖w‖ < R := by
      rwa [Metric.mem_ball, dist_zero_right] at hw
    calc
      (g w).re ≤ B * (1 + ‖w‖) ^ alpha := h_re w
      _ ≤ B * (1 + R) ^ alpha := by gcongr
  let M : ℝ := B * (1 + R) ^ alpha
  have hM_pos : 0 < M := by positivity
  have h_bc := Complex.borelCaratheodory hM_pos hg_diff.differentiableOn
    h_maps hR_pos hz_R
  have h1R : 1 + R ≤ 3 * (1 + ‖z‖) := by linarith
  have h1R_alpha : (1 + R) ^ alpha ≤ (3 * (1 + ‖z‖)) ^ alpha :=
    Real.rpow_le_rpow (by positivity) h1R halpha.le
  have h3alpha :
      (3 * (1 + ‖z‖)) ^ alpha = 3 ^ alpha * (1 + ‖z‖) ^ alpha :=
    Real.mul_rpow (by norm_num) (by linarith)
  have h1alpha : 1 ≤ (1 + ‖z‖) ^ alpha := by
    calc
      (1 : ℝ) = 1 ^ alpha := (one_rpow alpha).symm
      _ ≤ (1 + ‖z‖) ^ alpha :=
        Real.rpow_le_rpow (by norm_num) (by linarith) halpha.le
  have ht₁ : 2 * M * ‖z‖ / (R - ‖z‖) ≤ 2 * M := by
    rw [div_le_iff₀ hR_sub]
    nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + R) alpha]
  have ht₂ : ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖) ≤ 3 * ‖g 0‖ := by
    rw [div_le_iff₀ hR_sub]
    nlinarith [norm_nonneg (g 0)]
  have hM_bound : M ≤ B * 3 ^ alpha * (1 + ‖z‖) ^ alpha := by
    show B * (1 + R) ^ alpha ≤ B * 3 ^ alpha * (1 + ‖z‖) ^ alpha
    calc
      B * (1 + R) ^ alpha ≤ B * (3 ^ alpha * (1 + ‖z‖) ^ alpha) := by
        gcongr
        linarith [h3alpha ▸ h1R_alpha]
      _ = B * 3 ^ alpha * (1 + ‖z‖) ^ alpha := by ring
  calc
    ‖g z‖ ≤
        2 * M * ‖z‖ / (R - ‖z‖) +
          ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖) := h_bc
    _ ≤ 2 * M + 3 * ‖g 0‖ := by linarith
    _ ≤ 2 * (B * 3 ^ alpha * (1 + ‖z‖) ^ alpha) + 3 * ‖g 0‖ := by
      nlinarith
    _ = (2 * B * 3 ^ alpha) * (1 + ‖z‖) ^ alpha + 3 * ‖g 0‖ := by
      ring
    _ ≤ (2 * B * 3 ^ alpha) * (1 + ‖z‖) ^ alpha +
          3 * ‖g 0‖ * (1 + ‖z‖) ^ alpha := by
      nlinarith [le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ 3 * ‖g 0‖) h1alpha]
    _ = C₀ * (1 + ‖z‖) ^ alpha := by ring
    _ ≤ max C₀ 1 * (1 + ‖z‖) ^ alpha := by
      nlinarith [le_max_left C₀ 1,
        Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + ‖z‖) alpha]

end ArithmeticHodge.Analysis.EntireFunction

#print axioms ArithmeticHodge.Analysis.EntireFunction.re_le_on_canonical_good_sphere
#print axioms ArithmeticHodge.Analysis.EntireFunction.re_bound_of_canonical_factorization
#print axioms ArithmeticHodge.Analysis.EntireFunction.canonical_factorization_growth
