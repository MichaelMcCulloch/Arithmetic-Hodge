/-
  Growth bound on the logarithmic part of Weierstraß factorization.

  This file provides the key estimate needed by the Hadamard factorization:
  given f = z^m * exp(g) * ∏ E_p(z/aₙ) where f has finite order ρ,
  the function g satisfies ‖g(z)‖ ≤ C * (1 + ‖z‖)^α for any α > ρ.

  Import chain: Defs → ZeroSummability → WeierstraßProduct → GrowthBound → Hadamard

  ## Sorry inventory

  Three targeted sorries:
  1. `order_implies_logMax_bound` — extract maxModulus bound from limsup
     definition of `entireOrder`. Proof sketch: `eventually_lt_of_limsup_lt`,
     then exponentiate. Blocked on `norm_le_maxModulus` being private.
  2. `re_bound_of_factorization` — combine f's growth bound with Weierstraß
     product lower bound to get `Re(g) ≤ O(r^α)`. Blocked on product lower
     bound infrastructure.
  3. `entireOrder_nonneg'` — `0 ≤ entireOrder f` for non-zero entire functions.
     Proved in Order.lean as private; needs to be exported.
-/

import ArithmeticHodge.Analysis.EntireFunction.WeierstraßProduct
import ArithmeticHodge.Analysis.BorelCaratheodory

open Complex Filter Topology Real ArithmeticHodge.Analysis.EntireFunction

namespace ArithmeticHodge.Analysis.EntireFunction

/-! ### Step 1: Finite order implies maxModulus growth bound -/

/-- If `f` has finite order and `α > (entireOrder f).toReal`, then eventually
    `log (maxModulus f r) ≤ r ^ α`. -/
private lemma order_implies_logMax_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (_hf_ne : ¬ f = 0) (hfin : HasFiniteOrder f) (α : ℝ)
    (hα : (entireOrder f).toReal < α) :
    ∃ R₀ : ℝ, 1 < R₀ ∧ ∀ r : ℝ, R₀ ≤ r → Real.log (maxModulus f r) ≤ r ^ α := by
  -- entireOrder f < ↑α in EReal
  have hord_lt : entireOrder f < (α : EReal) := by
    have hne_top : entireOrder f ≠ ⊤ := ne_of_lt hfin
    by_cases hbot : entireOrder f = ⊥
    · rw [hbot]; exact EReal.bot_lt_coe α
    · rw [← EReal.coe_toReal hne_top hbot]
      exact EReal.coe_lt_coe_iff.mpr hα
  -- From limsup < α: eventually log(log M(f,r))/log r < α
  have h_ev : ∀ᶠ r in Filter.atTop,
      (↑(Real.log (Real.log (maxModulus f r)) / Real.log r) : EReal) < (α : EReal) :=
    eventually_lt_of_limsup_lt hord_lt
  -- Convert EReal < to ℝ <
  have h_ev_real : ∀ᶠ r in Filter.atTop,
      Real.log (Real.log (maxModulus f r)) / Real.log r < α := by
    apply h_ev.mono; intro r hr; rwa [EReal.coe_lt_coe_iff] at hr
  -- Combine with r > 1
  obtain ⟨R₀', hR₀'⟩ := eventually_atTop.mp (h_ev_real.and
    (eventually_atTop.mpr ⟨2, fun r hr => show (1 : ℝ) < r by linarith⟩))
  refine ⟨max R₀' 2, by linarith [le_max_right R₀' 2], fun r hr => ?_⟩
  obtain ⟨h_ratio, h_r_gt1⟩ := hR₀' r (le_trans (le_max_left _ _) hr)
  have hlog_r_pos : 0 < Real.log r := Real.log_pos h_r_gt1
  have hM_nonneg : 0 ≤ maxModulus f r := by
    -- maxModulus f r = ⨆ z, ⨆ _ : ‖z‖ ≤ r, ‖f z‖ ≥ ‖f 0‖ ≥ 0
    unfold maxModulus
    have hr' : 0 < r := by linarith
    have h0r : ‖(0 : ℂ)‖ ≤ r := by simp; linarith
    have hcpt : IsCompact (Metric.closedBall (0 : ℂ) r) := isCompact_closedBall 0 r
    obtain ⟨C, hC⟩ := (hcpt.image_of_continuousOn hf.continuous.norm.continuousOn).bddAbove
    have hbdd : BddAbove (Set.range fun (w : ℂ) => ⨆ (_ : ‖w‖ ≤ r), ‖f w‖) := ⟨C, by
      rintro b ⟨w, rfl⟩
      by_cases hw : ‖w‖ ≤ r
      · simp only [ciSup_pos hw]
        exact hC ⟨w, by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero], rfl⟩
      · simp only [ciSup_neg hw, Real.sSup_empty]
        exact le_trans (le_refl 0) (le_trans (norm_nonneg (f 0))
          (hC ⟨0, by simp [Metric.mem_closedBall, hr'.le], rfl⟩))⟩
    calc (0 : ℝ) ≤ ‖f 0‖ := norm_nonneg _
      _ ≤ ⨆ (_ : ‖(0 : ℂ)‖ ≤ r), ‖f 0‖ :=
        le_ciSup ⟨‖f 0‖, fun b ⟨_, hb⟩ => hb ▸ le_refl _⟩ h0r
      _ ≤ ⨆ (z : ℂ), ⨆ (_ : ‖z‖ ≤ r), ‖f z‖ := le_ciSup hbdd 0
  by_cases hlogM : Real.log (maxModulus f r) ≤ 0
  · exact le_trans hlogM (rpow_nonneg (by linarith : (0 : ℝ) ≤ r) α)
  · push_neg at hlogM
    have hM_pos : 0 < maxModulus f r := by
      by_contra h; push_neg at h
      exact absurd (le_antisymm h hM_nonneg ▸ hlogM) (by simp [Real.log_zero])
    have h_loglogM : Real.log (Real.log (maxModulus f r)) < α * Real.log r :=
      (div_lt_iff₀ hlog_r_pos).mp h_ratio
    -- log(log M) < α * log r = log(r^α)
    rw [← Real.log_rpow (by linarith : 0 < r)] at h_loglogM
    -- log(log M) < log(r^α), and log M > 0, r^α > 0
    -- so log M < r^α
    have hrα_pos : 0 < r ^ α := rpow_pos_of_pos (by linarith) α
    -- h_loglogM : log(log M) < log(r^α)
    -- Since log M > 0 and r^α > 0, log is strictly monotone:
    -- log(log M) < log(r^α) implies log M < r^α
    exact le_of_lt ((Real.log_lt_log_iff hlogM hrα_pos).mp h_loglogM)

/-! ### Step 2: Real-part bound on g -/

/-- Given the Weierstraß factorization, `Re(g(z)) ≤ A * (1 + ‖z‖)^α`. -/
private lemma re_bound_of_factorization (f : ℂ → ℂ) (_hf : Differentiable ℂ f)
    (_hf_ne : ¬ f = 0) (_hfin : HasFiniteOrder f)
    (_m : ℕ) (g : ℂ → ℂ) (_a : ℕ → ℂ) (_p : ℕ)
    (_hg_diff : Differentiable ℂ g)
    (_hfact : ∀ z : ℂ, f z = z ^ _m * Complex.exp (g z) *
      ∏' n, weierstraßElementary _p (z / _a n))
    (_hsumm : Summable (fun n => (‖_a n‖⁻¹) ^ ((_p : ℝ) + 1)))
    (α : ℝ) (_hα : (entireOrder f).toReal < α) :
    ∃ (A : ℝ), 0 < A ∧ ∀ z : ℂ, (g z).re ≤ A * (1 + ‖z‖) ^ α := by
  sorry

/-! ### Step 3: Assemble via Borel-Carathéodory -/

theorem weierstraß_quotient_growth (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) (hfin : HasFiniteOrder f)
    (hord_nn : (0 : EReal) ≤ entireOrder f)
    (m : ℕ) (g : ℂ → ℂ) (a : ℕ → ℂ) (p : ℕ)
    (hg_diff : Differentiable ℂ g)
    (hfact : ∀ z : ℂ, f z = z ^ m * Complex.exp (g z) *
      ∏' n, weierstraßElementary p (z / a n))
    (hsumm : Summable (fun n => (‖a n‖⁻¹) ^ ((p : ℝ) + 1)))
    (α : ℝ) (hα : (entireOrder f).toReal < α) :
    ∃ (C : ℝ), 0 < C ∧ ∀ z : ℂ, ‖g z‖ ≤ C * (1 + ‖z‖) ^ α := by
  obtain ⟨A, hA_pos, h_re⟩ := re_bound_of_factorization f hf hf_ne hfin m g a p
    hg_diff hfact hsumm α hα
  -- 0 < α from entireOrder ≥ 0
  have hα_pos : 0 < α := by
    have hne_top : entireOrder f ≠ ⊤ := ne_of_lt hfin
    have := EReal.toReal_nonneg hord_nn
    linarith
  -- Apply Borel-Carathéodory pointwise
  set C₀ := 2 * A * 3 ^ α + 3 * ‖g 0‖
  refine ⟨max C₀ 1, lt_max_of_lt_right one_pos, fun z => ?_⟩
  set R := 2 * (1 + ‖z‖)
  have h_nz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hR_pos : (0 : ℝ) < R := by positivity
  have hz_R : z ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_zero_right]; linarith
  have hR_sub : (0 : ℝ) < R - ‖z‖ := by linarith
  -- Re(g(w)) ≤ A * (1+R)^α for w in ball 0 R
  -- (since 1+‖w‖ < 1+R for w ∈ ball 0 R)
  have h_maps : Set.MapsTo g (Metric.ball 0 R) {w : ℂ | w.re ≤ A * (1 + R) ^ α} := by
    intro w hw
    simp only [Set.mem_setOf_eq]
    have hw_norm : ‖w‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hw
    calc (g w).re ≤ A * (1 + ‖w‖) ^ α := h_re w
      _ ≤ A * (1 + R) ^ α := by gcongr <;> linarith
  -- BC bound
  set M := A * (1 + R) ^ α
  have hM_pos : (0 : ℝ) < M := by positivity
  have h_bc := Complex.borelCaratheodory hM_pos hg_diff.differentiableOn h_maps hR_pos hz_R
  -- Key: ‖z‖ ≤ R - ‖z‖ and R + ‖z‖ ≤ 3(R - ‖z‖)
  -- (1+R)^α = (3+2‖z‖)^α ≤ 3^α * (1+‖z‖)^α (since 3+2‖z‖ ≤ 3(1+‖z‖)))
  have h1R : 1 + R ≤ 3 * (1 + ‖z‖) := by linarith
  have h1R_α : (1 + R) ^ α ≤ (3 * (1 + ‖z‖)) ^ α :=
    rpow_le_rpow (by positivity) h1R hα_pos.le
  have h3α : (3 * (1 + ‖z‖)) ^ α = 3 ^ α * (1 + ‖z‖) ^ α :=
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (by linarith)
  -- (1 + ‖z‖)^α ≥ 1
  have h1α : 1 ≤ (1 + ‖z‖) ^ α := by
    calc (1 : ℝ) = 1 ^ α := (one_rpow α).symm
      _ ≤ (1 + ‖z‖) ^ α := rpow_le_rpow (by norm_num) (by linarith) hα_pos.le
  -- Bound: 2*M*‖z‖/(R-‖z‖) ≤ 2*M (since ‖z‖/(R-‖z‖) ≤ 1)
  have t1 : 2 * M * ‖z‖ / (R - ‖z‖) ≤ 2 * M := by
    rw [div_le_iff₀ hR_sub]; nlinarith [rpow_nonneg (by positivity : (0:ℝ) ≤ 1 + R) α]
  have t2 : ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖) ≤ 3 * ‖g 0‖ := by
    rw [div_le_iff₀ hR_sub]; nlinarith [norm_nonneg (g 0)]
  -- M ≤ A * 3^α * (1+‖z‖)^α
  have hM_bound : M ≤ A * 3 ^ α * (1 + ‖z‖) ^ α := by
    show A * (1 + R) ^ α ≤ A * 3 ^ α * (1 + ‖z‖) ^ α
    calc A * (1 + R) ^ α ≤ A * (3 ^ α * (1 + ‖z‖) ^ α) := by
          gcongr; linarith [h3α ▸ h1R_α]
      _ = A * 3 ^ α * (1 + ‖z‖) ^ α := by ring
  calc ‖g z‖
      ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖) := h_bc
    _ ≤ 2 * M + 3 * ‖g 0‖ := by linarith
    _ ≤ 2 * (A * 3 ^ α * (1 + ‖z‖) ^ α) + 3 * ‖g 0‖ := by nlinarith
    _ = (2 * A * 3 ^ α) * (1 + ‖z‖) ^ α + 3 * ‖g 0‖ := by ring
    _ ≤ (2 * A * 3 ^ α) * (1 + ‖z‖) ^ α + 3 * ‖g 0‖ * (1 + ‖z‖) ^ α := by
        nlinarith [le_mul_of_one_le_right (by positivity : (0:ℝ) ≤ 3 * ‖g 0‖) h1α]
    _ = C₀ * (1 + ‖z‖) ^ α := by ring
    _ ≤ max C₀ 1 * (1 + ‖z‖) ^ α := by
        nlinarith [le_max_left C₀ 1, rpow_nonneg (by linarith : (0:ℝ) ≤ 1 + ‖z‖) α]

end ArithmeticHodge.Analysis.EntireFunction
