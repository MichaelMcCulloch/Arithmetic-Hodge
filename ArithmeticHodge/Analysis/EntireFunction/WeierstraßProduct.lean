/-
  Step 1.1: Weierstraß Elementary Factors and Infinite Products

  Define the Weierstraß elementary factor E_p(z) and prove:
  - E_p(0) = 1
  - |1 - E_p(z)| ≤ |z|^{p+1} for |z| ≤ 1/2
  - Convergence of ∏_n E_{p_n}(z/a_n) under exponent of convergence conditions
  - The product defines an entire function with zeros exactly at {a_n}

  Infrastructure built on Mathlib's HasProd/tprod API and Complex.exp.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Complex Filter Topology Finset BigOperators

namespace ArithmeticHodge.Analysis.EntireFunction

-- ============================================================
-- Weierstraß Elementary Factors
-- ============================================================

/-- The Weierstraß elementary factor of genus p:
    E_p(z) = (1 - z) · exp(z + z²/2 + ⋯ + zᵖ/p)

    For p = 0: E₀(z) = 1 - z
    For p ≥ 1: E_p(z) = (1 - z) · exp(Σ_{k=1}^{p} zᵏ/k)

    This is the canonical building block for Weierstraß products.
    Each E_p has a simple zero at z = 1 and grows like exp(O(|z|^p)). -/
noncomputable def weierstraßElementary (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (↑(k + 1) : ℂ))

/-- E_p(0) = 1 for all p. -/
theorem weierstraßElementary_zero (p : ℕ) :
    weierstraßElementary p 0 = 1 := by
  simp [weierstraßElementary]

/-- E₀(z) = 1 - z (the simplest elementary factor). -/
theorem weierstraßElementary_genus_zero (z : ℂ) :
    weierstraßElementary 0 z = 1 - z := by
  simp [weierstraßElementary]

/-- The exponential sum in E_p: Σ_{k=1}^{p} zᵏ/k.
    This is the truncated Taylor series of -log(1-z). -/
noncomputable def weierstraßExpSum (p : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range p, z ^ (k + 1) / (↑(k + 1) : ℂ)

/-- The exponential sum at 0 is 0. -/
theorem weierstraßExpSum_zero (p : ℕ) : weierstraßExpSum p 0 = 0 := by
  simp [weierstraßExpSum]

/-- Rewrite E_p in terms of the exponential sum. -/
theorem weierstraßElementary_eq (p : ℕ) (z : ℂ) :
    weierstraßElementary p z = (1 - z) * Complex.exp (weierstraßExpSum p z) := by
  rfl

-- ============================================================
-- Derivative of weierstraßElementary
-- ============================================================

/-- The derivative of w^{n+1}/(n+1) is w^n. -/
private theorem hasDerivAt_pow_div (n : ℕ) (w : ℂ) :
    HasDerivAt (fun w => w ^ (n + 1) / (↑(n + 1) : ℂ)) (w ^ n) w := by
  have hne : (↑(n + 1) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd := (hasDerivAt_pow (n + 1) w).div_const (↑(n + 1) : ℂ)
  simp only [Nat.add_sub_cancel] at hd
  refine hd.congr_deriv ?_
  field_simp

/-- The derivative of S_p(w) = Σ_{k=1}^p w^k/k is Σ_{k=0}^{p-1} w^k. -/
private theorem hasDerivAt_weierstraßExpSum (p : ℕ) (w : ℂ) :
    HasDerivAt (weierstraßExpSum p) (∑ k ∈ Finset.range p, w ^ k) w := by
  unfold weierstraßExpSum
  induction p with
  | zero => simp; exact hasDerivAt_const w 0
  | succ n ih =>
    simp_rw [Finset.sum_range_succ]
    exact ih.add (hasDerivAt_pow_div n w)

/-- Geometric sum identity: (1 - w) · Σ_{k=0}^{p-1} w^k = 1 - w^p. -/
private theorem geom_sum_mul (p : ℕ) (w : ℂ) :
    (1 - w) * ∑ k ∈ Finset.range p, w ^ k = 1 - w ^ p := by
  induction p with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

/-- The derivative of E_p(w) = (1-w)·exp(S_p(w)) is -w^p · exp(S_p(w)).

    This follows from the product rule and the identity
    (1-w)·S_p'(w) = (1-w)·Σ_{k=0}^{p-1} w^k = 1-w^p. -/
private theorem hasDerivAt_weierstraßElementary_aux (p : ℕ) (w : ℂ) :
    HasDerivAt (weierstraßElementary p)
      (-(w ^ p) * Complex.exp (weierstraßExpSum p w)) w := by
  -- E_p(w) = (1-w) · exp(S_p(w))
  -- E_p'(w) = -exp(S_p(w)) + (1-w)·exp(S_p(w))·S_p'(w)
  --         = exp(S_p(w)) · (-1 + (1-w)·S_p'(w))
  --         = exp(S_p(w)) · (-1 + 1 - w^p)      [by geom_sum_mul]
  --         = -w^p · exp(S_p(w))
  show HasDerivAt (fun w => (1 - w) * Complex.exp (weierstraßExpSum p w))
    (-(w ^ p) * Complex.exp (weierstraßExpSum p w)) w
  have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) w :=
    (hasDerivAt_id w).const_sub 1 |>.congr_deriv (by ring)
  have hexp := (hasDerivAt_weierstraßExpSum p w).cexp
  refine (h1.mul hexp).congr_deriv ?_
  -- Goal: -w^p · exp(S) = -1 · exp(S) + (1-w) · (exp(S) · Σ w^k)
  have hgeo := geom_sum_mul p w
  -- Rewrite (1-w) · Σ w^k = 1 - w^p
  linear_combination Complex.exp (weierstraßExpSum p w) * hgeo

-- ============================================================
-- Key Bound: |1 - E_p(z)| ≤ |z|^{p+1} for |z| ≤ 1/2
-- ============================================================

/-- **Weierstraß elementary factor bound.**

    For |z| ≤ 1/2, we have |1 - E_p(z)| ≤ |z|^{p+1}.

    The proof parameterizes `t ↦ E_p(tz)` on `[0,1]` and computes
    `E_p'(w) = -w^p · exp(S_p(w))`. The mean value inequality
    gives `‖1 - E_p(z)‖ ≤ sup_{t∈[0,1]} ‖f'(t)‖`, where
    `‖f'(t)‖ = t^p · ‖z‖^{p+1} · |exp(S_p(tz))| ≤ ‖z‖^{p+1} · eᵗ`.

    For the exact bound, the integral form gives
    `‖1 - E_p(z)‖ ≤ ‖z‖^{p+1} · ∫₀¹ tᵖ·eᵗ dt ≤ ‖z‖^{p+1} · ∫₀¹ t·eᵗ dt = ‖z‖^{p+1}`,
    using `tᵖ⁺¹ ≤ t` for `t ∈ [0,1]` and `∫₀¹ t·eᵗ dt = 1` (IBP). -/
theorem weierstraßElementary_bound (p : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    ‖1 - weierstraßElementary p z‖ ≤ ‖z‖ ^ (p + 1) := by
  induction p with
  | zero =>
    simp [weierstraßElementary]
  | succ p _ih =>
    -- Use the MVT on f(t) = E_{p+1}(tz) for t ∈ [0,1].
    -- f(0) = 1, f(1) = E_{p+1}(z), so ‖1 - E_{p+1}(z)‖ = ‖f(0) - f(1)‖ ≤ sup ‖f'‖.
    --
    -- By the chain rule and hasDerivAt_weierstraßElementary_aux:
    --   f'(t) = -(tz)^{p+1} · z · exp(S_{p+1}(tz))
    --   ‖f'(t)‖ = t^{p+1} · ‖z‖^{p+2} · |exp(S_{p+1}(tz))|
    --
    -- Since S_{p+1}(tz) = Σ_{k=1}^{p+1} (tz)^k/k, for ‖z‖ ≤ 1/2 and t ∈ [0,1]:
    --   ‖S_{p+1}(tz)‖ ≤ t‖z‖/(1-t‖z‖) ≤ t
    --   |exp(S_{p+1}(tz))| ≤ eᵗ
    --
    -- So ‖f'(t)‖ ≤ t^{p+1}·‖z‖^{p+2}·eᵗ ≤ ‖z‖^{p+2}·e   [sup at t=1]
    --
    -- The MVT gives ‖1 - E_{p+1}(z)‖ ≤ e·‖z‖^{p+2}.
    --
    -- For the EXACT bound ‖z‖^{p+2}, one needs the integral form:
    --   ‖1 - E_{p+1}(z)‖ ≤ ∫₀¹ t^{p+1}·‖z‖^{p+2}·eᵗ dt
    --                     ≤ ‖z‖^{p+2}·∫₀¹ t·eᵗ dt = ‖z‖^{p+2}
    -- using t^{p+1} ≤ t for t ∈ [0,1] and ∫₀¹ t·eᵗ dt = 1.
    -- The proof uses the FTC along the path t ↦ E_{p+1}(tz).
    -- Define the path function and establish its derivative.
    set q := p.succ with hq
    set f : ℝ → ℂ := fun t => weierstraßElementary q ((↑t : ℂ) * z) with hf_def
    -- f(0) = 1, f(1) = E_q(z)
    have hf0 : f 0 = 1 := by simp [hf_def, weierstraßElementary_zero]
    have hf1 : f 1 = weierstraßElementary q z := by simp [hf_def]
    -- The derivative: f'(t) = z · E_q'(tz) = -(tz)^q · z · exp(S_q(tz))
    -- We need this for the MVT on [0,1].
    -- DifferentiableOn follows from weierstraßElementary_differentiable.
    -- HasDerivAt for the path function f(t) = E_q(tz)
    have hf_hasDerivAt : ∀ t : ℝ, HasDerivAt f
        (-((↑t : ℂ) * z) ^ q * Complex.exp (weierstraßExpSum q ((↑t : ℂ) * z)) * z) t := by
      intro t
      have hE := hasDerivAt_weierstraßElementary_aux q ((↑t : ℂ) * z)
      -- The inner function t ↦ ↑t * z has derivative z
      have hg : HasDerivAt (fun t : ℝ => (↑t : ℂ) * z) z t := by
        have := (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z
        simp at this; exact this
      -- Chain rule: f'(t) = E_q'(tz) · z
      -- HasDerivAt.comp : outer.comp inner gives derivative outer' * inner'
      have hcomp := hE.comp t hg
      change HasDerivAt (fun t => weierstraßElementary q (↑t * z)) _ t at hcomp

      exact hcomp
    have hf_diff : DifferentiableOn ℝ f (Set.Icc 0 1) :=
      fun t _ => (hf_hasDerivAt t).differentiableAt.differentiableWithinAt
    -- The derivative f'(t) = -(tz)^q · exp(S_q(tz)) · z
    -- has norm t^q · ‖z‖^{q+1} · ‖exp(S_q(tz))‖.
    -- We bound ‖exp(S_q(tz))‖ ≤ exp(‖S_q(tz)‖) ≤ exp(t)
    -- using ‖S_q(tz)‖ ≤ t‖z‖/(1-t‖z‖) ≤ t for ‖z‖ ≤ 1/2.
    -- Then ‖f'(t)‖ ≤ t^q · ‖z‖^{q+1} · eᵗ ≤ ‖z‖^{q+1} · e.
    -- MVT on [0,1]: ‖f(1) - f(0)‖ ≤ e · ‖z‖^{q+1}.
    -- Since q = p+1 ≥ 1 and ‖z‖ ≤ 1/2: e · ‖z‖^{q+1} ≤ e · ‖z‖^{p+2}.
    --
    -- For the EXACT bound ≤ ‖z‖^{p+2}, one needs the integral form:
    --   ‖1 - E_q(z)‖ ≤ ‖z‖^{q+1} · ∫₀¹ tq · eᵗ dt ≤ ‖z‖^{q+1}
    -- since tq ≤ t for t ∈ [0,1] (q ≥ 1) and ∫₀¹ t·eᵗ dt = 1.
    -- This integral bound is established via FTC and integration by parts.
    -- Use FTC: f(1) - f(0) = ∫₀¹ f'(t) dt
    set f' : ℝ → ℂ := fun t =>
      -((↑t : ℂ) * z) ^ q * Complex.exp (weierstraßExpSum q ((↑t : ℂ) * z)) * z with hf'_def
    -- FTC: ∫₀¹ f'(t) dt = f(1) - f(0) = E_q(z) - 1
    have hf'_cont : Continuous f' := by
      simp only [hf'_def]
      -- f'(t) = -(↑t * z)^q * exp(S_q(↑t * z)) * z
      -- This is continuous as a composition of continuous functions.
      have htz : Continuous (fun t : ℝ => (↑t : ℂ) * z) :=
        continuous_ofReal.mul continuous_const
      have hpow : Continuous (fun t : ℝ => ((↑t : ℂ) * z) ^ q) := htz.pow q
      have hsum : Continuous (fun t : ℝ => weierstraßExpSum q ((↑t : ℂ) * z)) := by
        unfold weierstraßExpSum
        apply continuous_finset_sum
        intro k _
        exact (htz.pow (k + 1)).div_const _
      have hexp : Continuous (fun t : ℝ => Complex.exp (weierstraßExpSum q ((↑t : ℂ) * z))) :=
        Complex.continuous_exp.comp hsum
      exact ((hpow.neg.mul hexp).mul continuous_const)
    have hFTC : ∫ t in (0 : ℝ)..1, f' t = f 1 - f 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t _ht
        exact hf_hasDerivAt t
      · exact hf'_cont.intervalIntegrable 0 1
    -- So 1 - E_q(z) = -(∫₀¹ f'(t) dt) = ∫₀¹ -f'(t) dt = ∫₀¹ (tz)^q · exp(S) · z dt
    -- ‖1 - E_q(z)‖ = ‖f(0) - f(1)‖ = ‖∫₀¹ f'(t) dt‖
    have h_eq : 1 - weierstraßElementary q z = -(f 1 - f 0) := by
      rw [hf0, hf1]; ring
    rw [h_eq, norm_neg, ← hFTC]
    -- ‖∫₀¹ f'(t) dt‖ ≤ ∫₀¹ ‖f'(t)‖ dt ≤ ‖z‖^{q+1} · ∫₀¹ t^q · exp(t) dt
    calc ‖∫ t in (0 : ℝ)..1, f' t‖
        ≤ ∫ t in (0 : ℝ)..1, ‖f' t‖ := by
          exact intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)
      _ ≤ ∫ t in (0 : ℝ)..1, (t : ℝ) ^ q * ‖z‖ ^ (q + 1) * Real.exp t := by
          -- Bound ‖f'(t)‖ ≤ t^q · ‖z‖^{q+1} · exp(t)
          apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
          · exact (hf'_cont.norm).intervalIntegrable 0 1
          · apply Continuous.intervalIntegrable
            exact ((continuous_pow q).mul continuous_const).mul (Real.continuous_exp)
            -- continuous t^q · ‖z‖^{q+1} · exp(t)
          · intro t ht
            simp only [Set.mem_Icc] at ht
            simp only [hf'_def]
            -- ‖-(tz)^q · exp(S) · z‖ ≤ t^q · ‖z‖^{q+1} · exp(t)
            -- ‖-(tz)^q · exp(S) · z‖ ≤ t^q · ‖z‖^{q+1} · exp(t)
            have ht0 := ht.1  -- 0 ≤ t
            -- Bound ‖exp(S_q(tz))‖ ≤ exp(t) using ‖S_q(tz)‖ ≤ t
            -- ‖-(tz)^q · exp(S) · z‖ ≤ t^q · ‖z‖^{q+1} · exp(t)
            have ht0 := ht.1  -- 0 ≤ t
            -- Bound ‖exp(w)‖ ≤ exp(‖w‖) ≤ exp(t) where ‖S_q(tz)‖ ≤ t
            -- Sub-lemma: ‖S_q(tz)‖ ≤ t
            have h_norm_S : ‖weierstraßExpSum q ((↑t : ℂ) * z)‖ ≤ t := by
              unfold weierstraßExpSum
              have htz : t * ‖z‖ ≤ 1 / 2 := by nlinarith
              calc ‖∑ k ∈ Finset.range q, ((↑t : ℂ) * z) ^ (k + 1) / (↑(k + 1) : ℂ)‖
                  ≤ ∑ k ∈ Finset.range q, ‖((↑t : ℂ) * z) ^ (k + 1) / (↑(k + 1) : ℂ)‖ :=
                    norm_sum_le _ _
                _ ≤ ∑ k ∈ Finset.range q, (t * ‖z‖) ^ (k + 1) := by
                    gcongr with k _hk
                    rw [norm_div, norm_pow, norm_mul]
                    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
                    apply div_le_self (pow_nonneg (mul_nonneg ht0 (norm_nonneg z)) _)
                    simp only [norm_natCast]
                    exact_mod_cast Nat.succ_pos k
                _ ≤ t := by
                    -- Each (t‖z‖)^{k+1} ≤ (t‖z‖) · (1/2)^k since t‖z‖ ≤ 1/2
                    -- So Σ (t‖z‖)^{k+1} ≤ t‖z‖ · Σ (1/2)^k ≤ t‖z‖ · 2 = 2t‖z‖ ≤ t
                    set r := t * ‖z‖ with hr_def
                    have hr0 : 0 ≤ r := mul_nonneg ht0 (norm_nonneg z)
                    have hr1 : r ≤ 1 / 2 := by nlinarith
                    -- r^{k+1} = r · r^k ≤ r · (1/2)^k
                    have hterm : ∀ k, r ^ (k + 1) ≤ r * (1 / 2) ^ k := by
                      intro k
                      have heq : r ^ (k + 1) = r * r ^ k := by ring
                      rw [heq]; gcongr
                    calc ∑ k ∈ Finset.range q, r ^ (k + 1)
                        ≤ ∑ k ∈ Finset.range q, r * (1 / 2) ^ k := Finset.sum_le_sum (fun k _ => hterm k)
                      _ = r * ∑ k ∈ Finset.range q, (1 / 2) ^ k := by rw [← Finset.mul_sum]
                      _ ≤ r * 2 := by
                          gcongr
                          -- Σ_{k<q} (1/2)^k ≤ 2
                          have hsumm : Summable (fun k => (1 / 2 : ℝ) ^ k) :=
                            summable_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)
                          calc (∑ k ∈ Finset.range q, (1 / 2 : ℝ) ^ k : ℝ)
                              ≤ ∑' k, (1 / 2 : ℝ) ^ k :=
                                hsumm.sum_le_tsum _ (fun _ _ => by positivity)
                            _ = 2 := by
                                rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)]
                                norm_num
                      _ = 2 * r := by ring
                      _ = 2 * (t * ‖z‖) := by rw [hr_def]
                      _ ≤ 2 * (t * (1 / 2)) := by gcongr
                      _ = t := by ring
            -- Sub-lemma: ‖exp(w)‖ ≤ exp(‖w‖) for any w : ℂ
            have h_exp_norm : ‖Complex.exp (weierstraßExpSum q ((↑t : ℂ) * z))‖
                ≤ Real.exp ‖weierstraßExpSum q ((↑t : ℂ) * z)‖ := by
              -- ‖exp(w)‖ = exp(w.re) ≤ exp(|w.re|) ≤ exp(‖w‖)
              set w := weierstraßExpSum q ((↑t : ℂ) * z)
              have : ‖Complex.exp w‖ = Real.exp w.re := by
                simp [Complex.norm_exp]
              rw [this]
              exact Real.exp_le_exp_of_le ((le_abs_self w.re).trans (Complex.abs_re_le_norm w))
            have h_norm_exp : ‖Complex.exp (weierstraßExpSum q ((↑t : ℂ) * z))‖ ≤ Real.exp t :=
              h_exp_norm.trans (Real.exp_le_exp_of_le h_norm_S)
            -- Assemble the norm bound
            calc ‖-((↑t : ℂ) * z) ^ q * Complex.exp (weierstraßExpSum q ((↑t : ℂ) * z)) * z‖
                = ‖((↑t : ℂ) * z) ^ q‖ * ‖Complex.exp (weierstraßExpSum q ((↑t : ℂ) * z))‖ * ‖z‖ := by
                  rw [norm_mul, norm_mul, norm_neg]
              _ = (t * ‖z‖) ^ q * ‖Complex.exp (weierstraßExpSum q ((↑t : ℂ) * z))‖ * ‖z‖ := by
                  congr 2; rw [norm_pow, norm_mul]; simp [abs_of_nonneg ht0]
              _ ≤ (t * ‖z‖) ^ q * Real.exp t * ‖z‖ := by gcongr
              _ = t ^ q * ‖z‖ ^ (q + 1) * Real.exp t := by rw [mul_pow]; ring
      _ = ‖z‖ ^ (q + 1) * ∫ t in (0 : ℝ)..1, t ^ q * Real.exp t := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1; ext t; ring
      _ ≤ ‖z‖ ^ (q + 1) * 1 := by
          gcongr
          -- Need: ∫₀¹ t^q · exp(t) dt ≤ 1
          -- Since q ≥ 1: t^q ≤ t on [0,1], so ∫ t^q · exp(t) ≤ ∫ t · exp(t)
          -- And ∫₀¹ t · exp(t) dt = 1 (by FTC with antiderivative (t-1)·exp(t))
          calc ∫ t in (0 : ℝ)..1, t ^ q * Real.exp t
              ≤ ∫ t in (0 : ℝ)..1, t * Real.exp t := by
                apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
                · exact (((continuous_pow q).mul Real.continuous_exp).intervalIntegrable 0 1)
                · exact ((continuous_id.mul Real.continuous_exp).intervalIntegrable 0 1)
                · intro t ht
                  simp only [Set.mem_Icc] at ht
                  gcongr
                  -- t^q ≤ t for t ∈ [0,1] when q ≥ 1
                  calc t ^ q = t ^ (p + 1) := by rfl
                    _ = t * t ^ p := by ring
                    _ ≤ t * 1 := by
                        apply mul_le_mul_of_nonneg_left _ ht.1
                        exact pow_le_one₀ ht.1 ht.2
                    _ = t := by ring
            _ = 1 := by
                -- ∫₀¹ t · exp(t) dt = 1
                -- Antiderivative F(t) = (t-1) · exp(t), F'(t) = exp(t) + (t-1)·exp(t) = t·exp(t)
                -- F(1) - F(0) = 0 · e - (-1) · 1 = 1
                have hF : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
                    HasDerivAt (fun t => (t - 1) * Real.exp t) (t * Real.exp t) t := by
                  intro t _
                  have h1 := (hasDerivAt_id t).sub (hasDerivAt_const t 1)
                  have h2 := Real.hasDerivAt_exp t
                  have hmul := h1.mul h2
                  -- hmul gives derivative (id t - 1)' * exp t + (id t - 1) * (exp t)'
                  -- = 1 * exp t + (t - 1) * exp t = t * exp t
                  refine hmul.congr_deriv ?_
                  simp only [Pi.sub_apply, id, sub_zero]; ring
                rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
                    ((continuous_id.mul Real.continuous_exp).intervalIntegrable 0 1)]
                -- F(1) - F(0) = (1-1)·exp(1) - (0-1)·exp(0) = 0 - (-1) = 1
                norm_num [Real.exp_zero]
      _ = ‖z‖ ^ (q + 1) := by ring

/-- The elementary factor E_p(z) ≠ 0 when z ≠ 1.
    Since E_p(z) = (1-z) · exp(polynomial), the only zero is at z = 1. -/
theorem weierstraßElementary_ne_zero (p : ℕ) (z : ℂ) (hz : z ≠ 1) :
    weierstraßElementary p z ≠ 0 := by
  unfold weierstraßElementary
  apply mul_ne_zero
  · exact sub_ne_zero.mpr (Ne.symm hz)
  · exact Complex.exp_ne_zero _

/-- E_p is differentiable (and hence analytic) everywhere. -/
theorem weierstraßElementary_differentiable (p : ℕ) :
    Differentiable ℂ (weierstraßElementary p) := by
  unfold weierstraßElementary
  apply Differentiable.mul
  · exact differentiable_const 1 |>.sub differentiable_id
  · have hsum : Differentiable ℂ (weierstraßExpSum p) := by
      unfold weierstraßExpSum
      induction p with
      | zero => simp
      | succ n ih =>
        simp_rw [Finset.sum_range_succ]
        exact ih.add ((differentiable_id.pow (n + 1)).div_const _)
    exact Complex.differentiable_exp.comp hsum

-- ============================================================
-- Weierstraß Infinite Product
-- ============================================================

/-- A sequence of nonzero complex numbers with no finite accumulation point.
    This is the data needed to construct a Weierstraß product.
    The condition |a_n| → ∞ ensures the zeros are isolated. -/
structure ZeroSequence where
  /-- The sequence of (nonzero) zero locations -/
  zeros : ℕ → ℂ
  /-- All entries are nonzero -/
  ne_zero : ∀ n, zeros n ≠ 0
  /-- The norms tend to infinity -/
  tendsto_norm : Filter.Tendsto (fun n => ‖zeros n‖) Filter.atTop Filter.atTop

/-- The exponent of convergence of a zero sequence:
    inf { σ ≥ 0 : Σ |a_n|^{-σ} < ∞ }

    This controls which genus p is needed for convergence. -/
noncomputable def exponentOfConvergence (a : ZeroSequence) : ℝ :=
  sInf { σ : ℝ | 0 ≤ σ ∧ Summable (fun n => ‖a.zeros n‖⁻¹ ^ σ) }

/-- The Weierstraß canonical product with uniform genus p:
    P(z) = ∏_n E_p(z / a_n)

    This defines an entire function with simple zeros at each a_n
    (assuming the a_n are distinct). -/
noncomputable def weierstraßProduct (a : ZeroSequence) (p : ℕ) (z : ℂ) : ℂ :=
  ∏' n, weierstraßElementary p (z / a.zeros n)

/-- Auxiliary: convert rpow summability to pow summability. -/
private theorem rpow_to_pow_summable (a : ZeroSequence) (p : ℕ)
    (hconv : Summable (fun n => (‖a.zeros n‖⁻¹) ^ (p + 1 : ℝ))) :
    Summable (fun n => (‖a.zeros n‖⁻¹) ^ (p + 1)) := by
  have : (fun n => (‖a.zeros n‖⁻¹) ^ (p + 1 : ℝ)) = (fun n => (‖a.zeros n‖⁻¹) ^ (p + 1)) := by
    ext n; rw [← Real.rpow_natCast]; norm_cast
  rwa [this] at hconv

/-- The norm bound on the perturbation E_p(z/a_n) - 1 is eventually dominated
    by a summable sequence. This is used for both convergence and zero analysis. -/
private theorem perturbation_norm_bound (a : ZeroSequence) (p : ℕ) (z : ℂ) :
    ∀ᶠ n in Filter.atTop,
      ‖weierstraßElementary p (z / a.zeros n) - 1‖ ≤
        ‖z‖ ^ (p + 1) * (‖a.zeros n‖⁻¹) ^ (p + 1) := by
  apply (a.tendsto_norm.eventually_ge_atTop (2 * ‖z‖ + 1)).mono
  intro n hn
  have ha_pos : (0 : ℝ) < ‖a.zeros n‖ := by linarith [norm_nonneg z]
  have hznorm : ‖z / a.zeros n‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_div_iff₀ ha_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hbound := weierstraßElementary_bound p (z / a.zeros n) hznorm
  rw [norm_sub_rev] at hbound
  calc ‖weierstraßElementary p (z / a.zeros n) - 1‖
      ≤ ‖z / a.zeros n‖ ^ (p + 1) := hbound
    _ = ‖z‖ ^ (p + 1) * ‖a.zeros n‖⁻¹ ^ (p + 1) := by
        rw [norm_div, div_eq_mul_inv, mul_pow]

/-- The perturbation E_p(z/a_n) - 1 is summable in norm. -/
private theorem perturbation_summable_norm (a : ZeroSequence) (p : ℕ)
    (hconv : Summable (fun n => (‖a.zeros n‖⁻¹) ^ (p + 1 : ℝ))) (z : ℂ) :
    Summable fun n => ‖weierstraßElementary p (z / a.zeros n) - 1‖ := by
  apply ((rpow_to_pow_summable a p hconv).mul_left (‖z‖ ^ (p + 1))).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  exact (perturbation_norm_bound a p z).mono fun n hn => by
    simp only [Real.norm_eq_abs, abs_norm]; exact hn

/-- **Convergence of the Weierstraß product.**

    If Σ_n |a_n|^{-(p+1)} < ∞, then for any R > 0, the product
    ∏_n E_p(z/a_n) converges absolutely and uniformly on |z| ≤ R.

    The proof uses the elementary factor bound: for |z| ≤ R and n large enough
    that |a_n| > 2R, we have |z/a_n| ≤ 1/2, so
    |1 - E_p(z/a_n)| ≤ |z/a_n|^{p+1} ≤ (R/|a_n|)^{p+1}.
    The summability of Σ (R/|a_n|)^{p+1} follows from Σ |a_n|^{-(p+1)} < ∞. -/
theorem weierstraßProduct_convergent (a : ZeroSequence) (p : ℕ)
    (hconv : Summable (fun n => (‖a.zeros n‖⁻¹) ^ (p + 1 : ℝ))) :
    ∀ z : ℂ, Multipliable (fun n => weierstraßElementary p (z / a.zeros n)) := by
  intro z
  have key : (fun n => weierstraßElementary p (z / a.zeros n)) =
      (fun n => 1 + (weierstraßElementary p (z / a.zeros n) - 1)) := by
    ext n; ring
  rw [key]
  apply Complex.multipliable_one_add_of_summable
  apply ((rpow_to_pow_summable a p hconv).mul_left (‖z‖ ^ (p + 1))).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  exact perturbation_norm_bound a p z

/-- **The Weierstraß product is entire.**

    Under the convergence condition Σ |a_n|^{-(p+1)} < ∞,
    z ↦ ∏_n E_p(z/a_n) is an entire function (analytic everywhere). -/
theorem weierstraßProduct_differentiable (a : ZeroSequence) (p : ℕ)
    (hconv : Summable (fun n => (‖a.zeros n‖⁻¹) ^ (p + 1 : ℝ))) :
    Differentiable ℂ (weierstraßProduct a p) := by
  sorry -- SCAFFOLD: differentiability of uniformly convergent product of analytic functions

/-- **The zeros of the Weierstraß product are exactly {a_n}.**

    P(z) = 0 iff z = a_n for some n (assuming distinct a_n). -/
theorem weierstraßProduct_zero_iff (a : ZeroSequence) (p : ℕ)
    (hconv : Summable (fun n => (‖a.zeros n‖⁻¹) ^ (p + 1 : ℝ)))
    (hdistinct : Function.Injective a.zeros) (z : ℂ) :
    weierstraßProduct a p z = 0 ↔ ∃ n, z = a.zeros n := by
  unfold weierstraßProduct
  constructor
  · -- If product = 0, some factor must be zero
    intro hprod
    by_contra h
    push_neg at h
    have hne : ∀ n, z / a.zeros n ≠ 1 :=
      fun n heq => h n (div_eq_one_iff_eq (a.ne_zero n) |>.mp heq)
    -- Rewrite product as ∏' n, (1 + perturbation)
    have hrewrite : (fun n => weierstraßElementary p (z / a.zeros n)) =
        (fun n => 1 + (weierstraßElementary p (z / a.zeros n) - 1)) := by
      ext n; ring
    rw [hrewrite] at hprod
    -- Product of nonzero factors with summable perturbation is nonzero
    exact tprod_one_add_ne_zero_of_summable
      (fun n => by simp [weierstraßElementary_ne_zero p _ (hne n)])
      (perturbation_summable_norm a p hconv z) hprod
  · -- If z = a_n, then E_p(a_n/a_n) = E_p(1) = 0, so the product is 0
    rintro ⟨n, rfl⟩
    apply tprod_of_exists_eq_zero
    exact ⟨n, by simp [weierstraßElementary, div_self (a.ne_zero n)]⟩

-- ============================================================
-- Weierstraß Factorization Theorem (existence form)
-- ============================================================

/-- **Weierstraß Factorization Theorem.**

    Every entire function f can be written as
      f(z) = z^m · e^{g(z)} · ∏_n E_{p_n}(z/a_n)
    where:
    - m is the order of vanishing at 0
    - g is entire
    - {a_n} are the nonzero zeros of f
    - p_n are chosen to ensure convergence

    This is the foundational factorization; Hadamard's theorem adds the
    constraint that g is a polynomial when f has finite order.

    We state a version with uniform genus p. -/
theorem weierstraß_factorization (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) :
    ∃ (m : ℕ) (g : ℂ → ℂ) (a : ℕ → ℂ) (p : ℕ),
      Differentiable ℂ g ∧
      (∀ n, a n ≠ 0 → f (a n) = 0) ∧
      ∀ z, f z = z ^ m * Complex.exp (g z) *
        ∏' n, weierstraßElementary p (z / a n) := by
  sorry -- SCAFFOLD: Full Weierstraß factorization

end ArithmeticHodge.Analysis.EntireFunction
