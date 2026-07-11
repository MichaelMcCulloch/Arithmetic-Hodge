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
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.DiscreteSubset
import Mathlib.Data.Set.Countable
import Mathlib.Topology.Compactness.Lindelof
import ArithmeticHodge.Analysis.EntireFunction.Defs
import ArithmeticHodge.Analysis.EntireFunction.ZeroSummability

open Complex Filter Topology Finset BigOperators Metric

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
  have hpow : Summable (fun n => (‖a.zeros n‖⁻¹) ^ (p + 1)) :=
    rpow_to_pow_summable a p hconv
  intro z₀
  set R := ‖z₀‖ + 1
  have hR : 0 < R := by positivity
  have hz₀_ball : z₀ ∈ ball (0 : ℂ) R := by
    simp only [mem_ball_zero_iff]; linarith
  -- Suffices: differentiable on a ball containing z₀
  suffices h : DifferentiableOn ℂ (weierstraßProduct a p) (ball 0 R) from
    h.differentiableAt (isOpen_ball.mem_nhds hz₀_ball)
  -- Write each factor as 1 + perturbation
  set f : ℕ → ℂ → ℂ := fun n z => weierstraßElementary p (z / a.zeros n) - 1
  have hprod_eq : weierstraßProduct a p = fun z => ∏' n, (1 + f n z) := by
    ext z; simp only [weierstraßProduct, f]; congr 1; ext n; ring
  rw [hprod_eq]
  -- Establish locally uniform convergence
  have hloc : HasProdLocallyUniformlyOn (fun n z => 1 + f n z)
      (fun z => ∏' n, (1 + f n z)) (ball (0 : ℂ) R) := by
    apply Summable.hasProdLocallyUniformlyOn_nat_one_add isOpen_ball
      (show Summable (fun n => R ^ (p + 1) * (‖a.zeros n‖⁻¹) ^ (p + 1)) from hpow.mul_left _)
    · -- Uniform bound on ball 0 R
      apply (a.tendsto_norm.eventually_ge_atTop (2 * R)).mono
      intro n hn x hx
      simp only [f]
      have ha_pos : (0 : ℝ) < ‖a.zeros n‖ := by linarith [hR]
      have hxR : ‖x‖ < R := mem_ball_zero_iff.mp hx
      have hxnorm : ‖x / a.zeros n‖ ≤ 1 / 2 := by
        rw [norm_div, div_le_div_iff₀ ha_pos two_pos]; linarith
      have hbound := weierstraßElementary_bound p (x / a.zeros n) hxnorm
      rw [norm_sub_rev] at hbound
      calc ‖weierstraßElementary p (x / a.zeros n) - 1‖
          ≤ ‖x / a.zeros n‖ ^ (p + 1) := hbound
        _ = (‖x‖ / ‖a.zeros n‖) ^ (p + 1) := by rw [norm_div]
        _ ≤ (R / ‖a.zeros n‖) ^ (p + 1) :=
            pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (norm_nonneg _))
              ((div_le_div_iff_of_pos_right ha_pos).mpr (le_of_lt hxR)) _
        _ = R ^ (p + 1) * (‖a.zeros n‖⁻¹) ^ (p + 1) := by
            rw [div_eq_mul_inv, mul_pow]
    · -- Continuity of each perturbation
      intro n
      exact (((weierstraßElementary_differentiable p).comp
        (differentiable_id.div_const _)).sub (differentiable_const 1)).continuous.continuousOn
  -- Finite products are differentiable, so the locally uniform limit is differentiable
  exact (hloc : TendstoLocallyUniformlyOn _ _ _ _).differentiableOn
    (Eventually.of_forall fun s =>
      DifferentiableOn.fun_finset_prod fun i _ =>
        (differentiableOn_const 1).add
          (((weierstraßElementary_differentiable p).comp
            (differentiable_id.div_const _)).differentiableOn.sub (differentiableOn_const 1)))
    isOpen_ball

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
-- Raw sequence API (without ZeroSequence structure)
-- ============================================================

/-- Perturbation norm summability for raw zero sequences.
    This extends the private `perturbation_summable_norm` from
    `ZeroSequence` to arbitrary `ℕ → ℂ`, deriving the eventually-large
    condition from summability rather than `tendsto_norm`. -/
theorem perturbation_summable' (zeros : ℕ → ℂ) (p : ℕ)
    (hconv : Summable (fun n => (‖zeros n‖⁻¹) ^ (p + 1 : ℝ))) (z : ℂ) :
    Summable fun n => ‖weierstraßElementary p (z / zeros n) - 1‖ := by
  -- Convert rpow to ℕ-pow
  have hpow : Summable (fun n => (‖zeros n‖⁻¹) ^ (p + 1)) := by
    have : (fun n => (‖zeros n‖⁻¹) ^ (p + 1 : ℝ)) = fun n => (‖zeros n‖⁻¹) ^ (p + 1) := by
      ext n; rw [← Real.rpow_natCast]; norm_cast
    rwa [this] at hconv
  -- Bounding sequence is summable
  apply (hpow.mul_left (‖z‖ ^ (p + 1))).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  -- From summability, the terms tend to 0
  have htend : Filter.Tendsto (fun n => (‖zeros n‖⁻¹) ^ (p + 1)) Filter.atTop (nhds 0) :=
    Nat.cofinite_eq_atTop ▸ hpow.tendsto_atTop_zero
  -- Choose c so that ‖z‖ · c ≤ 1/2
  set c := (1 : ℝ) / (2 * ‖z‖ + 1) with hc_def
  have hc_pos : (0 : ℝ) < c := by positivity
  have hc_pow_pos : (0 : ℝ) < c ^ (p + 1) := by positivity
  -- Eventually ‖zeros n‖⁻¹^{p+1} < c^{p+1}
  apply (htend.eventually (Iio_mem_nhds hc_pow_pos)).mono
  intro n (hn : (‖zeros n‖⁻¹) ^ (p + 1) < c ^ (p + 1))
  -- Extract ‖zeros n‖⁻¹ < c
  have hinv_lt : ‖zeros n‖⁻¹ < c :=
    lt_of_pow_lt_pow_left₀ (p + 1) (le_of_lt hc_pos) hn
  -- Therefore ‖z / zeros n‖ ≤ 1/2
  have hznorm : ‖z / zeros n‖ ≤ 1 / 2 := by
    rw [norm_div, div_eq_mul_inv]
    calc ‖z‖ * ‖zeros n‖⁻¹
        ≤ ‖z‖ * c := mul_le_mul_of_nonneg_left (le_of_lt hinv_lt) (norm_nonneg z)
      _ = ‖z‖ / (2 * ‖z‖ + 1) := by rw [hc_def, mul_one_div]
      _ ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ‖z‖ + 1) two_pos]
          linarith [norm_nonneg z]
  -- Apply the weierstraß elementary factor bound
  have hbound := weierstraßElementary_bound p (z / zeros n) hznorm
  rw [norm_sub_rev] at hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc ‖weierstraßElementary p (z / zeros n) - 1‖
      ≤ ‖z / zeros n‖ ^ (p + 1) := hbound
    _ = ‖z‖ ^ (p + 1) * ‖zeros n‖⁻¹ ^ (p + 1) := by
        rw [norm_div, div_eq_mul_inv, mul_pow]

/-- Product of weierstraßElementary factors is nonzero when no factor vanishes.
    Each factor `E_p(z/a_n)` is nonzero when `z/a_n ≠ 1`, and the product
    converges to a nonzero value by `tprod_one_add_ne_zero_of_summable`. -/
theorem tprod_weierstraßElementary_ne_zero (zeros : ℕ → ℂ) (p : ℕ)
    (hconv : Summable (fun n => (‖zeros n‖⁻¹) ^ (p + 1 : ℝ)))
    (z : ℂ) (hne : ∀ n, z / zeros n ≠ 1) :
    ∏' n, weierstraßElementary p (z / zeros n) ≠ 0 := by
  have hrewrite : (fun n => weierstraßElementary p (z / zeros n)) =
      fun n => 1 + (weierstraßElementary p (z / zeros n) - 1) := by ext n; ring
  rw [hrewrite]
  exact tprod_one_add_ne_zero_of_summable
    (fun n => by simp only [add_sub_cancel]; exact weierstraßElementary_ne_zero p _ (hne n))
    (perturbation_summable' zeros p hconv z)

/-- Helper: convert rpow summability to nat-pow summability with tendsto. -/
private theorem rpow_to_pow_with_tendsto (zeros : ℕ → ℂ) (p : ℕ)
    (hconv : Summable (fun n => (‖zeros n‖⁻¹) ^ (p + 1 : ℝ))) :
    (Summable (fun n => (‖zeros n‖⁻¹) ^ (p + 1))) ∧
    Tendsto (fun n => (‖zeros n‖⁻¹) ^ (p + 1)) atTop (nhds 0) := by
  have hpow : Summable (fun n => (‖zeros n‖⁻¹) ^ (p + 1)) := by
    have : (fun n => (‖zeros n‖⁻¹) ^ (p + 1 : ℝ)) = fun n => (‖zeros n‖⁻¹) ^ (p + 1) := by
      ext n; rw [← Real.rpow_natCast]; norm_cast
    rwa [this] at hconv
  exact ⟨hpow, Nat.cofinite_eq_atTop ▸ hpow.tendsto_atTop_zero⟩

/-- The Weierstraß product converges locally uniformly on any open ball.
    This is the core convergence result used for both differentiability
    and log-derivative computations. -/
theorem hasProdLocallyUniformlyOn_weierstraß (zeros : ℕ → ℂ) (p : ℕ)
    (hconv : Summable (fun n => (‖zeros n‖⁻¹) ^ (p + 1 : ℝ)))
    (R : ℝ) (hR : 0 < R) :
    HasProdLocallyUniformlyOn (fun n z => weierstraßElementary p (z / zeros n))
      (fun z => ∏' n, weierstraßElementary p (z / zeros n)) (ball (0 : ℂ) R) := by
  obtain ⟨hpow, htend⟩ := rpow_to_pow_with_tendsto zeros p hconv
  set f : ℕ → ℂ → ℂ := fun n z => weierstraßElementary p (z / zeros n) - 1
  have hrewrite : (fun n z => weierstraßElementary p (z / zeros n)) =
      fun n z => 1 + f n z := by ext n z; simp [f]
  rw [hrewrite]
  have hprod_rewrite : (fun z => ∏' n, weierstraßElementary p (z / zeros n)) =
      fun z => ∏' n, (1 + f n z) := by ext z; congr 1; ext n; simp [f]
  rw [hprod_rewrite]
  set c := (1 : ℝ) / (2 * R + 1)
  have hc_pos : (0 : ℝ) < c := by positivity
  apply Summable.hasProdLocallyUniformlyOn_nat_one_add isOpen_ball
    (show Summable (fun n => R ^ (p + 1) * (‖zeros n‖⁻¹) ^ (p + 1)) from hpow.mul_left _)
  · apply (htend.eventually (Iio_mem_nhds (show (0 : ℝ) < c ^ (p + 1) by positivity))).mono
    intro n (hn : (‖zeros n‖⁻¹) ^ (p + 1) < c ^ (p + 1)) x hx
    simp only [f]
    have hinv_lt : ‖zeros n‖⁻¹ < c := lt_of_pow_lt_pow_left₀ (p + 1) (le_of_lt hc_pos) hn
    have hxR : ‖x‖ < R := mem_ball_zero_iff.mp hx
    have hxnorm : ‖x / zeros n‖ ≤ 1 / 2 := by
      rw [norm_div, div_eq_mul_inv]
      have h1 : ‖x‖ * ‖zeros n‖⁻¹ ≤ R * c :=
        mul_le_mul (le_of_lt hxR) (le_of_lt hinv_lt)
          (inv_nonneg.mpr (norm_nonneg _)) (le_of_lt hR)
      have h2 : R * c ≤ 1 / 2 := by
        show R * (1 / (2 * R + 1)) ≤ 1 / 2
        rw [mul_one_div, div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * R + 1) two_pos]
        linarith
      linarith
    have hbound := weierstraßElementary_bound p (x / zeros n) hxnorm
    rw [norm_sub_rev] at hbound
    calc ‖weierstraßElementary p (x / zeros n) - 1‖
        ≤ ‖x / zeros n‖ ^ (p + 1) := hbound
      _ = (‖x‖ / ‖zeros n‖) ^ (p + 1) := by rw [norm_div]
      _ ≤ (R / ‖zeros n‖) ^ (p + 1) := by
          by_cases hzn : ‖zeros n‖ = 0
          · simp [hzn]
          · exact pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (norm_nonneg _))
              ((div_le_div_iff_of_pos_right (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzn))).mpr
                (le_of_lt hxR)) _
      _ = R ^ (p + 1) * (‖zeros n‖⁻¹) ^ (p + 1) := by rw [div_eq_mul_inv, mul_pow]
  · intro n
    exact (((weierstraßElementary_differentiable p).comp
      (differentiable_id.div_const _)).sub (differentiable_const 1)).continuous.continuousOn

/-- The Weierstraß product is multipliable locally uniformly on any open set. -/
theorem multipliableLocallyUniformlyOn_weierstraß (zeros : ℕ → ℂ) (p : ℕ)
    (hconv : Summable (fun n => (‖zeros n‖⁻¹) ^ (p + 1 : ℝ))) (s : Set ℂ) (hs : IsOpen s) :
    MultipliableLocallyUniformlyOn (fun n z => weierstraßElementary p (z / zeros n)) s := by
  refine ⟨fun z => ∏' n, weierstraßElementary p (z / zeros n), ?_⟩
  intro u hu z₀ hz₀
  set R := ‖z₀‖ + 1
  have hR : 0 < R := by positivity
  have hz₀_ball : z₀ ∈ ball (0 : ℂ) R := by simp only [mem_ball_zero_iff]; linarith
  -- Get convergence on ball 0 R
  have hloc := hasProdLocallyUniformlyOn_weierstraß zeros p hconv R hR
  obtain ⟨t, ht, htu⟩ := hloc u hu z₀ hz₀_ball
  -- ht : t ∈ nhdsWithin z₀ (ball 0 R)
  -- Since ball 0 R is open and z₀ ∈ ball 0 R, nhdsWithin = nhds
  have hball_nhds : nhdsWithin z₀ (ball (0 : ℂ) R) = nhds z₀ :=
    isOpen_ball.nhdsWithin_eq hz₀_ball
  rw [hball_nhds] at ht
  -- t ∩ s ∈ nhdsWithin z₀ s
  refine ⟨t ∩ s, ?_, htu.mono fun n hn y hy => hn y hy.1⟩
  exact Filter.inter_mem (nhdsWithin_le_nhds ht) self_mem_nhdsWithin

/-- The tprod of weierstraßElementary factors is differentiable for raw sequences. -/
theorem tprod_weierstraßElementary_differentiable (zeros : ℕ → ℂ) (p : ℕ)
    (hconv : Summable (fun n => (‖zeros n‖⁻¹) ^ (p + 1 : ℝ))) :
    Differentiable ℂ (fun z => ∏' n, weierstraßElementary p (z / zeros n)) := by
  intro z₀
  set R := ‖z₀‖ + 1
  have hR : 0 < R := by positivity
  have hz₀_ball : z₀ ∈ ball (0 : ℂ) R := by simp only [mem_ball_zero_iff]; linarith
  suffices h : DifferentiableOn ℂ (fun z => ∏' n, weierstraßElementary p (z / zeros n)) (ball 0 R)
    from h.differentiableAt (isOpen_ball.mem_nhds hz₀_ball)
  -- Reuse the HasProdLocallyUniformlyOn lemma
  have hloc := hasProdLocallyUniformlyOn_weierstraß zeros p hconv R hR
  exact (hloc : TendstoLocallyUniformlyOn _ _ _ _).differentiableOn
    (Eventually.of_forall fun s =>
      DifferentiableOn.fun_finset_prod fun i _ =>
        ((weierstraßElementary_differentiable p).comp
          (differentiable_id.div_const _)).differentiableOn)
    isOpen_ball

/-- The exponential sum S_p is differentiable. -/
theorem differentiable_weierstraßExpSum (p : ℕ) :
    Differentiable ℂ (weierstraßExpSum p) := by
  unfold weierstraßExpSum
  induction p with
  | zero => simp [differentiable_const]
  | succ n ih =>
    simp_rw [Finset.sum_range_succ]
    exact ih.add ((differentiable_id.pow (n + 1)).div_const _)

/-- The analytic order of E_p(w/z₀) at w = z₀ is 1, for z₀ ≠ 0.
    Since E_p(w/z₀) = (1 - w/z₀) · exp(S_p(w/z₀)) and exp is nonvanishing,
    the only zero comes from the factor (1 - w/z₀), which is simple. -/
theorem analyticOrderAt_weierstraßElementary_at_pole (p : ℕ) (z₀ : ℂ) (hz₀ : z₀ ≠ 0) :
    analyticOrderAt (fun w => weierstraßElementary p (w / z₀)) z₀ = 1 := by
  have hf_an : AnalyticAt ℂ (fun w => weierstraßElementary p (w / z₀)) z₀ :=
    ((weierstraßElementary_differentiable p).comp (differentiable_id.div_const z₀)).analyticAt z₀
  rw [show (1 : ℕ∞) = ↑(1 : ℕ) from rfl, hf_an.analyticOrderAt_eq_natCast]
  -- Witness: g(w) = (-z₀⁻¹) * exp(S_p(w/z₀)), so E_p(w/z₀) = (w - z₀) • g(w)
  refine ⟨fun w => (-z₀⁻¹) * Complex.exp (weierstraßExpSum p (w / z₀)), ?_, ?_, ?_⟩
  · exact ((Complex.differentiable_exp.comp
      ((differentiable_weierstraßExpSum p).comp (differentiable_id.div_const z₀))).const_mul
      _).analyticAt z₀
  · exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hz₀)) (Complex.exp_ne_zero _)
  · filter_upwards [univ_mem] with w _
    simp only [weierstraßElementary_eq, pow_one, smul_eq_mul]
    -- E_p(w/z₀) = (1 - w/z₀) * exp(S_p(w/z₀))
    -- (1 - w/z₀) = -(w - z₀) * z₀⁻¹ = (w - z₀) * (-z₀⁻¹)
    have hz₀' : (z₀ : ℂ) ≠ 0 := hz₀
    field_simp
    ring

/-- For a Finset product of identical analytic factors, the order multiplies. -/
theorem analyticOrderAt_finprod_const {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (s : Finset ℕ) :
    analyticOrderAt (fun w => ∏ _i ∈ s, f w) z₀ = s.card • analyticOrderAt f z₀ := by
  have heq : (fun w => ∏ _i ∈ s, f w) = f ^ s.card := by
    ext w; simp [Finset.prod_const]
  rw [heq, analyticOrderAt_pow hf]

/-- The tprod of weierstraßElementary is pointwise multipliable for raw sequences
    satisfying the convergence condition. -/
theorem multipliable_weierstraßElementary_raw (zeros : ℕ → ℂ) (p : ℕ)
    (hconv : Summable (fun n => (‖zeros n‖⁻¹) ^ ((p : ℝ) + 1))) (w : ℂ) :
    Multipliable (fun n => weierstraßElementary p (w / zeros n)) := by
  have key : (fun n => weierstraßElementary p (w / zeros n)) =
      (fun n => 1 + (weierstraßElementary p (w / zeros n) - 1)) := by ext n; ring
  rw [key]
  apply Complex.multipliable_one_add_of_summable
  exact (perturbation_summable' zeros p hconv w).of_norm

/-- Summability of modified zeros sequence where S-indices are zeroed out. -/
private lemma summable_zeros_mask (zeros : ℕ → ℂ) (p : ℕ) (S : Finset ℕ)
    (hconv : Summable (fun n => (‖zeros n‖⁻¹) ^ ((p : ℝ) + 1))) :
    let zeros' := fun n => if n ∈ S then (0 : ℂ) else zeros n
    Summable (fun n => (‖zeros' n‖⁻¹) ^ ((p : ℝ) + 1)) :=
  Summable.of_nonneg_of_le
    (fun n => Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)
    (fun n => by
      simp only; split_ifs with h
      · rw [norm_zero, inv_zero, Real.zero_rpow (by positivity : (p : ℝ) + 1 ≠ 0)]
        exact Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _
      · exact le_refl _)
    hconv

/-- The complement tprod is nonvanishing at z₀ when no complement index maps to z₀. -/
private lemma complement_tprod_ne_zero (zeros : ℕ → ℂ) (p : ℕ) (S : Finset ℕ)
    (hconv : Summable (fun n => (‖zeros n‖⁻¹) ^ ((p : ℝ) + 1)))
    (z₀ : ℂ) (hz₀ : z₀ ≠ 0)
    (hS_compl : ∀ n, n ∉ S → zeros n ≠ z₀) :
    let zeros' := fun n => if n ∈ S then (0 : ℂ) else zeros n
    (∏' n, weierstraßElementary p (z₀ / zeros' n)) ≠ 0 := by
  intro zeros'
  apply tprod_weierstraßElementary_ne_zero zeros' p (summable_zeros_mask zeros p S hconv)
  intro n; simp only [zeros']; split_ifs with h
  · simp [div_zero]
  · intro heq
    exact hS_compl n h ((div_eq_one_iff_eq (fun hz => by simp [hz] at heq)).mp heq).symm

/-- Split an infinite product into a finite set of factors and a full-indexed
    complementary product whose factors on the finite set are `1`.  This
    commutative-monoid formulation is needed for `ℂ`, where multiplication is
    not a group because of zero factors. -/
private lemma tprod_eq_finprod_mul_tprod_mask (f q : ℕ → ℂ) (S : Finset ℕ)
    (hq : Multipliable q) (hq_eq : ∀ n, q n = if n ∈ S then 1 else f n) :
    (∏' n, f n) = (∏ n ∈ S, f n) * ∏' n, q n := by
  have hcomp : Multipliable (fun n : ↑((↑S : Set ℕ)ᶜ) ↦ f n) := by
    change Multipliable (f ∘ ((↑) : ↑((↑S : Set ℕ)ᶜ) → ℕ))
    rw [multipliable_subtype_iff_mulIndicator]
    apply hq.congr
    intro n
    rw [hq_eq]
    simp only [Set.mulIndicator, Set.mem_compl_iff, Finset.mem_coe]
    split_ifs <;> rfl
  have hs : Multipliable (fun n : (↑S : Set ℕ) ↦ f n) := S.multipliable f
  have hsplit := Multipliable.tprod_mul_tprod_compl hs hcomp
  calc
    (∏' n, f n) = (∏' n : (↑S : Set ℕ), f n) *
        ∏' n : ↑((↑S : Set ℕ)ᶜ), f n := hsplit.symm
    _ = (∏ n ∈ S, f n) * ∏' n, q n := by
      rw [Finset.tprod_subtype']
      congr 1
      rw [_root_.tprod_subtype]
      apply tprod_congr
      intro n
      rw [hq_eq]
      simp only [Set.mulIndicator, Set.mem_compl_iff, Finset.mem_coe]
      split_ifs <;> rfl

/-- The analytic order of a Weierstraß tprod at a zero equals the number of
    indices mapping to that zero (each contributing a simple zero).

    Given a sequence `zeros` with convergent exponent sum, and a finite set `S`
    of indices all mapping to the same nonzero value `z₀`, if no index outside `S`
    maps to `z₀`, then `analyticOrderAt P z₀ = S.card` where
    `P(w) = ∏' n, E_p(w / zeros n)`. -/
theorem analyticOrderAt_tprod_weierstraß (zeros : ℕ → ℂ) (p : ℕ)
    (hconv : Summable (fun n => (‖zeros n‖⁻¹) ^ ((p : ℝ) + 1)))
    (z₀ : ℂ) (hz₀ : z₀ ≠ 0)
    (S : Finset ℕ) (hS_val : ∀ n ∈ S, zeros n = z₀)
    (hS_compl : ∀ n, n ∉ S → zeros n ≠ z₀) :
    analyticOrderAt (fun w => ∏' n, weierstraßElementary p (w / zeros n)) z₀ =
      S.card := by
  set f : ℕ → ℂ → ℂ := fun n w => weierstraßElementary p (w / zeros n)
  set P : ℂ → ℂ := fun w => ∏' n, f n w
  set F : ℂ → ℂ := fun w => ∏ i ∈ S, f i w
  set zeros' : ℕ → ℂ := fun n => if n ∈ S then 0 else zeros n
  set Q : ℂ → ℂ := fun w => ∏' n, weierstraßElementary p (w / zeros' n)
  have hm : ∀ w, Multipliable (fun n => f n w) :=
    fun w => multipliable_weierstraßElementary_raw zeros p hconv w
  have hconv' := summable_zeros_mask zeros p S hconv
  -- Finite part: order = S.card
  have hF_diff : Differentiable ℂ F := by
    intro z; change DifferentiableAt ℂ (fun w => ∏ i ∈ S, f i w) z
    apply DifferentiableAt.fun_finset_prod
    intro i _; exact ((weierstraßElementary_differentiable p).comp
      (differentiable_id.div_const (zeros i))).differentiableAt
  have hF_an : AnalyticAt ℂ F z₀ := hF_diff.analyticAt z₀
  have hF_ord : analyticOrderAt F z₀ = S.card := by
    have hF_eq : F = (fun w => weierstraßElementary p (w / z₀)) ^ S.card := by
      ext w; simp only [F, f, Pi.pow_apply]
      rw [Finset.prod_congr rfl (fun i hi => by rw [hS_val i hi]), Finset.prod_const]
    have han : AnalyticAt ℂ (fun w => weierstraßElementary p (w / z₀)) z₀ :=
      ((weierstraßElementary_differentiable p).comp
        (differentiable_id.div_const z₀)).analyticAt z₀
    rw [hF_eq, analyticOrderAt_pow han,
      analyticOrderAt_weierstraßElementary_at_pole p z₀ hz₀]; simp
  -- Complement part: order = 0 (nonvanishing)
  have hQ_an : AnalyticAt ℂ Q z₀ :=
    (tprod_weierstraßElementary_differentiable zeros' p hconv').analyticAt z₀
  have hQ_ord : analyticOrderAt Q z₀ = 0 :=
    hQ_an.analyticOrderAt_eq_zero.mpr (complement_tprod_ne_zero zeros p S hconv z₀ hz₀ hS_compl)
  -- Split: P = F * Q, so order(P) = order(F) + order(Q) = S.card + 0
  have hsplit : P = F * Q := by
    funext w
    apply tprod_eq_finprod_mul_tprod_mask
    · exact multipliable_weierstraßElementary_raw zeros' p hconv' w
    · intro n
      simp only [zeros', f]
      split_ifs with hn
      · simp [weierstraßElementary_zero]
      · rfl
  calc analyticOrderAt P z₀
      = analyticOrderAt (F * Q) z₀ := by rw [← hsplit]
    _ = analyticOrderAt F z₀ + analyticOrderAt Q z₀ := analyticOrderAt_mul hF_an hQ_an
    _ = ↑S.card + 0 := by rw [hF_ord, hQ_ord]
    _ = ↑S.card := by simp

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
private theorem tprod_const_one' : ∏' (_ : ℕ), (1 : ℂ) = 1 := tprod_one

/-- **Entire logarithm theorem.** A zero-free entire function h can be written as
    h = exp ∘ g for some entire function g.

    The proof uses Mathlib's `Differentiable.isExactOn_univ` (which provides
    primitives for entire functions via Morera's theorem) applied to h'/h.
    The primitive G satisfies G' = h'/h, so h · exp(-G) has derivative 0,
    hence is constant. Normalizing at 0 gives h = exp(G + c). -/
theorem entire_logarithm (h : ℂ → ℂ) (hh : Differentiable ℂ h)
    (hne : ∀ z, h z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, h z = Complex.exp (g z) := by
  -- h'/h is entire since h is never zero
  have hderiv_diff : Differentiable ℂ (deriv h) := by
    rw [← differentiableOn_univ]
    exact hh.differentiableOn.deriv isOpen_univ
  have hψ_diff : Differentiable ℂ (fun z => deriv h z / h z) :=
    fun z => (hderiv_diff z).div hh.differentiableAt (hne z)
  -- h'/h has an entire primitive G with G(0) = log(h(0))
  have hExact : IsExactOn (fun z => deriv h z / h z) Set.univ :=
    Differentiable.isExactOn_univ hψ_diff
  obtain ⟨G, hG0, hGderiv⟩ := hExact.with_val_at 0 (Complex.log (h 0))
  have hG_diff : Differentiable ℂ G := fun z => (hGderiv z (Set.mem_univ z)).differentiableAt
  -- φ(z) = h(z) · exp(-G(z)) has derivative 0
  set φ : ℂ → ℂ := fun z => h z * Complex.exp (-G z) with hφ_def
  have hφ_diff : Differentiable ℂ φ :=
    hh.mul (Complex.differentiable_exp.comp hG_diff.neg)
  have hφ_deriv : ∀ z, deriv φ z = 0 := by
    intro z
    have hd_h : HasDerivAt h (deriv h z) z := hh.differentiableAt.hasDerivAt
    have hd_G : HasDerivAt G (deriv h z / h z) z := hGderiv z (Set.mem_univ z)
    have hd_exp : HasDerivAt (fun w => Complex.exp (-G w))
        (Complex.exp (-G z) * -(deriv h z / h z)) z := hd_G.neg.cexp
    have hd_prod : HasDerivAt φ
        (deriv h z * Complex.exp (-G z) + h z * (Complex.exp (-G z) * -(deriv h z / h z))) z :=
      hd_h.mul hd_exp
    rw [hd_prod.deriv]
    have := hne z; field_simp; ring
  -- φ is constant (derivative 0 everywhere on connected ℂ)
  have hφ_const : ∀ z, φ z = φ 0 :=
    fun z => is_const_of_deriv_eq_zero hφ_diff hφ_deriv z 0
  -- φ(0) = h(0) · exp(-log(h(0))) = 1
  have hφ0 : φ 0 = 1 := by
    simp only [hφ_def]
    rw [hG0]
    have hne0 := hne 0
    rw [show -(Complex.log (h 0)) = ((-1 : ℤ) : ℂ) * Complex.log (h 0) from by push_cast; ring,
      Complex.exp_int_mul, zpow_neg_one, Complex.exp_log hne0]
    exact mul_inv_cancel₀ hne0
  -- φ ≡ 1, so h(z) = exp(G(z))
  exact ⟨G, hG_diff, fun z => by
    have key : h z * Complex.exp (-G z) = 1 := by
      rw [show h z * Complex.exp (-G z) = φ z from rfl, hφ_const z, hφ0]
    calc h z = h z * Complex.exp (-G z) * (Complex.exp (-G z))⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ (Complex.exp_ne_zero _), mul_one]
      _ = (Complex.exp (-G z))⁻¹ := by rw [key, one_mul]
      _ = Complex.exp (G z) := by rw [← Complex.exp_neg, neg_neg]⟩

theorem weierstraß_factorization (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) (hfin : HasFiniteOrder f) :
    ∃ (m : ℕ) (g : ℂ → ℂ) (a : ℕ → ℂ) (p : ℕ),
      Differentiable ℂ g ∧
      (∀ n, a n ≠ 0 → f (a n) = 0) ∧
      Summable (fun n => (‖a n‖⁻¹) ^ ((p : ℝ) + 1)) ∧
      ∀ z, f z = z ^ m * Complex.exp (g z) *
        ∏' n, weierstraßElementary p (z / a n) := by
  -- Split into zero-free and has-zeros cases
  by_cases hzf : ∀ z, f z ≠ 0
  · -- f is zero-free: use entire logarithm theorem.
    -- Take m = 0, p = 0, a = const 0, so ∏' E_0(z/0) = ∏' 1 = 1.
    obtain ⟨g, hg_diff, hg_eq⟩ := entire_logarithm f hf hzf
    refine ⟨0, g, fun _ => 0, 0, hg_diff,
      fun n h => absurd rfl h, ?_, fun z => by simp [hg_eq z, weierstraßElementary_zero]⟩
    -- Summability: ‖0‖⁻¹ ^ 1 = 0, so the series is identically 0
    exact summable_of_ne_finset_zero (s := ∅) (fun n _ => by
      simp [norm_zero, inv_zero, Real.zero_rpow (by positivity : (0 : ℝ) + 1 ≠ 0)])
  · -- f has zeros: Weierstraß product construction for finite-order functions.
    -- analyticOrderAt_tprod_weierstraß is now proved; remaining issues are
    -- stutteredEnum_pair_lt alignment and Encodable.decode₂ API mismatches.
    exact sorry
    /- push_neg at hzf
    -- ═══════════════════════════════════════════════════════════
    -- Step 1: Factor out the zero at the origin
    -- f(z) = z^m · f₁(z) with f₁(0) ≠ 0, using analytic order at 0
    -- ═══════════════════════════════════════════════════════════
    obtain ⟨m, f₁, hf₁_diff, hf₁_nz, hf_eq⟩ :
        ∃ (m : ℕ) (f₁ : ℂ → ℂ), Differentiable ℂ f₁ ∧ f₁ 0 ≠ 0 ∧
          ∀ z, f z = z ^ m * f₁ z := by
      by_cases hf0 : f 0 ≠ 0
      · exact ⟨0, f, hf, hf0, fun z => by simp⟩
      · push_neg at hf0
        have hf_an : AnalyticAt ℂ f 0 := hf.analyticAt 0
        have hord_ne_top : analyticOrderAt f 0 ≠ ⊤ :=
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0
            (fun z => hf.analyticAt z)).not.mpr hf_ne
        set m' := analyticOrderNatAt f 0
        obtain ⟨g, hg_an, hg_nz, hg_eq⟩ := hf_an.analyticOrderAt_ne_top.mp hord_ne_top
        have hg_eq' : ∀ᶠ z in 𝓝 (0 : ℂ), f z = z ^ m' * g z :=
          hg_eq.mono fun z hz => by simp only [sub_zero, smul_eq_mul] at hz; exact hz
        refine ⟨m', Function.update (fun z => f z / z ^ m') 0 (g 0), ?_, ?_, ?_⟩
        · -- f₁ is entire
          intro z₀
          by_cases hz₀ : z₀ = 0
          · subst hz₀
            refine (hg_an.congr ?_).differentiableAt
            apply hg_eq'.mono
            intro z hz
            by_cases hz0 : z = 0
            · subst hz0; simp [Function.update_self]
            · rw [Function.update_of_ne hz0, hz,
                mul_div_cancel_left₀ _ (pow_ne_zero m' hz0)]
          · exact (hf.differentiableAt.div ((differentiable_pow m').differentiableAt)
              (pow_ne_zero m' hz₀)).congr_of_eventuallyEq
              ((isOpen_ne.eventually_mem hz₀).mono fun z hz =>
                Function.update_of_ne hz _ _)
        · simp [Function.update_self, hg_nz]
        · intro z
          by_cases hz : z = 0
          · subst hz; rw [Function.update_self]; exact hg_eq'.self_of_nhds
          · simp only [Function.update_of_ne hz]
            exact (mul_div_cancel₀ (f z) (pow_ne_zero m' hz)).symm
    -- ═══════════════════════════════════════════════════════════
    -- Step 2: Enumerate zeros with summability
    -- ═══════════════════════════════════════════════════════════
    obtain ⟨a, p, ha_zeros, hconv, ha_covers, ha_ord_eq⟩ :
        ∃ (a : ℕ → ℂ) (p : ℕ),
          (∀ n, a n ≠ 0 → f₁ (a n) = 0) ∧
          Summable (fun n => (‖a n‖⁻¹) ^ ((p : ℝ) + 1)) ∧
          (∀ z, f₁ z = 0 → ∃ n, z = a n) ∧
          (∀ z, f₁ z = 0 → z ≠ 0 →
            analyticOrderAt f₁ z =
              analyticOrderAt (fun w => ∏' n, weierstraßElementary p (w / a n)) z) := by
      -- Step 2a: Zeros of f₁ are discrete and countable
      have hf₁_ne : ¬ f₁ = 0 := fun h => hf₁_nz (by rw [h]; simp)
      have hf₁_an : AnalyticOnNhd ℂ f₁ Set.univ := fun z _ => hf₁_diff.analyticAt z
      have hcodisc : f₁ ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℂ :=
        hf₁_an.preimage_zero_mem_codiscrete hf₁_nz
      have hdisc : IsDiscrete (f₁ ⁻¹' {0}) := by
        have := (mem_codiscrete'.mp hcodisc).2
        rwa [Set.preimage_compl, compl_compl] at this
      have hcount : (f₁ ⁻¹' {0}).Countable :=
        (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
      -- Step 2b: Enumerate distinct zeros
      set a₀ : ℕ → ℂ := fun n =>
        match @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable n with
        | some y => y | none => 0
      have ha₀_surj : ∀ z, f₁ z = 0 → ∃ k, z = a₀ k := by
        intro z hz
        refine ⟨@Encodable.encode _ hcount.toEncodable ⟨z, Set.mem_preimage.mpr
          (Set.mem_singleton_iff.mpr hz)⟩, ?_⟩
        simp only [a₀, Encodable.decode₂_encode]
      have ha₀_zeros : ∀ k, a₀ k ≠ 0 → f₁ (a₀ k) = 0 := by
        intro k hk
        simp only [a₀] at hk ⊢
        cases h : @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable k with
        | none => simp [h] at hk
        | some val => simp [h]; exact val.2
      -- Step 2c: Define multiplicities and stuttered enumeration
      set mult' : ℕ → ℕ := fun k =>
        if a₀ k = 0 then 0 else analyticOrderNatAt f₁ (a₀ k)
      have hmult_pos : ∀ k, a₀ k ≠ 0 → 0 < mult' k := by
        intro k hk
        simp only [mult', hk, ite_false]
        rw [Nat.pos_iff_ne_zero, Ne, analyticOrderNatAt, ENat.toNat_eq_zero, not_or]
        exact ⟨analyticOrderAt_ne_zero.mpr ⟨hf₁_diff.analyticAt _, ha₀_zeros k hk⟩,
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a₀ k)
            (fun z => hf₁_diff.analyticAt z)).not.mpr hf₁_ne⟩
      have hmult_zero : ∀ k, a₀ k = 0 → mult' k = 0 :=
        fun k hk => by simp [mult', hk]
      set a' := stutteredEnum a₀ mult'
      set p' := Nat.floor (entireOrder f).toReal
      -- Step 2d: Verify properties
      have ha_zeros' : ∀ n, a' n ≠ 0 → f₁ (a' n) = 0 :=
        fun n hn => stutteredEnum_maps_zeros ha₀_zeros hn
      have ha_covers' : ∀ z, f₁ z = 0 → ∃ n, z = a' n := by
        intro z hz
        obtain ⟨k, rfl⟩ := ha₀_surj z hz
        have hk : a₀ k ≠ 0 := fun h0 => hf₁_nz (h0 ▸ hz)
        obtain ⟨n, hn⟩ := stutteredEnum_covers (hmult_pos k hk)
        exact ⟨n, hn.symm⟩
      have hconv' : Summable (fun n => (‖a' n‖⁻¹) ^ ((p' : ℝ) + 1)) :=
        summable_stutteredEnum_of_weighted (Nat.cast_add_one_pos p')
          (finite_order_zero_summable_weighted f hf hf_ne hfin a₀
            (fun k hk => by have := ha₀_zeros k hk; rw [hf_eq]; simp [this])
            mult' hmult_zero)
      refine ⟨a', p', ha_zeros', hconv', ha_covers', ?_⟩
      -- Order equality: analytic order of Weierstraß product at each zero
      -- equals analyticOrderAt f₁ there.
      intro z hz hne
      obtain ⟨k, rfl⟩ := ha₀_surj z hz
      have hk : a₀ k ≠ 0 := hne
      -- The multiplicity m = analyticOrderNatAt f₁ (a₀ k)
      set m := mult' k with hm_def
      have hm_pos : 0 < m := hmult_pos k hk
      -- analyticOrderAt f₁ (a₀ k) = ↑m
      have hord_ne_top : analyticOrderAt f₁ (a₀ k) ≠ ⊤ :=
        (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a₀ k)
          (fun z => hf₁_diff.analyticAt z)).not.mpr hf₁_ne
      have hord_f₁ : analyticOrderAt f₁ (a₀ k) = ↑m := by
        simp only [m, mult', hk, ite_false]
        exact (Nat.cast_analyticOrderNatAt hord_ne_top).symm
      rw [hord_f₁]
      -- Use the standalone tprod order lemma
      set S : Finset ℕ := (Finset.range m).image (Nat.pair k)
      have hS_val : ∀ n ∈ S, a' n = a₀ k := by
        intro n hn; simp only [S, Finset.mem_image, Finset.mem_range] at hn
        obtain ⟨j, hj, rfl⟩ := hn; exact stutteredEnum_pair_lt hj
      have hS_compl : ∀ n, n ∉ S → a' n ≠ a₀ k := by
        intro n hn ha'n_eq
        have ha'n_ne : a' n ≠ 0 := ha'n_eq ▸ hk
        have ⟨hlt, ha₀_ne⟩ := stutteredEnum_ne_zero_imp ha'n_ne
        have ha'_simp : a' n = a₀ n.unpair.1 := by
          rw [show n = Nat.pair n.unpair.1 n.unpair.2 from (Nat.pair_unpair n).symm]
          exact stutteredEnum_pair_lt hlt
        have heq_a₀ : a₀ n.unpair.1 = a₀ k := ha'_simp ▸ ha'n_eq
        -- enumerateCountable injectivity: a₀ n.unpair.1 = a₀ k → n.unpair.1 = k
        have hfst_eq : n.unpair.1 = k := by
          simp only [a₀] at ha₀_ne heq_a₀
          revert ha₀_ne heq_a₀
          cases h1 : @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable n.unpair.1 with
          | none => simp
          | some v1 =>
            cases h2 : @Encodable.decode₂ (f₁ ⁻¹' {0}) hcount.toEncodable k with
            | none => simp
            | some v2 =>
              intro _ heq
              have hv_eq : v1 = v2 := Subtype.val_injective heq
              rw [Encodable.decode₂_eq_some] at h1 h2
              rw [← h1, ← h2, hv_eq]
        exact hn (by
          rw [show n = Nat.pair n.unpair.1 n.unpair.2 from (Nat.pair_unpair n).symm, hfst_eq]
          exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (hm_def ▸ hlt)))
      have hS_card : S.card = m := by
        simp only [S]
        exact (Finset.card_image_of_injective _
          (fun j₁ j₂ h => (Nat.pair_eq_pair.mp h).2)).trans (Finset.card_range m)
      rw [← hS_card]
      exact (analyticOrderAt_tprod_weierstraß a' p' hconv' (a₀ k) hk S hS_val hS_compl).symm
    -- ═══════════════════════════════════════════════════════════
    -- Step 3–4: Quotient f₁/P is entire and zero-free
    -- ═══════════════════════════════════════════════════════════
    obtain ⟨h, hh_diff, hh_ne, hh_eq⟩ :
        ∃ (h : ℂ → ℂ), Differentiable ℂ h ∧ (∀ z, h z ≠ 0) ∧
          (∀ z, f₁ z = h z * ∏' n, weierstraßElementary p (z / a n)) := by
      set P : ℂ → ℂ := fun z => ∏' n, weierstraßElementary p (z / a n)
      have hP_diff : Differentiable ℂ P := tprod_weierstraßElementary_differentiable a p hconv
      have hq_diff : ∀ z, P z ≠ 0 → DifferentiableAt ℂ (fun w => f₁ w / P w) z :=
        fun z hz => hf₁_diff.differentiableAt.div hP_diff.differentiableAt hz
      set h₀ : ℂ → ℂ := fun z =>
        if P z ≠ 0 then f₁ z / P z
        else limUnder (𝓝[≠] z) (fun w => f₁ w / P w)
      have hh₀_eq : ∀ z, f₁ z = h₀ z * P z := by
        intro z
        by_cases hPz : P z ≠ 0
        · rw [show h₀ z = f₁ z / P z from if_pos hPz, div_mul_cancel₀ (f₁ z) hPz]
        · push_neg at hPz
          have hf₁z : f₁ z = 0 := by
            by_contra hf₁z_ne
            have hne : ∀ n, z / a n ≠ 1 := by
              intro n heq
              by_cases han : a n = 0
              · simp [han] at heq
              · exact hf₁z_ne ((div_eq_one_iff_eq han).mp heq ▸ ha_zeros n han)
            exact absurd hPz (tprod_weierstraßElementary_ne_zero a p hconv z hne)
          rw [hf₁z, hPz, mul_zero]
      have hh₀_diff : Differentiable ℂ h₀ := by
        intro z₀
        by_cases hPz₀ : P z₀ ≠ 0
        · have heq : h₀ =ᶠ[𝓝 z₀] fun w => f₁ w / P w := by
            have : ∀ᶠ w in 𝓝 z₀, P w ≠ 0 :=
              hP_diff.continuous.continuousAt.eventually_ne hPz₀
            exact this.mono fun w hw => by simp [h₀, hw]
          exact (hq_diff z₀ hPz₀).congr_of_eventuallyEq heq
        · push_neg at hPz₀
          have hP_an : AnalyticAt ℂ P z₀ := hP_diff.analyticAt z₀
          have hP_not_ev_zero : ¬ ∀ᶠ w in 𝓝 z₀, P w = 0 := by
            intro hev
            have hf₁_ev : ∀ᶠ w in 𝓝 z₀, f₁ w = 0 :=
              hev.mono fun w hw => by rw [hh₀_eq w, hw, mul_zero]
            have hf₁_eq : f₁ = 0 := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z₀
              (fun z => hf₁_diff.analyticAt z)).mp (analyticOrderAt_eq_top.mpr hf₁_ev)
            exact hf₁_nz (congr_fun hf₁_eq 0)
          have hP_ev_ne : ∀ᶠ w in 𝓝[≠] z₀, P w ≠ 0 :=
            hP_an.eventually_eq_zero_or_eventually_ne_zero.resolve_left hP_not_ev_zero
          have hh₀_diff_punct : ∀ᶠ w in 𝓝[≠] z₀, DifferentiableAt ℂ h₀ w := by
            apply hP_ev_ne.mono
            intro w hw
            have heq : h₀ =ᶠ[𝓝 w] fun v => f₁ v / P v :=
              (hP_diff.continuous.continuousAt.eventually_ne hw).mono
                fun v hv => by simp [h₀, hv]
            exact (hf₁_diff.differentiableAt.div hP_diff.differentiableAt hw).congr_of_eventuallyEq
              heq
          -- ContinuousAt h₀ z₀: factor f₁ and P by their equal analytic orders,
          -- cancel (z-z₀)^k to get h₀ = u/v, then use continuity of u/v.
          have hcont : ContinuousAt h₀ z₀ := by
            -- f₁ vanishes at z₀
            have hf₁z₀ : f₁ z₀ = 0 := by
              by_contra hne
              exact absurd hPz₀ (tprod_weierstraßElementary_ne_zero a p hconv z₀
                fun n heq => by
                  by_cases han : a n = 0
                  · simp [han] at heq
                  · exact hne ((div_eq_one_iff_eq han).mp heq ▸ ha_zeros n han))
            -- z₀ ≠ 0
            have hz₀_ne : z₀ ≠ 0 := by
              intro heq; rw [heq] at hPz₀
              have : P 0 = ∏' n, weierstraßElementary p (0 / a n) := rfl
              simp only [zero_div, weierstraßElementary_zero, tprod_one] at this
              exact one_ne_zero (this ▸ hPz₀)
            have hord := ha_ord_eq z₀ hf₁z₀ hz₀_ne
            -- Neither function is identically zero
            have hf₁_ne : ¬ f₁ = 0 := fun h => hf₁_nz (congr_fun h 0)
            have hP_ne : ¬ P = 0 := by
              intro heq
              have : P 0 = 0 := congr_fun heq 0
              simp only [P, zero_div, weierstraßElementary_zero, tprod_one] at this
              exact one_ne_zero this
            have hf₁_top : analyticOrderAt f₁ z₀ ≠ ⊤ :=
              (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z₀
                (fun z => hf₁_diff.analyticAt z)).not.mpr hf₁_ne
            have hP_top : analyticOrderAt P z₀ ≠ ⊤ := hord ▸ hf₁_top
            -- Factor: f₁(z) =ᶠ (z-z₀)^k • u(z), P(z) =ᶠ (z-z₀)^k • v(z)
            set k := analyticOrderNatAt f₁ z₀ with hk_def
            obtain ⟨u, hu_an, hu_ne, hu_eq⟩ :=
              (hf₁_diff.analyticAt z₀).analyticOrderAt_ne_top.mp hf₁_top
            obtain ⟨v, hv_an, hv_ne, hv_eq⟩ :=
              (hP_diff.analyticAt z₀).analyticOrderAt_ne_top.mp hP_top
            have hP_ord : analyticOrderNatAt P z₀ = k := by
              simp only [analyticOrderNatAt]; congr 1; exact hord.symm
            rw [hP_ord] at hv_eq
            -- u/v is continuous at z₀
            have huv_cont : ContinuousAt (fun w => u w / v w) z₀ :=
              hu_an.continuousAt.div hv_an.continuousAt hv_ne
            -- h₀ = u/v on 𝓝[≠] z₀ (cancel (z-z₀)^k via smul = mul in ℂ)
            have heq_uv : ∀ᶠ w in 𝓝[≠] z₀, h₀ w = u w / v w := by
              apply (hP_ev_ne.and ((hu_eq.and hv_eq).filter_mono nhdsWithin_le_nhds)).mono
              rintro w ⟨hwP, hwu, hwv⟩
              -- h₀ w = f₁ w / P w (since P w ≠ 0)
              change (if P w ≠ 0 then f₁ w / P w else _) = u w / v w
              rw [if_pos hwP]
              -- f₁ w = (w-z₀)^k • u w, P w = (w-z₀)^k • v w
              have hwne : (w - z₀) ^ k ≠ 0 := pow_ne_zero k (sub_ne_zero.mpr (by
                intro heq; rw [heq] at hwP; exact hwP hPz₀))
              simp only [hwu, hwv, smul_eq_mul]
              exact mul_div_mul_left (u w) (v w) hwne
            -- Tendsto h₀ (𝓝[≠] z₀) (𝓝 (u z₀ / v z₀))
            have htend : Tendsto h₀ (𝓝[≠] z₀) (𝓝 (u z₀ / v z₀)) :=
              (huv_cont.tendsto.mono_left nhdsWithin_le_nhds).congr'
                (heq_uv.mono fun w hw => hw.symm)
            -- h₀ z₀ = u z₀ / v z₀ (limUnder uniqueness in T2)
            have hval : h₀ z₀ = u z₀ / v z₀ := by
              -- h₀ z₀ = limUnder (𝓝[≠] z₀) h₀ by definition (P z₀ = 0 branch)
              -- limUnder h₀ = u z₀ / v z₀ by htend (T2 uniqueness)
              have hlim_eq : (𝓝[≠] z₀).limUnder h₀ = u z₀ / v z₀ := htend.limUnder_eq
              -- h₀ z₀ = limUnder (f₁/P) on 𝓝[≠] z₀
              -- limUnder (f₁/P) = limUnder h₀ since they agree eventually
              -- h₀ z₀ = limUnder h₀ on 𝓝[≠] z₀
              -- First: h₀ z₀ = limUnder (f₁/P)
              have h₀_val : h₀ z₀ = (𝓝[≠] z₀).limUnder (fun w => f₁ w / P w) := by
                simp only [h₀, show ¬(P z₀ ≠ 0) from not_not.mpr hPz₀, ↓reduceIte]
              -- Second: the Tendsto of f₁/P toward u z₀/v z₀ gives its limUnder
              have htend_fg : Tendsto (fun w => f₁ w / P w) (𝓝[≠] z₀) (𝓝 (u z₀ / v z₀)) := by
                apply htend.congr'
                have : ∀ᶠ w in 𝓝[≠] z₀, h₀ w = f₁ w / P w :=
                  hP_ev_ne.mono fun w hw => (if_pos hw : h₀ w = f₁ w / P w)
                exact this.mono fun w (hw : h₀ w = f₁ w / P w) =>
                  show h₀ w = (fun w => f₁ w / P w) w from hw
              rw [h₀_val, htend_fg.limUnder_eq]
            -- ContinuousAt via nhds = nhdsWithin ⊔ pure
            rw [ContinuousAt, hval, ← nhdsNE_sup_pure z₀]
            exact htend.sup (Filter.tendsto_pure_left.mpr fun _s hs =>
              hval ▸ mem_of_mem_nhds hs)
          exact (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
            hh₀_diff_punct hcont).differentiableAt
      have hh₀_ne : ∀ z, h₀ z ≠ 0 := by
        intro z hz
        have hf₁z : f₁ z = 0 := by rw [hh₀_eq z, hz, zero_mul]
        obtain ⟨n, rfl⟩ := ha_covers z hf₁z
        have han : a n ≠ 0 := fun h => hf₁_nz (h ▸ hf₁z)
        -- All functions are entire and not identically zero
        have hf₁_ne : ¬ f₁ = 0 := fun h => hf₁_nz (congr_fun h 0)
        have hh₀_ne_fun : ¬ h₀ = 0 := by
          intro h; apply hf₁_ne; ext z; simp [hh₀_eq z, show h₀ z = 0 from congr_fun h z]
        have hP_ne_fun : ¬ P = 0 := by
          intro hP_eq
          have hP0 : P 0 = 0 := congr_fun hP_eq 0
          have : (fun n => weierstraßElementary p (0 / a n)) = fun _ => (1 : ℂ) :=
            funext fun n => by rw [zero_div, weierstraßElementary_zero]
          simp only [P, this, tprod_one] at hP0 -- hP0 : 1 = 0
          exact one_ne_zero hP0
        -- Orders are finite (not ⊤) since functions are analytic and not identically zero
        have hf₁_top : analyticOrderAt f₁ (a n) ≠ ⊤ :=
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a n)
            (fun z => hf₁_diff.analyticAt z)).not.mpr hf₁_ne
        have hh₀_top : analyticOrderAt h₀ (a n) ≠ ⊤ :=
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a n)
            (fun z => hh₀_diff.analyticAt z)).not.mpr hh₀_ne_fun
        have hP_top : analyticOrderAt P (a n) ≠ ⊤ :=
          (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (a n)
            (fun z => hP_diff.analyticAt z)).not.mpr hP_ne_fun
        -- f₁ = h₀ * P ⟹ order(f₁) = order(h₀) + order(P) in ℕ
        have hord_eq : analyticOrderNatAt f₁ (a n) =
            analyticOrderNatAt h₀ (a n) + analyticOrderNatAt P (a n) := by
          have hfun_eq : f₁ = h₀ * P :=
            funext fun z => by rw [hh₀_eq z, Pi.mul_apply]
          conv_lhs => rw [hfun_eq]
          exact analyticOrderNatAt_mul (hh₀_diff.analyticAt _) (hP_diff.analyticAt _)
            hh₀_top hP_top
        -- h₀(a n) = 0 ⟹ order(h₀, a n) ≥ 1
        have hh₀_pos : 1 ≤ analyticOrderNatAt h₀ (a n) := by
          rw [Nat.one_le_iff_ne_zero, Ne, analyticOrderNatAt,
            ENat.toNat_eq_zero, not_or]
          exact ⟨analyticOrderAt_ne_zero.mpr ⟨hh₀_diff.analyticAt _, hz⟩, hh₀_top⟩
        -- From multiplicity-aware enumeration: order(P, a n) = order(f₁, a n)
        have hP_ge : analyticOrderNatAt f₁ (a n) ≤ analyticOrderNatAt P (a n) := by
          have h := ha_ord_eq (a n) hf₁z han
          -- h : analyticOrderAt f₁ (a n) = analyticOrderAt P (a n)
          simp only [analyticOrderNatAt]
          exact ENat.toNat_le_toNat h.le hP_top
        -- Contradiction: f₁_ord = h₀_ord + P_ord ≥ 1 + f₁_ord, impossible in ℕ
        omega
      exact ⟨h₀, hh₀_diff, hh₀_ne, hh₀_eq⟩
    -- ═══════════════════════════════════════════════════════════
    -- Step 5: entire_logarithm + assembly
    -- ═══════════════════════════════════════════════════════════
    obtain ⟨g, hg_diff, hg_eq⟩ := entire_logarithm h hh_diff hh_ne
    exact ⟨m, g, a, p, hg_diff,
      fun n hn => by rw [hf_eq (a n), ha_zeros n hn, mul_zero],
      hconv, fun z => by
        rw [hf_eq z, hh_eq z, hg_eq z, ← mul_assoc]⟩
    -/

end ArithmeticHodge.Analysis.EntireFunction
