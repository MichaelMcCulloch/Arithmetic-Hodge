/-
  Complex Stirling Approximation for Γ(s)

  Provides:
  1. complex_stirling_bound: log|Γ(σ+it)| = (σ-1/2)·log|t| - π|t|/2 + O(log|t|)
  2. digamma_growth_bound: ‖ψ(s)‖ ≤ C·log|t| in vertical strips

  Strategy: Define f(s) = -γ + Σ(1/(n+1) - 1/(s+n)), show |f| ≤ C·log|t|,
  show ψ = f via Liouville argument (h = ψ - f is entire periodic, h/sin bounded,
  Liouville + anti-periodicity → h = 0).
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.NumberTheory.Harmonic.Bounds

open Complex Real Filter Topology MeasureTheory Set Finset
open scoped NNReal ComplexConjugate

noncomputable section

namespace ArithmeticHodge.Analysis

/-! ## Auxiliary estimates -/

/-- For |t| ≥ 2, log|t| ≥ log 2 > 0. -/
private lemma log_abs_im_pos {t : ℝ} (ht : 2 ≤ |t|) : 0 < Real.log |t| :=
  Real.log_pos (by linarith)

/-- Bound: 1/(n+1) - 1/(s+n) = (s-1)/((n+1)·(s+n)). -/
private lemma series_term_eq (s : ℂ) (n : ℕ) (hs : s + ↑n ≠ 0) :
    (1 : ℂ) / (↑n + 1) - 1 / (s + ↑n) =
    (s - 1) / ((↑n + 1) * (s + ↑n)) := by
  have h1 : (↑n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp; ring

/-- The series terms are O(1/n²) for n large relative to |s|. -/
private lemma series_term_bound (s : ℂ) (n : ℕ) (hn : (n : ℝ) ≥ 2 * ‖s‖ + 2) :
    ‖(1 : ℂ) / (↑n + 1) - 1 / (s + ↑n)‖ ≤
    2 * (‖s‖ + 1) / (↑n : ℝ) ^ 2 := by
  have hn_pos : (0 : ℝ) < n := by
    by_contra h; push_neg at h
    have : (n : ℝ) ≤ 0 := h
    linarith [norm_nonneg s]
  have hn_cast_pos : (0 : ℝ) < (n : ℝ) := hn_pos
  -- Reverse triangle: ‖s + n‖ ≥ n - ‖s‖ ≥ n/2
  have h_sn : (n : ℝ) / 2 ≤ ‖s + ↑n‖ := by
    have h1 : ‖(↑n : ℂ)‖ ≤ ‖s + ↑n‖ + ‖s‖ := by
      calc ‖(↑n : ℂ)‖ = ‖(s + ↑n) + (-s)‖ := by ring_nf
        _ ≤ ‖s + ↑n‖ + ‖-s‖ := norm_add_le _ _
        _ = ‖s + ↑n‖ + ‖s‖ := by rw [norm_neg]
    have h2 : ‖(↑n : ℂ)‖ = (n : ℝ) := by
      simp
    linarith
  have h_sn_ne : s + ↑n ≠ 0 := by
    intro h; rw [h, norm_zero] at h_sn; linarith
  rw [series_term_eq s n h_sn_ne, norm_div, norm_mul]
  -- ‖n + 1‖ ≥ n
  have h_n1 : (n : ℝ) ≤ ‖(↑n : ℂ) + 1‖ := by
    have : (↑n : ℂ) + 1 = ↑(n + 1 : ℕ) := by push_cast; ring
    rw [this, Complex.norm_natCast]
    exact_mod_cast Nat.le_succ n
  -- ‖(n+1) · (s+n)‖ ≥ n²/2
  have h_denom : (n : ℝ) ^ 2 / 2 ≤ ‖(↑n + 1 : ℂ)‖ * ‖s + ↑n‖ := by
    calc (n : ℝ) ^ 2 / 2 = n * (n / 2) := by ring
      _ ≤ ‖(↑n : ℂ) + 1‖ * ‖s + ↑n‖ :=
        mul_le_mul h_n1 h_sn (by positivity) (by positivity)
  -- ‖s - 1‖ ≤ ‖s‖ + 1
  have h_num : ‖s - 1‖ ≤ ‖s‖ + 1 := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le s 1
      _ = ‖s‖ + 1 := by simp
  -- Combine
  have h_denom_pos : 0 < (n : ℝ) ^ 2 / 2 := by positivity
  have h_prod_pos : 0 < ‖(↑n + 1 : ℂ)‖ * ‖s + ↑n‖ :=
    mul_pos (lt_of_lt_of_le hn_pos h_n1) (lt_of_lt_of_le (half_pos hn_pos) h_sn)
  calc ‖s - 1‖ / (‖(↑n : ℂ) + 1‖ * ‖s + ↑n‖)
      ≤ (‖s‖ + 1) / (‖(↑n : ℂ) + 1‖ * ‖s + ↑n‖) := by
        apply div_le_div_of_nonneg_right h_num (le_of_lt h_prod_pos)
    _ ≤ (‖s‖ + 1) / ((n : ℝ) ^ 2 / 2) := by
        apply div_le_div_of_nonneg_left _ h_denom_pos h_denom
        linarith [norm_nonneg s]
    _ = 2 * (‖s‖ + 1) / (n : ℝ) ^ 2 := by ring

/-! ### Euler's product and the digamma partial-fraction series -/

/-- The nontrivial part of the `n`-th Weierstrass factor for `1 / Γ`. -/
private noncomputable def gammaWeierstrassTerm (n : ℕ) (z : ℂ) : ℂ :=
  (1 + z / (n + 1)) * Complex.exp (-z / (n + 1)) - 1

/-- A quadratic bound for a Weierstrass factor, uniform on compact sets after division by
`(n + 1)²`. -/
private lemma norm_gammaWeierstrassTerm_le (n : ℕ) (z : ℂ) :
    ‖gammaWeierstrassTerm n z‖ ≤
      2 * ‖z / (n + 1 : ℂ)‖ ^ 2 * Real.exp ‖z / (n + 1 : ℂ)‖ := by
  set x : ℂ := z / (n + 1) with hx
  have h₁ := Complex.norm_exp_sub_sum_le_norm_mul_exp (-x) 2
  have h₂ := Complex.norm_exp_sub_sum_le_norm_mul_exp (-x) 1
  have h₁' : ‖Complex.exp (-x) - 1 + x‖ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖ := by
    convert h₁ using 1 <;> simp [Finset.sum_range_succ_comm, Nat.factorial] <;> ring
  have h₂' : ‖Complex.exp (-x) - 1‖ ≤ ‖x‖ * Real.exp ‖x‖ := by
    simpa using h₂
  rw [gammaWeierstrassTerm, neg_div, ← hx]
  rw [show (1 + x) * Complex.exp (-x) - 1 =
      (Complex.exp (-x) - 1 + x) + x * (Complex.exp (-x) - 1) by ring]
  calc
    ‖(Complex.exp (-x) - 1 + x) + x * (Complex.exp (-x) - 1)‖
        ≤ ‖Complex.exp (-x) - 1 + x‖ + ‖x * (Complex.exp (-x) - 1)‖ :=
          norm_add_le _ _
    _ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖ + ‖x‖ * (‖x‖ * Real.exp ‖x‖) := by
      rw [norm_mul]
      gcongr
    _ = 2 * ‖z / (n + 1 : ℂ)‖ ^ 2 * Real.exp ‖z / (n + 1 : ℂ)‖ := by
      rw [hx]
      ring

private lemma gammaWeierstrassTerm_bound_on_compact {K : Set ℂ} (hK : IsCompact K) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n z, z ∈ K → ‖gammaWeierstrassTerm n z‖ ≤ u n := by
  have hcont : ContinuousOn (fun z : ℂ => 2 * ‖z‖ ^ 2 * Real.exp ‖z‖) K := by
    fun_prop
  obtain ⟨M, hM⟩ := bddAbove_def.mp (IsCompact.bddAbove_image hK hcont)
  refine ⟨fun n : ℕ => ‖(M : ℂ) / (n + 1) ^ 2‖, ?_, ?_⟩
  · simpa using summable_pow_div_add (M : ℂ) 2 1 Nat.one_lt_two
  · intro n z hz
    have hn_pos : (0 : ℝ) < n + 1 := by positivity
    have hcast : ((n : ℂ) + 1) = ((n : ℝ) + 1 : ℝ) := by push_cast; rfl
    have hdennorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn_pos]
    have hnorm_div : ‖z / (n + 1 : ℂ)‖ = ‖z‖ / (n + 1 : ℝ) := by
      rw [norm_div, hdennorm]
    have hdiv_le : ‖z‖ / (n + 1 : ℝ) ≤ ‖z‖ := by
      apply div_le_self (norm_nonneg z)
      exact_mod_cast Nat.le_add_left 1 n
    have hexp_le : Real.exp (‖z‖ / (n + 1 : ℝ)) ≤ Real.exp ‖z‖ :=
      Real.exp_le_exp_of_le hdiv_le
    have hpoly : 2 * ‖z / (n + 1 : ℂ)‖ ^ 2 *
        Real.exp ‖z / (n + 1 : ℂ)‖ ≤
        (2 * ‖z‖ ^ 2 * Real.exp ‖z‖) / (n + 1 : ℝ) ^ 2 := by
      rw [hnorm_div]
      have hden : 0 < (n + 1 : ℝ) ^ 2 := by positivity
      calc
        2 * (‖z‖ / (n + 1 : ℝ)) ^ 2 * Real.exp (‖z‖ / (n + 1 : ℝ))
            ≤ 2 * (‖z‖ / (n + 1 : ℝ)) ^ 2 * Real.exp ‖z‖ := by
              gcongr
        _ = (2 * ‖z‖ ^ 2 * Real.exp ‖z‖) / (n + 1 : ℝ) ^ 2 := by
              field_simp
    calc
      ‖gammaWeierstrassTerm n z‖
          ≤ 2 * ‖z / (n + 1 : ℂ)‖ ^ 2 * Real.exp ‖z / (n + 1 : ℂ)‖ :=
            norm_gammaWeierstrassTerm_le n z
      _ ≤ (2 * ‖z‖ ^ 2 * Real.exp ‖z‖) / (n + 1 : ℝ) ^ 2 := hpoly
      _ ≤ |M| / (n + 1 : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact (hM _ ⟨z, hz, rfl⟩).trans (le_abs_self M)
      _ = ‖(M : ℂ) / (n + 1) ^ 2‖ := by
        rw [norm_div, norm_pow, hdennorm]
        simp

private lemma multipliableUniformlyOn_gammaWeierstrass {K : Set ℂ} (hK : IsCompact K) :
    MultipliableUniformlyOn
      (fun n : ℕ => fun z : ℂ => 1 + gammaWeierstrassTerm n z) K := by
  obtain ⟨u, hu, hub⟩ := gammaWeierstrassTerm_bound_on_compact hK
  refine Summable.multipliableUniformlyOn_nat_one_add hK hu ?_ ?_
  · filter_upwards with n z hz using hub n z hz
  · intro n
    apply Continuous.continuousOn
    unfold gammaWeierstrassTerm
    fun_prop

private lemma hasProdLocallyUniformlyOn_gammaWeierstrass :
    HasProdLocallyUniformlyOn
      (fun n : ℕ => fun z : ℂ => 1 + gammaWeierstrassTerm n z)
      (fun z => ∏' n : ℕ, (1 + gammaWeierstrassTerm n z)) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  exact (multipliableUniformlyOn_gammaWeierstrass hK).hasProdUniformlyOn

private lemma gammaWeierstrass_partial_product_eq (z : ℂ) {n : ℕ} (hn : n ≠ 0) :
    z * Complex.exp (((harmonic n : ℝ) - Real.log n) * z) *
        (∏ k ∈ Finset.range n, (1 + gammaWeierstrassTerm k z)) =
      (Complex.GammaSeq z n)⁻¹ := by
  rw [Complex.GammaSeq, inv_div]
  have hfactor (k : ℕ) : 1 + gammaWeierstrassTerm k z =
      (1 + z / (k + 1 : ℂ)) * Complex.exp (-z / (k + 1 : ℂ)) := by
    unfold gammaWeierstrassTerm
    ring
  simp_rw [hfactor, Finset.prod_mul_distrib]
  rw [← Complex.exp_sum]
  have hharm : (∑ k ∈ Finset.range n, -z / (k + 1 : ℂ)) = -(harmonic n : ℂ) * z := by
    rw [harmonic]
    push_cast
    simp only [div_eq_mul_inv]
    rw [← Finset.mul_sum]
    ring
  rw [hharm]
  rw [show z * Complex.exp (((harmonic n : ℝ) - Real.log n) * z) *
        ((∏ k ∈ Finset.range n, (1 + z / (k + 1 : ℂ))) *
          Complex.exp (-(harmonic n : ℂ) * z)) =
      z * (Complex.exp (((harmonic n : ℝ) - Real.log n) * z) *
          Complex.exp (-(harmonic n : ℂ) * z)) *
        (∏ k ∈ Finset.range n, (1 + z / (k + 1 : ℂ))) by ring,
    ← Complex.exp_add]
  have hpow : Complex.exp (-(Real.log n : ℂ) * z) = ((n : ℂ) ^ z)⁻¹ := by
    rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
    have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
      change Complex.log ((n : ℝ) : ℂ) = (Real.log (n : ℝ) : ℂ)
      exact (Complex.ofReal_log (Nat.cast_nonneg n)).symm
    rw [hlog]
    rw [← Complex.exp_neg]
    congr 1
    ring
  rw [show (((harmonic n : ℝ) - Real.log n : ℂ) * z + -(harmonic n : ℂ) * z) =
      -(Real.log n : ℂ) * z by push_cast; ring, hpow]
  rw [show (∏ k ∈ Finset.range n, (1 + z / (k + 1 : ℂ))) =
      (∏ k ∈ Finset.range n, (z + (k + 1 : ℂ))) / (Nat.factorial n : ℂ) by
    have hone (k : ℕ) : 1 + z / (k + 1 : ℂ) =
        (z + (k + 1 : ℂ)) / (k + 1 : ℂ) := by
      field_simp
      ring
    simp_rw [hone, Finset.prod_div_distrib]
    congr 1
    norm_cast
    exact Finset.prod_range_add_one_eq_factorial n]
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero]
  push_cast
  field_simp

private lemma gamma_inv_eq_weierstrass (z : ℂ) (hz : 0 < z.re) :
    (Complex.Gamma z)⁻¹ =
      z * Complex.exp (Real.eulerMascheroniConstant * z) *
        ∏' n : ℕ, (1 + gammaWeierstrassTerm n z) := by
  let A : ℕ → ℂ := fun n =>
    z * Complex.exp (((harmonic n : ℝ) - Real.log n) * z) *
      ∏ k ∈ Finset.range n, (1 + gammaWeierstrassTerm k z)
  have hcoeff : Tendsto
      (fun n : ℕ => (((harmonic n : ℝ) - Real.log n : ℝ) : ℂ)) atTop
      (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
    Complex.continuous_ofReal.tendsto _ |>.comp Real.tendsto_harmonic_sub_log
  have hexp : Tendsto
      (fun n : ℕ => Complex.exp ((((harmonic n : ℝ) - Real.log n : ℝ) : ℂ) * z)) atTop
      (𝓝 (Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z))) :=
    (hcoeff.mul_const z).cexp
  have hprod : Tendsto
      (fun n : ℕ => ∏ k ∈ Finset.range n, (1 + gammaWeierstrassTerm k z)) atTop
      (𝓝 (∏' n : ℕ, (1 + gammaWeierstrassTerm n z))) :=
    (hasProdLocallyUniformlyOn_gammaWeierstrass.hasProd (Set.mem_univ z)).tendsto_prod_nat
  have hAprod : Tendsto A atTop
      (𝓝 (z * Complex.exp (Real.eulerMascheroniConstant * z) *
        ∏' n : ℕ, (1 + gammaWeierstrassTerm n z))) := by
    simpa [A] using
      (((tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z)).mul hexp).mul hprod)
  have hpole : ∀ m : ℕ, z ≠ -↑m := by
    intro m hm
    have hre := congr_arg Complex.re hm
    simp only [neg_re, natCast_re] at hre
    linarith
  have hAinv : Tendsto A atTop (𝓝 (Complex.Gamma z)⁻¹) := by
    apply (Complex.GammaSeq_tendsto_Gamma z).inv₀ (Complex.Gamma_ne_zero hpole) |>.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (gammaWeierstrass_partial_product_eq z hn).symm
  exact tendsto_nhds_unique hAinv hAprod

private lemma norm_digammaSeriesTerm_le (s : ℂ) (hs : 1 ≤ s.re) (n : ℕ) :
    ‖(1 : ℂ) / (s + (↑(n + 1 : ℕ) : ℂ)) - 1 / (↑(n + 1 : ℕ) : ℂ)‖ ≤
      ‖s‖ / (n + 1 : ℝ) ^ 2 := by
  have hkpos : (0 : ℝ) < n + 1 := by positivity
  have hk : (↑(n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hsk : s + (↑(n + 1 : ℕ) : ℂ) ≠ 0 := by
    intro h
    have hre := congr_arg Complex.re h
    simp at hre
    linarith
  have hknorm : ‖(↑(n + 1 : ℕ) : ℂ)‖ = (n + 1 : ℝ) := by
    rw [Complex.norm_natCast]
    norm_cast
  have hsknorm : (n + 1 : ℝ) ≤ ‖s + (↑(n + 1 : ℕ) : ℂ)‖ := by
    calc
      (n + 1 : ℝ) ≤ (s + (↑(n + 1 : ℕ) : ℂ)).re := by simp; linarith
      _ ≤ |(s + (↑(n + 1 : ℕ) : ℂ)).re| := le_abs_self _
      _ ≤ ‖s + (↑(n + 1 : ℕ) : ℂ)‖ := Complex.abs_re_le_norm _
  rw [show (1 : ℂ) / (s + (↑(n + 1 : ℕ) : ℂ)) - 1 / (↑(n + 1 : ℕ) : ℂ) =
      -s / ((↑(n + 1 : ℕ) : ℂ) * (s + (↑(n + 1 : ℕ) : ℂ))) by
        field_simp [hk, hsk]
        ring,
    norm_div, norm_neg, norm_mul, hknorm]
  have hden : (n + 1 : ℝ) ^ 2 ≤
      (n + 1 : ℝ) * ‖s + (↑(n + 1 : ℕ) : ℂ)‖ := by
    rw [pow_two]
    gcongr
  exact div_le_div_of_nonneg_left (norm_nonneg s) (sq_pos_of_pos hkpos) hden

private lemma summable_digammaSeriesTerm (s : ℂ) (hs : 1 ≤ s.re) :
    Summable (fun n : ℕ =>
      (1 : ℂ) / (s + (↑(n + 1 : ℕ) : ℂ)) - 1 / (↑(n + 1 : ℕ) : ℂ)) := by
  have hmajorant : Summable (fun n : ℕ => ‖s‖ / (n + 1 : ℝ) ^ 2) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (summable_pow_div_add (‖s‖ : ℝ) 2 1 Nat.one_lt_two)
  exact hmajorant.of_norm_bounded (norm_digammaSeriesTerm_le s hs)

private lemma logDeriv_gammaWeierstrassFactor (s : ℂ) (n : ℕ)
    (hs : s ≠ -(↑(n + 1 : ℕ) : ℂ)) :
    logDeriv (fun z : ℂ => 1 + gammaWeierstrassTerm n z) s =
      1 / (s + (↑(n + 1 : ℕ) : ℂ)) - 1 / (↑(n + 1 : ℕ) : ℂ) := by
  have hk : (↑(n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hsk : s + (↑(n + 1 : ℕ) : ℂ) ≠ 0 := by
    simpa [add_eq_zero_iff_eq_neg] using hs
  push_cast at hs hk hsk ⊢
  have hsk' : (n : ℂ) + 1 + s ≠ 0 := by
    intro h
    apply hsk
    linear_combination h
  have h₁ : HasDerivAt (fun z : ℂ => 1 + z / (n + 1 : ℂ))
      (1 / (n + 1 : ℂ)) s := by
    simpa only [Pi.add_apply, Pi.one_apply, id_eq, zero_add] using
      (hasDerivAt_const s (1 : ℂ)).add
        ((hasDerivAt_id s).div_const (n + 1 : ℂ))
  have h₂ : HasDerivAt (fun z : ℂ => Complex.exp (-z / (n + 1 : ℂ)))
      (Complex.exp (-s / (n + 1 : ℂ)) * (-1 / (n + 1 : ℂ))) s := by
    simpa only [Pi.neg_apply, id_eq, neg_div, one_div, neg_mul] using
      ((hasDerivAt_id s).neg.div_const (n + 1 : ℂ)).cexp
  have hmul : HasDerivAt
      (fun z : ℂ => (1 + z / (n + 1 : ℂ)) * Complex.exp (-z / (n + 1 : ℂ)))
      ((1 / (n + 1 : ℂ)) * Complex.exp (-s / (n + 1 : ℂ)) +
        (1 + s / (n + 1 : ℂ)) *
          (Complex.exp (-s / (n + 1 : ℂ)) * (-1 / (n + 1 : ℂ)))) s := by
    simpa only [Pi.mul_apply] using h₁.mul h₂
  have hfun : (fun z : ℂ => 1 + gammaWeierstrassTerm n z) =
      fun z : ℂ => (1 + z / (n + 1 : ℂ)) * Complex.exp (-z / (n + 1 : ℂ)) := by
    funext z
    unfold gammaWeierstrassTerm
    ring
  rw [hfun, logDeriv_apply, hmul.deriv]
  field_simp [hk, hsk, hsk', Complex.exp_ne_zero]
  ring

private lemma digamma_series (s : ℂ) (hs : 1 ≤ s.re) :
    Complex.digamma s =
      -(1 / s + Real.eulerMascheroniConstant +
        ∑' n : ℕ,
          ((1 : ℂ) / (s + (↑(n + 1 : ℕ) : ℂ)) - 1 / (↑(n + 1 : ℕ) : ℂ))) := by
  let P : ℂ → ℂ := fun z => ∏' n : ℕ, (1 + gammaWeierstrassTerm n z)
  let E : ℂ → ℂ := fun z => Complex.exp (Real.eulerMascheroniConstant * z)
  have hspos : 0 < s.re := lt_of_lt_of_le zero_lt_one hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, zero_re] at hs
    linarith
  have hpole : ∀ m : ℕ, s ≠ -↑m := by
    intro m h
    have hre := congr_arg Complex.re h
    simp only [neg_re, natCast_re] at hre
    linarith
  have hGamma : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hpole
  have hfactor_ne : ∀ n : ℕ, 1 + gammaWeierstrassTerm n s ≠ 0 := by
    intro n
    have hk : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hlin : 1 + s / (n + 1 : ℂ) ≠ 0 := by
      intro h
      apply hpole (n + 1)
      field_simp [hk] at h
      push_cast
      linear_combination h
    unfold gammaWeierstrassTerm
    rw [show 1 + ((1 + s / (n + 1 : ℂ)) * Complex.exp (-s / (n + 1 : ℂ)) - 1) =
      (1 + s / (n + 1 : ℂ)) * Complex.exp (-s / (n + 1 : ℂ)) by ring]
    exact mul_ne_zero hlin (Complex.exp_ne_zero _)
  have hP_ne : P s ≠ 0 := by
    have hinv : (Complex.Gamma s)⁻¹ ≠ 0 := inv_ne_zero hGamma
    rw [gamma_inv_eq_weierstrass s hspos] at hinv
    simpa [P, E, hs0, Complex.exp_ne_zero] using hinv
  have hP_diff : DifferentiableAt ℂ P s := by
    apply (hasProdLocallyUniformlyOn_gammaWeierstrass.tendstoLocallyUniformlyOn_finsetRange
      |>.differentiableOn ?_ isOpen_univ).differentiableAt
    · exact isOpen_univ.mem_nhds (Set.mem_univ s)
    · filter_upwards with N
      apply Differentiable.differentiableOn
      simp only [gammaWeierstrassTerm]
      fun_prop
  have hsum := summable_digammaSeriesTerm s hs
  have hlogsum : Summable
      (fun n : ℕ => logDeriv (fun z : ℂ => 1 + gammaWeierstrassTerm n z) s) :=
    hsum.congr (fun n => (logDeriv_gammaWeierstrassFactor s n (hpole (n + 1))).symm)
  have hP_logDeriv : logDeriv P s =
      ∑' n : ℕ,
        ((1 : ℂ) / (s + (↑(n + 1 : ℕ) : ℂ)) - 1 / (↑(n + 1 : ℕ) : ℂ)) := by
    have h := logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ s) hfactor_ne
      (fun n => by
        unfold gammaWeierstrassTerm
        fun_prop)
      hlogsum
      hasProdLocallyUniformlyOn_gammaWeierstrass.multipliableLocallyUniformlyOn hP_ne
    change logDeriv (fun z => ∏' n : ℕ, (1 + gammaWeierstrassTerm n z)) s = _
    rw [h]
    apply tsum_congr
    intro n
    exact logDeriv_gammaWeierstrassFactor s n (hpole (n + 1))
  have hfun_eq : (fun z : ℂ => (Complex.Gamma z)⁻¹) =ᶠ[𝓝 s]
      (fun z : ℂ => z * E z * P z) := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually (Ioi_mem_nhds hspos)] with z hz
    simpa [E, P] using gamma_inv_eq_weierstrass z hz
  have hlogDeriv_eq : logDeriv (fun z : ℂ => (Complex.Gamma z)⁻¹) s =
      logDeriv (fun z : ℂ => z * E z * P z) s := by
    have hval : (Complex.Gamma s)⁻¹ = s * E s * P s := hfun_eq.self_of_nhds
    simp only [logDeriv_apply]
    rw [hfun_eq.deriv_eq, hval]
  have hGamma_diff : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s hpole
  have hinv_logDeriv : logDeriv (fun z : ℂ => (Complex.Gamma z)⁻¹) s =
      -Complex.digamma s := by
    have hcomp := logDeriv_comp (x := s) (f := fun z : ℂ => z⁻¹) (g := Complex.Gamma)
      (differentiableAt_inv hGamma) hGamma_diff
    change logDeriv (fun z : ℂ => (Complex.Gamma z)⁻¹) s = _ at hcomp
    rw [hcomp, logDeriv_inv, Complex.digamma_def, logDeriv_apply]
    ring
  have hE_ne : E s ≠ 0 := Complex.exp_ne_zero _
  have hE_diff : DifferentiableAt ℂ E s := by
    dsimp [E]
    fun_prop
  have hE_logDeriv : logDeriv E s = Real.eulerMascheroniConstant := by
    have hderiv : HasDerivAt E
        (Complex.exp (Real.eulerMascheroniConstant * s) * Real.eulerMascheroniConstant) s := by
      simpa only [E, id_eq, mul_one] using
        ((hasDerivAt_id s).const_mul (Real.eulerMascheroniConstant : ℂ)).cexp
    rw [logDeriv_apply, hderiv.deriv]
    dsimp [E]
    field_simp [Complex.exp_ne_zero]
  have hinner : logDeriv (fun z : ℂ => z * E z) s =
      1 / s + Real.eulerMascheroniConstant := by
    have h := logDeriv_mul (x := s) (f := fun z : ℂ => z) (g := E)
      hs0 hE_ne (by fun_prop) hE_diff
    simpa only [Pi.mul_apply, logDeriv_id', hE_logDeriv] using h
  have houter : logDeriv (fun z : ℂ => z * E z * P z) s =
      1 / s + Real.eulerMascheroniConstant +
        ∑' n : ℕ,
          ((1 : ℂ) / (s + (↑(n + 1 : ℕ) : ℂ)) - 1 / (↑(n + 1 : ℕ) : ℂ)) := by
    have hinner_diff : DifferentiableAt ℂ (fun z : ℂ => z * E z) s :=
      (show DifferentiableAt ℂ (fun z : ℂ => z) s by fun_prop).mul hE_diff
    have h := logDeriv_mul (x := s) (f := fun z : ℂ => z * E z) (g := P)
      (mul_ne_zero hs0 hE_ne) hP_ne hinner_diff hP_diff
    simpa only [Pi.mul_apply, hinner, hP_logDeriv] using h
  rw [hinv_logDeriv, houter] at hlogDeriv_eq
  linear_combination -hlogDeriv_eq

private lemma norm_digammaSeriesTerm_le_harmonic (s : ℂ) (n : ℕ)
    (him : 1 ≤ |s.im|) :
    ‖(1 : ℂ) / (s + (↑(n + 1 : ℕ) : ℂ)) - 1 / (↑(n + 1 : ℕ) : ℂ)‖ ≤
      |s.im|⁻¹ + (n + 1 : ℝ)⁻¹ := by
  have himpos : 0 < |s.im| := by linarith
  have hden : |s.im| ≤ ‖s + (↑(n + 1 : ℕ) : ℂ)‖ := by
    calc
      |s.im| = |(s + (↑(n + 1 : ℕ) : ℂ)).im| := by simp
      _ ≤ ‖s + (↑(n + 1 : ℕ) : ℂ)‖ := Complex.abs_im_le_norm _
  calc
    ‖(1 : ℂ) / (s + (↑(n + 1 : ℕ) : ℂ)) - 1 / (↑(n + 1 : ℕ) : ℂ)‖
        ≤ ‖(1 : ℂ) / (s + (↑(n + 1 : ℕ) : ℂ))‖ +
          ‖(1 : ℂ) / (↑(n + 1 : ℕ) : ℂ)‖ := norm_sub_le _ _
    _ = ‖s + (↑(n + 1 : ℕ) : ℂ)‖⁻¹ + (n + 1 : ℝ)⁻¹ := by
      rw [one_div, one_div, norm_inv, norm_inv, Complex.norm_natCast]
      norm_cast
    _ ≤ |s.im|⁻¹ + (n + 1 : ℝ)⁻¹ := by
      gcongr

private lemma tsum_inv_sq_nat_add_le (N : ℕ) :
    ∑' j : ℕ, (((N + j + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 / (N + 1 : ℝ) := by
  apply Real.tsum_le_of_sum_range_le
  · intro j
    positivity
  · intro m
    calc
      (∑ j ∈ Finset.range m, (((N + j + 1 : ℕ) : ℝ) ^ 2)⁻¹) =
          ∑ i ∈ Finset.Ioo N (N + m + 1), ((i : ℝ) ^ 2)⁻¹ := by
        rw [show Finset.Ioo N (N + m + 1) = Finset.Ico (N + 1) (N + m + 1) by
          ext i
          simp]
        rw [Finset.sum_Ico_eq_sum_range]
        have hsub : N + m + 1 - (N + 1) = m := by omega
        rw [hsub]
        apply Finset.sum_congr rfl
        intro j _
        congr 3
        omega
      _ ≤ 2 / (N + 1 : ℝ) := sum_Ioo_inv_sq_le N (N + m + 1)

/-! ## Derivative of log ‖Γ‖ and functional equation -/

/-- Differentiability of σ ↦ Γ(σ + it) from ℝ to ℂ. -/
private lemma hasDerivAt_Gamma_ofReal (σ : ℝ) (t : ℝ)
    (hs : ∀ m : ℕ, (↑σ + ↑t * I : ℂ) ≠ -↑m) :
    HasDerivAt (fun σ' : ℝ => Complex.Gamma (↑σ' + ↑t * I))
      (deriv Complex.Gamma (↑σ + ↑t * I)) σ := by
  have hd : DifferentiableAt ℂ Complex.Gamma (↑σ + ↑t * I) :=
    Complex.differentiableAt_Gamma _ hs
  have hlin : HasDerivAt (fun σ' : ℝ => (↑σ' + ↑t * I : ℂ)) 1 σ := by
    convert (Complex.ofRealCLM.hasDerivAt).add (hasDerivAt_const σ (↑t * I : ℂ)) using 1
    simp
  have hcomp := HasDerivAt.comp σ (hd.hasDerivAt) hlin
  simp at hcomp; exact hcomp

/-- The function σ ↦ Real.log ‖Γ(σ + it)‖ has derivative Re(ψ(σ + it)).
    Key tool for the MVT approach to Stirling/digamma bounds. -/
private lemma hasDerivAt_log_norm_Gamma (σ : ℝ) (t : ℝ) (_ht : t ≠ 0)
    (hs : ∀ m : ℕ, (↑σ + ↑t * I : ℂ) ≠ -↑m) :
    HasDerivAt (fun σ' : ℝ => Real.log ‖Complex.Gamma (↑σ' + ↑t * I)‖)
      (Complex.digamma (↑σ + ↑t * I)).re σ := by
  set s := (↑σ + ↑t * I : ℂ) with hs_def
  have hΓ_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have hψ_eq : Complex.digamma s = deriv Complex.Gamma s / Complex.Gamma s := rfl
  obtain h_slit | h_slit := Complex.mem_slitPlane_or_neg_mem_slitPlane hΓ_ne
  · -- Case 1: Γ(s) ∈ slitPlane
    have hlog_deriv : HasDerivAt (fun w : ℂ => Complex.log (Complex.Gamma (w + ↑t * I)))
        (Complex.digamma s) (↑σ) := by
      have hlin : HasDerivAt (fun w : ℂ => w + ↑t * I) 1 (↑σ : ℂ) := by
        have h1 := hasDerivAt_id (↑σ : ℂ)
        have h2 := hasDerivAt_const (↑σ : ℂ) (↑t * I : ℂ)
        convert h1.add h2 using 1; simp
      have hΓ_at := (Complex.differentiableAt_Gamma s hs).hasDerivAt
      have hcomp : HasDerivAt (fun w => Complex.Gamma (w + ↑t * I))
          (deriv Complex.Gamma s) (↑σ) := by
        have h := hΓ_at.comp (↑σ : ℂ) hlin; simp only [mul_one] at h; exact h
      have hclog := hcomp.clog h_slit
      rwa [hψ_eq]
    have hre := hlog_deriv.real_of_complex
    simp only [Complex.log_re] at hre
    exact hre
  · -- Case 2: -Γ(s) ∈ slitPlane. Use log(-Γ) which has same Re.
    have hlog_deriv : HasDerivAt (fun w : ℂ => Complex.log (-Complex.Gamma (w + ↑t * I)))
        (Complex.digamma s) (↑σ) := by
      have hlin : HasDerivAt (fun w : ℂ => w + ↑t * I) 1 (↑σ : ℂ) := by
        have h1 := hasDerivAt_id (↑σ : ℂ)
        have h2 := hasDerivAt_const (↑σ : ℂ) (↑t * I : ℂ)
        convert h1.add h2 using 1; simp
      have hΓ_at := (Complex.differentiableAt_Gamma s hs).hasDerivAt
      have hcomp : HasDerivAt (fun w => Complex.Gamma (w + ↑t * I))
          (deriv Complex.Gamma s) (↑σ) := by
        have h := hΓ_at.comp (↑σ : ℂ) hlin; simp only [mul_one] at h; exact h
      have hneg : HasDerivAt (fun w => -Complex.Gamma (w + ↑t * I))
          (-deriv Complex.Gamma s) (↑σ) := by
        have h := hcomp.neg; simp at h; exact h
      have hclog := hneg.clog h_slit
      -- derivative is (-deriv Γ s) / (-Γ s) = deriv Γ s / Γ s = ψ(s)
      simp only [neg_div_neg_eq] at hclog
      rwa [hψ_eq]
    have hre := hlog_deriv.real_of_complex
    simp only [Complex.log_re, norm_neg] at hre
    exact hre

/-- Functional equation for log ‖Γ‖: from Γ(s+1) = s·Γ(s). -/
private lemma log_norm_Gamma_add_one (s : ℂ) (hs : ∀ m : ℕ, s ≠ -↑m) :
    Real.log ‖Complex.Gamma (s + 1)‖ = Real.log ‖s‖ + Real.log ‖Complex.Gamma s‖ := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  have hΓ_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  rw [Complex.Gamma_add_one s hs0, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hs0)
    (norm_ne_zero_iff.mpr hΓ_ne)]

/-- ContinuousOn for σ ↦ log ‖Γ(σ + it)‖ when t ≠ 0. -/
private lemma continuousOn_log_norm_Gamma (t : ℝ) (ht : t ≠ 0) (a b : ℝ) :
    ContinuousOn (fun σ : ℝ => Real.log ‖Complex.Gamma (↑σ + ↑t * I)‖) (Set.Icc a b) := by
  have hne : ∀ σ : ℝ, ∀ m : ℕ, (↑σ + ↑t * I : ℂ) ≠ -↑m := by
    intro σ m h; have := congr_arg Complex.im h; simp at this; exact ht this
  apply ContinuousOn.log
  · apply ContinuousOn.norm
    intro σ hσ
    show ContinuousWithinAt (fun σ' : ℝ => Complex.Gamma (↑σ' + ↑t * I)) (Set.Icc a b) σ
    change ContinuousWithinAt ((Complex.Gamma) ∘ (fun σ' : ℝ => (↑σ' + ↑t * I : ℂ))) _ σ
    exact ContinuousAt.comp_continuousWithinAt
      (Complex.differentiableAt_Gamma _ (hne σ)).continuousAt
      (by fun_prop : ContinuousWithinAt (fun σ' : ℝ => (↑σ' + ↑t * I : ℂ)) (Set.Icc a b) σ)
  · intro σ _
    exact norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (hne σ))

/-! ## Digamma recurrence and series infrastructure -/

/-- Iterated digamma recurrence: ψ(s) = ψ(s+N) - Σ_{k=0}^{N-1} (s+k)⁻¹.
    From iterating ψ(s+1) = ψ(s) + s⁻¹. -/
private lemma digamma_shift (s : ℂ) (N : ℕ)
    (hs : ∀ k : ℕ, k < N → ∀ m : ℕ, s + ↑k ≠ -↑m) :
    Complex.digamma s =
      Complex.digamma (s + ↑N) - ∑ k ∈ Finset.range N, (s + ↑k)⁻¹ := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hs_n : ∀ m : ℕ, s + ↑n ≠ -↑m := hs n (by omega)
    have ih' := ih (fun k hk => hs k (by omega))
    rw [ih', Finset.sum_range_succ]
    -- ψ(s+n) - Σ_{k<n} (s+k)⁻¹ = ψ(s+(n+1)) - Σ_{k<n} (s+k)⁻¹ - (s+n)⁻¹
    -- Using: ψ(s+n+1) = ψ(s+n) + (s+n)⁻¹
    have hrec := Complex.digamma_apply_add_one (s + ↑n) hs_n
    -- hrec: ψ(s + ↑n + 1) = ψ(s + ↑n) + (s + ↑n)⁻¹
    have hkey : Complex.digamma (s + ↑n) =
        Complex.digamma (s + ↑n + 1) - (s + ↑n)⁻¹ :=
      eq_sub_of_add_eq hrec.symm
    -- Cast: s + ↑(n+1) = s + ↑n + 1
    have : (↑(n + 1 : ℕ) : ℂ) = (↑n : ℂ) + 1 := by push_cast; ring
    rw [show (s + ↑(n + 1 : ℕ) : ℂ) = s + ↑n + 1 from by rw [this]; ring]
    linear_combination hkey

/-- Each term |(s+k)⁻¹| ≤ |Im s|⁻¹ when |Im s| ≥ 1. -/
private lemma inv_shift_bound (s : ℂ) (k : ℕ) (him : 1 ≤ |s.im|) :
    ‖(s + ↑k)⁻¹‖ ≤ |s.im|⁻¹ := by
  have him_pos : (0 : ℝ) < |s.im| := by linarith
  have hle : |s.im| ≤ ‖s + ↑k‖ :=
    calc |s.im| = |(s + ↑k).im| := by simp
      _ ≤ ‖s + ↑k‖ := Complex.abs_im_le_norm _
  rw [norm_inv]
  exact inv_anti₀ (by positivity) hle

/-- Sum bound: ‖Σ_{k=0}^{N-1} (s+k)⁻¹‖ ≤ N / |Im s|. -/
private lemma shift_sum_bound (s : ℂ) (N : ℕ) (him : 1 ≤ |s.im|) :
    ‖∑ k ∈ Finset.range N, (s + ↑k)⁻¹‖ ≤ ↑N / |s.im| := by
  calc ‖∑ k ∈ Finset.range N, (s + ↑k)⁻¹‖
      ≤ ∑ k ∈ Finset.range N, ‖(s + ↑k)⁻¹‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, |s.im|⁻¹ :=
        Finset.sum_le_sum (fun k _ => inv_shift_bound s k him)
    _ = ↑N * |s.im|⁻¹ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ↑N / |s.im| := by rw [div_eq_mul_inv]


/-- Bound on ‖ψ(s)‖ for Re(s) ≥ 1 and |Im s| ≥ 2.
    Uses shift to large real part + harmonic sum bound. -/
private lemma digamma_bound_re_ge_one (σ : ℝ) (t : ℝ) (hσ : 1 ≤ σ) (ht : 2 ≤ |t|) :
    ‖Complex.digamma (↑σ + ↑t * I)‖ ≤ (2 * σ + 10) * (Real.log |t| + 3) := by
  let s : ℂ := ↑σ + ↑t * I
  let a : ℕ → ℂ := fun n =>
    (1 : ℂ) / (s + (↑(n + 1 : ℕ) : ℂ)) - 1 / (↑(n + 1 : ℕ) : ℂ)
  let N : ℕ := ⌈|t|⌉₊
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hsre_one : 1 ≤ s.re := by simpa [hsre]
  have him : 1 ≤ |s.im| := by simpa [hsim] using ht.trans' (by norm_num)
  have htpos : 0 < |t| := by linarith
  have hN_ge : |t| ≤ (N : ℝ) := by
    exact Nat.le_ceil |t|
  have hN_lt : (N : ℝ) < |t| + 1 := by
    exact Nat.ceil_lt_add_one (abs_nonneg t)
  have hN_pos : 0 < N := by
    rw [Nat.ceil_pos]
    exact htpos
  have hN_div : (N : ℝ) * |t|⁻¹ ≤ 3 / 2 := by
    rw [← div_eq_mul_inv]
    calc
      (N : ℝ) / |t| ≤ (|t| + 1) / |t| :=
        div_le_div_of_nonneg_right hN_lt.le htpos.le
      _ = 1 + 1 / |t| := by field_simp
      _ ≤ 3 / 2 := by
        have hinv : 1 / |t| ≤ (1 : ℝ) / 2 :=
          one_div_le_one_div_of_le (by norm_num) ht
        linarith
  have hN_le : (N : ℝ) ≤ 2 * |t| := by linarith
  have hlogN : Real.log (N : ℝ) ≤ Real.log |t| + 1 := by
    have h := Real.log_le_log (by exact_mod_cast hN_pos) hN_le
    rw [Real.log_mul (by norm_num) (ne_of_gt htpos)] at h
    linarith [Real.log_two_lt_d9]
  have hharm : (harmonic N : ℝ) ≤ Real.log |t| + 2 := by
    exact (harmonic_le_one_add_log N).trans (by linarith)
  have ha_sum : Summable a := by
    simpa only [a] using summable_digammaSeriesTerm s hsre_one
  have hlow : ‖∑ n ∈ Finset.range N, a n‖ ≤
      (N : ℝ) * |t|⁻¹ + (harmonic N : ℝ) := by
    calc
      ‖∑ n ∈ Finset.range N, a n‖
          ≤ ∑ n ∈ Finset.range N, ‖a n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N, (|t|⁻¹ + (n + 1 : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro n _
        simpa only [a, hsim] using norm_digammaSeriesTerm_le_harmonic s n him
      _ = (N : ℝ) * |t|⁻¹ + (harmonic N : ℝ) := by
        have hh : (∑ n ∈ Finset.range N, (n + 1 : ℝ)⁻¹) = (harmonic N : ℝ) := by
          rw [harmonic]
          push_cast
          rfl
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hh]
  have hlow' : ‖∑ n ∈ Finset.range N, a n‖ ≤ Real.log |t| + 4 := by
    linarith
  have ha_tail : Summable (fun j : ℕ => a (j + N)) :=
    (summable_nat_add_iff N).2 ha_sum
  have hinv_tail : Summable
      (fun j : ℕ => (((N + j + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    have hbase : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
      simpa [one_div, Nat.cast_add, Nat.cast_one] using
        (summable_pow_div_add (1 : ℝ) 2 1 Nat.one_lt_two)
    have hshift := (summable_nat_add_iff N).2 hbase
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift
  have htail_point : ∀ j : ℕ,
      ‖a (j + N)‖ ≤ ‖s‖ * (((N + j + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro j
    have h := norm_digammaSeriesTerm_le s hsre_one (j + N)
    dsimp only [a]
    convert h using 1
    all_goals push_cast
    all_goals ring
  have htail : ‖∑' j : ℕ, a (j + N)‖ ≤ ‖s‖ * (2 / (N + 1 : ℝ)) := by
    calc
      ‖∑' j : ℕ, a (j + N)‖ ≤ ∑' j : ℕ, ‖a (j + N)‖ :=
        norm_tsum_le_tsum_norm ha_tail.norm
      _ ≤ ∑' j : ℕ, ‖s‖ * (((N + j + 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
        ha_tail.norm.tsum_le_tsum htail_point (hinv_tail.mul_left ‖s‖)
      _ = ‖s‖ * ∑' j : ℕ, (((N + j + 1 : ℕ) : ℝ) ^ 2)⁻¹ := tsum_mul_left
      _ ≤ ‖s‖ * (2 / (N + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_left (tsum_inv_sq_nat_add_le N) (norm_nonneg s)
  have hsnorm : ‖s‖ ≤ σ + |t| := by
    calc
      ‖s‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := by
        dsimp [s]
        exact norm_add_le _ _
      _ = σ + |t| := by simp [abs_of_nonneg (zero_le_one.trans hσ)]
  have htail' : ‖∑' j : ℕ, a (j + N)‖ ≤ σ + 2 := by
    calc
      ‖∑' j : ℕ, a (j + N)‖ ≤ ‖s‖ * (2 / (N + 1 : ℝ)) := htail
      _ ≤ ‖s‖ * (2 / |t|) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
        exact div_le_div_of_nonneg_left (by norm_num) htpos (by linarith)
      _ = 2 * ‖s‖ / |t| := by ring
      _ ≤ σ + 2 := by
        rw [div_le_iff₀ htpos]
        nlinarith [mul_nonneg (zero_le_one.trans hσ) (sub_nonneg.mpr ht)]
  have hsplit := ha_sum.sum_add_tsum_nat_add N
  have hseries : ‖∑' n : ℕ, a n‖ ≤ Real.log |t| + σ + 6 := by
    rw [← hsplit]
    calc
      ‖(∑ n ∈ Finset.range N, a n) + ∑' j : ℕ, a (j + N)‖
          ≤ ‖∑ n ∈ Finset.range N, a n‖ + ‖∑' j : ℕ, a (j + N)‖ :=
            norm_add_le _ _
      _ ≤ Real.log |t| + σ + 6 := by linarith
  have hs_im_norm : |t| ≤ ‖s‖ := by
    rw [← hsim]
    exact Complex.abs_im_le_norm s
  have hinv : ‖(1 : ℂ) / s‖ ≤ (1 : ℝ) / 2 := by
    rw [one_div, norm_inv]
    calc
      ‖s‖⁻¹ ≤ |t|⁻¹ := inv_anti₀ htpos hs_im_norm
      _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) ht
      _ = (1 : ℝ) / 2 := by norm_num
  have hgamma : ‖(Real.eulerMascheroniConstant : ℂ)‖ ≤ (2 : ℝ) / 3 := by
    have hgamma_pos : 0 < Real.eulerMascheroniConstant :=
      (by norm_num : (0 : ℝ) < 1 / 2).trans Real.one_half_lt_eulerMascheroniConstant
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hgamma_pos]
    exact Real.eulerMascheroniConstant_lt_two_thirds.le
  rw [digamma_series s hsre_one, norm_neg]
  have htotal : ‖(1 : ℂ) / s + Real.eulerMascheroniConstant + ∑' n : ℕ, a n‖ ≤
      Real.log |t| + σ + 8 := by
    calc
      ‖(1 : ℂ) / s + Real.eulerMascheroniConstant + ∑' n : ℕ, a n‖
          ≤ ‖(1 : ℂ) / s + Real.eulerMascheroniConstant‖ + ‖∑' n : ℕ, a n‖ :=
            norm_add_le _ _
      _ ≤ (‖(1 : ℂ) / s‖ + ‖(Real.eulerMascheroniConstant : ℂ)‖) +
          ‖∑' n : ℕ, a n‖ := by
            gcongr
            exact norm_add_le _ _
      _ ≤ Real.log |t| + σ + 8 := by linarith
  have hlogpos : 0 < Real.log |t| := log_abs_im_pos ht
  have hnonneg : 0 ≤ (2 * σ + 9) * Real.log |t| :=
    mul_nonneg (by linarith) hlogpos.le
  exact htotal.trans (by nlinarith)

/-! ## Digamma growth bound -/

/-- The digamma function satisfies ‖ψ(s)‖ ≤ C · log|Im s| in vertical strips.
    This is the key growth estimate needed for the Stirling approximation.

    Proof: shift s by N steps (N depends on σ₁) to land in Re ∈ [1,2].
    Use recurrence ψ(s) = ψ(s+N) - Σ (s+k)⁻¹. The sum contributes N/|t| = O(1).
    At the base strip, bound ‖ψ‖ ≤ C·log|t| via the partial fraction series. -/
theorem digamma_growth_bound (σ₁ σ₂ : ℝ) :
    ∃ C, 0 < C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 2 ≤ |s.im| →
      ‖Complex.digamma s‖ ≤ C * Real.log |s.im| := by
  -- Shift right by N to get Re(s+N) ≥ 1, then apply digamma_bound_re_ge_one
  set N : ℕ := max 1 ⌈1 - σ₁⌉₊
  -- C must absorb: base bound (2·(σ₂+N)+10)·(log|t|+3) + shift sum N/|t|
  -- Since log|t| ≥ log 2 > 0, we need C·log|t| ≥ (2σ₂+2N+10)·(log|t|+3) + N/2
  -- Take C = (2|σ₂|+2N+10)·4 + N (generous to avoid edge cases)
  set C : ℝ := (2 * |σ₂| + 2 * ↑N + 10) * 8 + ↑N + 1
  refine ⟨C, by positivity, fun s hσ₁ hσ₂ him => ?_⟩
  have ht_pos : 0 < |s.im| := by linarith
  have hlog_pos : 0 < Real.log |s.im| := Real.log_pos (by linarith)
  -- s is not at a non-positive integer
  have him_ne : ∀ m : ℕ, s ≠ -↑m := by
    intro m h; have := congr_arg Complex.im h; simp at this
    rw [this, abs_zero] at him; linarith
  -- All shifted points avoid non-positive integers
  have hshift_ne : ∀ k : ℕ, k < N → ∀ m : ℕ, s + ↑k ≠ -↑m := by
    intro k _ m h; have := congr_arg Complex.im h; simp at this
    rw [this, abs_zero] at him; linarith
  -- Re(s+N) ≥ 1
  have hre_shifted : 1 ≤ (s + ↑N).re := by
    simp only [add_re, natCast_re]
    have : (1 : ℝ) - σ₁ ≤ ↑N := by
      calc (1 : ℝ) - σ₁ ≤ max (1 - σ₁) 0 := le_max_left _ _
        _ ≤ ↑⌈max (1 - σ₁) 0⌉₊ := Nat.le_ceil _
        _ ≤ ↑(max 1 ⌈1 - σ₁⌉₊) := by
          have : ⌈max (1 - σ₁) 0⌉₊ = ⌈1 - σ₁⌉₊ := by
            rcases le_or_gt (1 - σ₁) 0 with h | h
            · simp [max_eq_right h, Nat.ceil_eq_zero.mpr h]
            · rw [max_eq_left h.le]
          rw [this]; exact_mod_cast le_max_right 1 ⌈1 - σ₁⌉₊
    linarith
  -- Write s = σ + it, apply digamma_shift
  have him1 : 1 ≤ |s.im| := by linarith
  have hshift := digamma_shift s N hshift_ne
  -- Im(s+N) = Im(s)
  have him_shifted : (s + ↑N).im = s.im := by simp
  -- s+N = ↑(s+N).re + ↑s.im * I
  have hs_eq : s + ↑N = ↑(s + ↑N).re + ↑s.im * I := by
    apply Complex.ext <;> simp
  -- Bound ψ(s+N) via digamma_bound_re_ge_one
  have hbase : ‖Complex.digamma (s + ↑N)‖ ≤
      (2 * (s + ↑N).re + 10) * (Real.log |s.im| + 3) := by
    have h := digamma_bound_re_ge_one (s + ↑N).re s.im hre_shifted him
    -- h : ‖ψ(↑re + ↑im * I)‖ ≤ ..., need ‖ψ(s+N)‖ ≤ ...
    rw [show (↑(s + ↑N).re : ℂ) + ↑s.im * I = s + ↑N from hs_eq.symm] at h
    exact h
  -- Bound the sum
  have hsum := shift_sum_bound s N him1
  -- log bounds
  have hlog2 : Real.log 2 ≤ Real.log |s.im| := Real.log_le_log (by norm_num) him
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_half : (1 : ℝ) / 2 < Real.log |s.im| := by
    calc (1:ℝ)/2
        = Real.log (Real.exp (1/2)) := (Real.log_exp _).symm
      _ < Real.log 2 := by
          apply Real.log_lt_log (Real.exp_pos _)
          have he := Real.exp_one_lt_three
          have hsq : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by
            rw [← Real.exp_add]; norm_num
          nlinarith [sq_nonneg (Real.exp (1/2))]
      _ ≤ Real.log |s.im| := hlog2
  -- 3 ≤ 6 · log|s.im| since log|s.im| > 1/2
  have h3 : 3 ≤ 6 * Real.log |s.im| := by nlinarith
  -- N/|s.im| ≤ N * log|s.im|
  have hN_div : (↑N : ℝ) / |s.im| ≤ ↑N * Real.log |s.im| := by
    calc (↑N : ℝ) / |s.im| ≤ ↑N / 2 := by gcongr
      _ = ↑N * (1 / 2) := by ring
      _ ≤ ↑N * Real.log |s.im| :=
          mul_le_mul_of_nonneg_left (le_of_lt hlog_half) (Nat.cast_nonneg N)
  -- σ₂ + N ≥ 1 (since Re(s+N) ≥ 1 and Re(s) ≤ σ₂)
  have hσN : (1 : ℝ) ≤ σ₂ + ↑N := by
    have : (s + ↑N).re = s.re + ↑N := by simp
    linarith
  -- Assembly via triangle inequality
  rw [hshift]
  -- Intermediate bound
  have hre_le : (s + ↑N).re ≤ σ₂ + ↑N := by
    simp only [Complex.add_re, Complex.natCast_re]; linarith
  have hstep : (2 * (s + ↑N).re + 10) * (Real.log |s.im| + 3) + ↑N / |s.im| ≤
      ((2 * σ₂ + 2 * ↑N + 10) * 7 + ↑N) * Real.log |s.im| := by
    have hA_pos : (0 : ℝ) ≤ 2 * (σ₂ + ↑N) + 10 := by linarith
    -- (s+N).re ≤ σ₂+N, so 2*(s+N).re + 10 ≤ 2*(σ₂+N) + 10
    have h1 : 2 * (s + ↑N).re + 10 ≤ 2 * (σ₂ + ↑N) + 10 := by linarith
    -- log + 3 ≤ 7*log since 3 ≤ 6*log (as log > 1/2)
    have h2 : Real.log |s.im| + 3 ≤ 7 * Real.log |s.im| := by nlinarith
    -- 2*(s+N).re + 10 ≥ 12 > 0
    have h3' : (0 : ℝ) ≤ 2 * (s + ↑N).re + 10 := by linarith [hre_shifted]
    nlinarith [hN_div, mul_le_mul h1 h2 (by nlinarith) hA_pos]
  calc ‖Complex.digamma (s + ↑N) - ∑ k ∈ Finset.range N, (s + ↑k)⁻¹‖
      ≤ ‖Complex.digamma (s + ↑N)‖ + ‖∑ k ∈ Finset.range N, (s + ↑k)⁻¹‖ := norm_sub_le _ _
    _ ≤ (2 * (s + ↑N).re + 10) * (Real.log |s.im| + 3) + ↑N / |s.im| :=
        add_le_add hbase hsum
    _ ≤ ((2 * σ₂ + 2 * ↑N + 10) * 7 + ↑N) * Real.log |s.im| := hstep
    _ ≤ C * Real.log |s.im| := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hlog_pos)
        show _ ≤ (2 * |σ₂| + 2 * ↑N + 10) * 8 + ↑N + 1
        nlinarith [le_abs_self σ₂, abs_nonneg σ₂]

/-! ## Complex Stirling bound

We prove the Stirling approximation for `log ‖Γ(s)‖` in vertical strips.
The proof uses the functional equation `Γ(s+1) = s·Γ(s)` to reduce to `Re(s) ∈ [1/2, 3/2)`,
then uses the reflection formula `Γ(s)·Γ(1-s) = π/sin(πs)` combined with `Γ(z̄) = conj(Γ(z))`
to compute `|Γ(1/2+it)|² = π/cosh(πt)`, and bounds the remaining terms.
-/

/-- sin(π(1/2 + it)) = cosh(πt) as complex numbers. -/
private lemma sin_pi_half_add_I_mul (t : ℝ) :
    Complex.sin (↑π * (1/2 + ↑t * Complex.I)) = ↑(Real.cosh (π * t)) := by
  have key : (↑π : ℂ) * (1/2 + ↑t * Complex.I) = ↑(π / 2) + ↑(π * t) * Complex.I := by
    push_cast; ring
  rw [key, Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
    Real.sin_pi_div_two, Real.cos_pi_div_two]
  push_cast; ring

/-- norm of Γ(1/2 + it) squared equals π / cosh(πt). -/
private lemma norm_sq_Gamma_half_add (t : ℝ) :
    ‖Complex.Gamma (1/2 + ↑t * Complex.I)‖ ^ 2 = π / Real.cosh (π * t) := by
  -- From the reflection formula: Γ(s)·Γ(1-s) = π/sin(πs)
  -- At s = 1/2 + it: 1 - s = 1/2 - it = conj(s), so Γ(1-s) = conj(Γ(s))
  -- Therefore |Γ(s)|² = Γ(s)·conj(Γ(s)) = π/sin(π(1/2+it)) = π/cosh(πt)
  set s := (1/2 : ℂ) + ↑t * Complex.I
  have h1s : 1 - s = conj s := by
    apply Complex.ext <;> simp [s, Complex.conj_re, Complex.conj_im] <;> ring
  have hΓ_eq : Complex.Gamma s * Complex.Gamma (1 - s) = ↑π / Complex.sin (↑π * s) :=
    Complex.Gamma_mul_Gamma_one_sub s
  rw [h1s, Complex.Gamma_conj] at hΓ_eq
  -- |Γ(s)|² = ‖Γ(s)‖² = Γ(s) * conj(Γ(s)) = π/sin(πs)
  have hΓ_norm : (‖Complex.Gamma s‖ ^ 2 : ℂ) = ↑π / Complex.sin (↑π * s) := by
    rw [← Complex.mul_conj']
    exact_mod_cast hΓ_eq
  -- sin(π·s) = cosh(πt) (real and positive)
  rw [sin_pi_half_add_I_mul] at hΓ_norm
  have hcosh_pos : (0 : ℝ) < Real.cosh (π * t) := Real.cosh_pos _
  -- Extract the real equation
  have : (‖Complex.Gamma s‖ ^ 2 : ℂ) = (↑(π / Real.cosh (π * t)) : ℂ) := by
    rw [hΓ_norm]; push_cast; rfl
  exact_mod_cast this

/-- log cosh(x) is close to |x| for large |x|: log(cosh x) ≤ |x| + log 2. -/
private lemma log_cosh_le (x : ℝ) : Real.log (Real.cosh x) ≤ |x| + Real.log 2 := by
  have hcosh_pos : (0 : ℝ) < Real.cosh x := Real.cosh_pos _
  -- cosh x ≤ exp|x| since cosh x = (exp x + exp(-x))/2 ≤ (exp|x| + exp|x|)/2 = exp|x|
  have hle : Real.cosh x ≤ Real.exp |x| := by
    rw [Real.cosh_eq]
    have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp_of_le (le_abs_self x)
    have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp_of_le (neg_le_abs x)
    linarith
  calc Real.log (Real.cosh x)
      ≤ Real.log (Real.exp |x|) := Real.log_le_log hcosh_pos hle
    _ = |x| := Real.log_exp _
    _ ≤ |x| + Real.log 2 := le_add_of_nonneg_right (Real.log_nonneg (by norm_num))

/-- log cosh(x) ≥ |x| - log 2 for all x. -/
private lemma le_log_cosh (x : ℝ) : |x| - Real.log 2 ≤ Real.log (Real.cosh x) := by
  have hcosh_pos : (0 : ℝ) < Real.cosh x := Real.cosh_pos _
  -- exp|x| ≤ 2 · cosh x since exp|x| ≤ exp x + exp(-x) = 2·cosh x
  have hle : Real.exp |x| ≤ 2 * Real.cosh x := by
    rw [Real.cosh_eq, mul_div_cancel₀ _ (two_ne_zero)]
    by_cases h : 0 ≤ x
    · calc Real.exp |x| = Real.exp x := by rw [abs_of_nonneg h]
        _ ≤ Real.exp x + Real.exp (-x) := le_add_of_nonneg_right (by positivity)
    · push_neg at h
      calc Real.exp |x| = Real.exp (-x) := by rw [abs_of_neg h]
        _ ≤ Real.exp x + Real.exp (-x) := le_add_of_nonneg_left (by positivity)
  calc |x| - Real.log 2
      = Real.log (Real.exp |x|) - Real.log 2 := by rw [Real.log_exp]
    _ ≤ Real.log (2 * Real.cosh x) - Real.log 2 := by
        gcongr
    _ = Real.log 2 + Real.log (Real.cosh x) - Real.log 2 := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hcosh_pos)]
    _ = Real.log (Real.cosh x) := by ring

/-- The reflection formula base case: log‖Γ(1/2+it)‖ is approximately -π|t|/2. -/
private lemma log_norm_Gamma_half_approx (t : ℝ) (ht : 2 ≤ |t|) :
    |Real.log ‖Complex.Gamma (1/2 + ↑t * Complex.I)‖ + |t| * (Real.pi / 2)| ≤
      (Real.log π + Real.log 2) / 2 + Real.log 2 := by
  set s := (1/2 : ℂ) + ↑t * Complex.I
  -- From norm_sq_Gamma_half_add: ‖Γ(s)‖² = π/cosh(πt)
  -- So log‖Γ(s)‖ = (1/2)(log π - log(cosh(πt)))
  -- And log(cosh(πt)) = π|t| + O(1)
  -- Hence log‖Γ(s)‖ + π|t|/2 = (1/2)(log π - log(cosh(πt)) + π|t|)
  -- = (1/2)(log π - π|t| - O(1) + π|t|) = O(1)
  have hΓ_pos : 0 < ‖Complex.Gamma s‖ := by
    rw [norm_pos_iff]
    apply Complex.Gamma_ne_zero
    intro m h
    have : s.im = (-↑m : ℂ).im := congr_arg Complex.im h
    simp [s] at this
    rw [this, abs_zero] at ht; linarith
  have hcosh_pos : (0 : ℝ) < Real.cosh (π * t) := Real.cosh_pos _
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  -- log ‖Γ(s)‖ = (1/2) · log(π / cosh(πt)) = (1/2)(log π - log(cosh(πt)))
  have hlog_norm : Real.log ‖Complex.Gamma s‖ =
      (Real.log π - Real.log (Real.cosh (π * t))) / 2 := by
    have h := norm_sq_Gamma_half_add t
    have hΓ_sq : Real.log (‖Complex.Gamma s‖ ^ 2) = 2 * Real.log ‖Complex.Gamma s‖ := by
      rw [Real.log_pow, Nat.cast_ofNat]
    rw [h] at hΓ_sq
    rw [Real.log_div (by positivity) (by positivity)] at hΓ_sq
    linarith
  rw [hlog_norm]
  -- Need: |(log π - log(cosh(πt)))/2 + |t|·π/2| ≤ (log π + log 2)/2 + log 2
  -- = |(log π + π|t| - log(cosh(πt)))/2|
  rw [show (Real.log π - Real.log (Real.cosh (π * t))) / 2 + |t| * (Real.pi / 2) =
      (Real.log π + π * |t| - Real.log (Real.cosh (π * t))) / 2 by ring]
  -- Need: |(log π + π|t| - log(cosh(πt)))/2| ≤ (log π + log 2)/2 + log 2
  have habs_πt : |π * t| = π * |t| := by rw [abs_mul, abs_of_pos hπ_pos]
  have h_upper : Real.log π + π * |t| - Real.log (Real.cosh (π * t)) ≤ Real.log π + Real.log 2 := by
    have := le_log_cosh (π * t)
    rw [habs_πt] at this; linarith
  have h_lower : Real.log π - Real.log 2 ≤ Real.log π + π * |t| - Real.log (Real.cosh (π * t)) := by
    have := log_cosh_le (π * t)
    rw [habs_πt] at this; linarith
  have hlog_pi_pos : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abs_le]; constructor <;> linarith

/-- For bounded σ and |t| ≥ 2: log√(σ² + t²) ≈ log|t| with error ≤ C. -/
private lemma log_norm_approx (σ : ℝ) (t : ℝ) (ht : 2 ≤ |t|) :
    |Real.log (Real.sqrt (σ ^ 2 + t ^ 2)) - Real.log (|t|)| ≤
      (1/2) * Real.log (1 + (σ / 2) ^ 2) := by
  have ht_pos : 0 < |t| := by linarith
  have ht_ne : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
  have hst : 0 < σ ^ 2 + t ^ 2 := by positivity
  -- √(σ² + t²) = |t| · √(1 + (σ/t)²)
  have hsqrt_eq : Real.sqrt (σ ^ 2 + t ^ 2) = |t| * Real.sqrt (1 + (σ / t) ^ 2) := by
    have : σ ^ 2 + t ^ 2 = t ^ 2 * (1 + (σ / t) ^ 2) := by
      field_simp; ring
    rw [this, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
  have h1_pos : 0 < 1 + (σ / t) ^ 2 := by positivity
  rw [hsqrt_eq, Real.log_mul ht_pos.ne' (Real.sqrt_pos.mpr h1_pos).ne',
    add_sub_cancel_left, Real.log_sqrt h1_pos.le]
  -- Need: |log(1 + (σ/t)²) / 2| ≤ (1/2) · log(1 + (σ/2)²)
  -- Since 1 + (σ/t)² ≥ 1, log ≥ 0
  have hge1 : 1 ≤ 1 + (σ / t) ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
  have hlog_nonneg := Real.log_nonneg hge1
  -- (σ/t)² ≤ (σ/2)² since |t| ≥ 2
  have hbound : (σ / t) ^ 2 ≤ (σ / 2) ^ 2 := by
    rw [div_pow, div_pow]
    apply div_le_div_of_nonneg_left (sq_nonneg σ) (by positivity)
    calc (2 : ℝ) ^ 2 = 4 := by norm_num
      _ ≤ |t| ^ 2 := by nlinarith
      _ = t ^ 2 := sq_abs t
  have hlog_le : Real.log (1 + (σ / t) ^ 2) ≤ Real.log (1 + (σ / 2) ^ 2) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [abs_of_nonneg (by positivity)]
  linarith

/-- **Complex Stirling approximation.**

    In any vertical strip σ₁ ≤ Re s ≤ σ₂ with |Im s| ≥ 2:
    log‖Γ(s)‖ = (Re s - 1/2)·log|Im s| - |Im s|·π/2 + O(log|Im s|). -/
theorem complex_stirling_bound (σ₁ σ₂ : ℝ) (hσ : σ₁ ≤ σ₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      2 ≤ |s.im| →
      |Real.log ‖Complex.Gamma s‖ -
        ((s.re - 1/2) * Real.log |s.im| -
         |s.im| * (Real.pi / 2))| ≤ C * Real.log |s.im| := by
  let a : ℝ := min σ₁ (1 / 2)
  let b : ℝ := max σ₂ (1 / 2)
  have hab : a ≤ b := by
    dsimp [a, b]
    exact (min_le_left _ _).trans (hσ.trans (le_max_left _ _))
  obtain ⟨D, hD_pos, hD⟩ := digamma_growth_bound a b
  let W : ℝ := |σ₁| + |σ₂| + 1
  let A : ℝ := (Real.log π + Real.log 2) / 2 + Real.log 2
  refine ⟨D * W + W + 2 * A, ?_, fun s hσ₁ hσ₂ him => ?_⟩
  · have hW_pos : 0 < W := by dsimp [W]; positivity
    have hA_pos : 0 < A := by
      dsimp [A]
      have hlogpi : 0 < Real.log π := Real.log_pos (by linarith [Real.pi_gt_three])
      have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    positivity
  · let t : ℝ := s.im
    let L : ℝ := Real.log |t|
    let f : ℝ → ℝ := fun x => Real.log ‖Complex.Gamma (↑x + ↑t * I)‖
    have ht : 2 ≤ |t| := by simpa [t] using him
    have ht_ne : t ≠ 0 := by
      intro ht0
      rw [ht0, abs_zero] at ht
      linarith
    have hL_pos : 0 < L := by exact log_abs_im_pos ht
    have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Icc a b := by
      exact ⟨min_le_right _ _, le_max_right _ _⟩
    have hre_mem : s.re ∈ Set.Icc a b := by
      exact ⟨(min_le_left _ _).trans hσ₁, hσ₂.trans (le_max_left _ _)⟩
    have hderiv : ∀ x ∈ Set.Icc a b,
        HasDerivWithinAt f (Complex.digamma (↑x + ↑t * I)).re (Set.Icc a b) x := by
      intro x hx
      apply HasDerivAt.hasDerivWithinAt
      apply hasDerivAt_log_norm_Gamma x t ht_ne
      intro m hm
      have him_eq := congr_arg Complex.im hm
      simp at him_eq
      exact ht_ne him_eq
    have hderiv_bound : ∀ x ∈ Set.Icc a b,
        ‖(Complex.digamma (↑x + ↑t * I)).re‖ ≤ D * L := by
      intro x hx
      calc
        ‖(Complex.digamma (↑x + ↑t * I)).re‖
            ≤ ‖Complex.digamma (↑x + ↑t * I)‖ := Complex.abs_re_le_norm _
        _ ≤ D * Real.log |(↑x + ↑t * I : ℂ).im| := by
          apply hD
          · simpa using hx.1
          · simpa using hx.2
          · simpa using ht
        _ = D * L := by simp [L]
    have hcompare := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hderiv_bound (convex_Icc a b) hhalf_mem hre_mem
    have hre_abs : |s.re| ≤ |σ₁| + |σ₂| := by
      rw [abs_le]
      constructor <;> linarith [le_abs_self σ₁, neg_le_abs σ₁,
        le_abs_self σ₂, neg_le_abs σ₂, abs_nonneg σ₁, abs_nonneg σ₂]
    have hwidth : |s.re - 1 / 2| ≤ W := by
      calc
        |s.re - 1 / 2| ≤ |s.re| + |(1 / 2 : ℝ)| := abs_sub _ _
        _ ≤ W := by dsimp [W]; norm_num at *; linarith
    have hcompare' : |f s.re - f (1 / 2)| ≤ D * L * W := by
      calc
        |f s.re - f (1 / 2)| = ‖f s.re - f (1 / 2)‖ := (Real.norm_eq_abs _).symm
        _ ≤ D * L * ‖s.re - 1 / 2‖ := hcompare
        _ ≤ D * L * W := by
          rw [Real.norm_eq_abs]
          gcongr
    have hbase : |f (1 / 2) + |t| * (Real.pi / 2)| ≤ A := by
      simpa [f, A] using log_norm_Gamma_half_approx t ht
    have hA_le : A ≤ 2 * A * L := by
      have hhalf_log : (1 / 2 : ℝ) < L := by
        dsimp [L]
        calc
          (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2)) := (Real.log_exp _).symm
          _ < Real.log 2 := by
            apply Real.log_lt_log (Real.exp_pos _)
            have he := Real.exp_one_lt_three
            have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
              rw [← Real.exp_add]
              norm_num
            nlinarith [sq_nonneg (Real.exp (1 / 2))]
          _ ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
      have hA_nonneg : 0 ≤ A := by
        dsimp [A]
        have hlogpi : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
        have hlogtwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        positivity
      nlinarith
    have hmain_width : |(s.re - 1 / 2) * L| ≤ W * L := by
      rw [abs_mul, abs_of_pos hL_pos]
      exact mul_le_mul_of_nonneg_right hwidth hL_pos.le
    have hs_cart : (↑s.re + ↑t * I : ℂ) = s := by
      apply Complex.ext <;> simp [t]
    have hf_re : f s.re = Real.log ‖Complex.Gamma s‖ := by
      simp only [f]
      rw [hs_cart]
    rw [← hf_re, ← show L = Real.log |s.im| by rfl,
      ← show |t| = |s.im| by rfl]
    calc
      |f s.re - ((s.re - 1 / 2) * L - |t| * (Real.pi / 2))|
          = |(f s.re - f (1 / 2)) + (f (1 / 2) + |t| * (Real.pi / 2)) -
              (s.re - 1 / 2) * L| := by ring_nf
      _ ≤ |f s.re - f (1 / 2)| + |f (1 / 2) + |t| * (Real.pi / 2)| +
          |(s.re - 1 / 2) * L| := by
        have h₁ := abs_sub
          ((f s.re - f (1 / 2)) + (f (1 / 2) + |t| * (Real.pi / 2)))
          ((s.re - 1 / 2) * L)
        have h₂ := abs_add_le (f s.re - f (1 / 2))
          (f (1 / 2) + |t| * (Real.pi / 2))
        linarith
      _ ≤ D * L * W + A + W * L := by linarith
      _ ≤ D * L * W + 2 * A * L + W * L := by linarith
      _ = (D * W + W + 2 * A) * L := by ring

/-! ## Crude Gamma bound for order estimates

For the order of the completed zeta function, we only need the crude bound
log|Γ(s)| ≤ C · |s| · log|s|, not the full Stirling approximation. This
follows from |Γ(s)| ≤ Γ(Re(s)) for Re(s) > 0 (integral bound) plus the
reflection formula for Re(s) ≤ 0, plus real Stirling for Γ(x).
-/

/-- Crude bound: |Γ(s)| ≤ Γ(Re(s)) for Re(s) > 0.
    Follows from the integral representation: |∫ t^{s-1} e^{-t} dt| ≤ ∫ t^{Re(s)-1} e^{-t} dt. -/
private lemma norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs]
  calc ‖Complex.GammaIntegral s‖
      = ‖∫ x in Ioi (0 : ℝ), ↑((-x).exp) * (x : ℂ) ^ (s - 1)‖ := rfl
    _ ≤ ∫ x in Ioi (0 : ℝ), ‖↑((-x).exp) * (x : ℂ) ^ (s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (s.re - 1) := by
        apply setIntegral_congr_fun measurableSet_Ioi (fun x (hx : (0 : ℝ) < x) => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Complex.norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]

/-- Γ(x) ≤ 1 for x ∈ [1, 2], from convexity + Γ(1) = Γ(2) = 1. -/
private lemma Gamma_le_one_of_mem_Icc {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) :
    Real.Gamma x ≤ 1 := by
  have hx_pos : x ∈ Ioi (0 : ℝ) := by simp; linarith
  have h1_pos : (1 : ℝ) ∈ Ioi (0 : ℝ) := by simp
  have h2_pos : (2 : ℝ) ∈ Ioi (0 : ℝ) := by simp
  have h_conv := Real.convexOn_Gamma
  have ht1 : 0 ≤ 2 - x := by linarith
  have ht2 : 0 ≤ x - 1 := by linarith
  have hsum : 2 - x + (x - 1) = 1 := by ring
  calc Real.Gamma x = Real.Gamma ((2 - x) * 1 + (x - 1) * 2) := by ring_nf
    _ ≤ (2 - x) * Real.Gamma 1 + (x - 1) * Real.Gamma 2 :=
        h_conv.2 h1_pos h2_pos ht1 ht2 hsum
    _ = 1 := by rw [Real.Gamma_one, Real.Gamma_two]; ring

/-- Helper: log Γ(x) ≤ x log x by induction on ⌊x⌋. -/
private lemma log_Gamma_le_mul_log_aux :
    ∀ n : ℕ, 2 ≤ n → ∀ x : ℝ, (n : ℝ) ≤ x → x ≤ (n : ℝ) + 1 →
      Real.log (Real.Gamma x) ≤ x * Real.log x := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
    intro hm x hx_lo hx_hi
    by_cases hm2 : m + 1 = 2
    · -- Base case: n = 2, x ∈ [2, 3]
      have hm_eq : m = 1 := by omega
      subst hm_eq; push_cast at hx_lo hx_hi
      have hx1_lo : 1 ≤ x - 1 := by linarith
      have hx1_hi : x - 1 ≤ 2 := by linarith
      have hΓ_le : Real.Gamma (x - 1) ≤ 1 := Gamma_le_one_of_mem_Icc hx1_lo hx1_hi
      have hx_pos : 0 < x := by linarith
      have hxm1_pos : 0 < x - 1 := by linarith
      have hxm1_ne : x - 1 ≠ 0 := ne_of_gt hxm1_pos
      have hΓ_eq : Real.Gamma x = (x - 1) * Real.Gamma (x - 1) := by
        have := Real.Gamma_add_one hxm1_ne; rw [sub_add_cancel] at this; linarith
      have hΓ_pos : 0 < Real.Gamma (x - 1) := Real.Gamma_pos_of_pos hxm1_pos
      calc Real.log (Real.Gamma x)
          = Real.log ((x - 1) * Real.Gamma (x - 1)) := by rw [hΓ_eq]
        _ = Real.log (x - 1) + Real.log (Real.Gamma (x - 1)) :=
            Real.log_mul hxm1_ne (ne_of_gt hΓ_pos)
        _ ≤ Real.log (x - 1) + 0 := by gcongr; exact Real.log_nonpos hΓ_pos.le hΓ_le
        _ = Real.log (x - 1) := add_zero _
        _ ≤ Real.log x := Real.log_le_log hxm1_pos (by linarith)
        _ = 1 * Real.log x := (one_mul _).symm
        _ ≤ x * Real.log x :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg (by linarith))
    · -- Inductive step: m + 1 ≥ 3, so m ≥ 2
      have hm_ge2 : 2 ≤ m := by omega
      have hx_ge3 : (3 : ℝ) ≤ x := by
        have : (m + 1 : ℕ) ≥ 3 := by omega
        exact le_trans (by exact_mod_cast this) hx_lo
      have hx_pos : 0 < x := by linarith
      have hxm1_pos : 0 < x - 1 := by linarith
      have hxm1_ne : x - 1 ≠ 0 := ne_of_gt hxm1_pos
      have hΓ_eq : Real.Gamma x = (x - 1) * Real.Gamma (x - 1) := by
        have := Real.Gamma_add_one hxm1_ne; rw [sub_add_cancel] at this; linarith
      have hΓ_pos : 0 < Real.Gamma (x - 1) := Real.Gamma_pos_of_pos hxm1_pos
      have hxm1_lo : (m : ℝ) ≤ x - 1 := by push_cast at hx_lo ⊢; linarith
      have hxm1_hi : x - 1 ≤ (m : ℝ) + 1 := by push_cast at hx_hi ⊢; linarith
      have hih := ih hm_ge2 (x - 1) hxm1_lo hxm1_hi
      calc Real.log (Real.Gamma x)
          = Real.log ((x - 1) * Real.Gamma (x - 1)) := by rw [hΓ_eq]
        _ = Real.log (x - 1) + Real.log (Real.Gamma (x - 1)) :=
            Real.log_mul hxm1_ne (ne_of_gt hΓ_pos)
        _ ≤ Real.log (x - 1) + (x - 1) * Real.log (x - 1) := by gcongr
        _ = x * Real.log (x - 1) := by ring
        _ ≤ x * Real.log x := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            exact Real.log_le_log hxm1_pos (by linarith)

/-- Crude bound: log Γ(x) ≤ x · log x for real x ≥ 2.
    From Stirling: Γ(x) = √(2π) · x^{x-1/2} · e^{-x} · (1 + O(1/x)).
    So log Γ(x) = (x-1/2)log x - x + (1/2)log(2π) + O(1/x) ≤ x · log x. -/
private lemma log_Gamma_le_mul_log {x : ℝ} (hx : 2 ≤ x) :
    Real.log (Real.Gamma x) ≤ x * Real.log x := by
  have hn := Nat.floor_le (by linarith : 0 ≤ x)
  have hn_lt := Nat.lt_floor_add_one x
  have hfl : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  exact log_Gamma_le_mul_log_aux ⌊x⌋₊ hfl x hn (le_of_lt hn_lt)

end ArithmeticHodge.Analysis
