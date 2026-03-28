/-
  Complex Stirling Approximation for Γ(s)

  Provides:
  1. complex_stirling_bound: log|Γ(σ+it)| = (σ-1/2)·log|t| - π|t|/2 + O(log|t|)
  2. digamma_growth_bound: ‖ψ(s)‖ ≤ C·log|t| in vertical strips

  Strategy for digamma: Use the functional equation ψ(s+1) = ψ(s) + 1/s
  iteratively and bound ψ in the shifted region via the Weierstrass series
  representation ψ(s) = -γ + Σ(1/(k+1) - 1/(s+k)), established by Liouville.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv

open Complex Real Filter Topology MeasureTheory Set Finset
open scoped NNReal

noncomputable section

namespace ArithmeticHodge.Analysis

/-! ## Auxiliary estimates -/

/-- For |t| ≥ 2, log|t| ≥ log 2 > 0. -/
private lemma log_abs_im_pos {t : ℝ} (ht : 2 ≤ |t|) : 0 < Real.log |t| :=
  Real.log_pos (by linarith)

/-- For s not a non-positive integer when |Im s| ≥ 2. -/
private lemma ne_neg_nat_of_im_ge_two {s : ℂ} (him : 2 ≤ |s.im|) :
    ∀ m : ℕ, s ≠ -↑m := by
  intro m h
  have : s.im = (-↑m : ℂ).im := congr_arg Complex.im h
  simp at this; rw [this, abs_zero] at him; linarith

/-- |Im s| ≤ ‖s + k‖ for any k : ℕ. -/
private lemma abs_im_le_norm_add_nat (s : ℂ) (k : ℕ) : |s.im| ≤ ‖s + ↑k‖ := by
  have h : |s.im| = |(s + ↑k).im| := by simp
  rw [h]; exact Complex.abs_im_le_norm _

/-- Iterating the digamma functional equation:
    ψ(s) = ψ(s + N) - Σ_{k=0}^{N-1} (s+k)⁻¹ -/
private lemma digamma_shift (s : ℂ) (hs : ∀ m : ℕ, s ≠ -↑m) (N : ℕ) :
    Complex.digamma s = Complex.digamma (s + ↑N) - ∑ k ∈ range N, (s + ↑k)⁻¹ := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hs_shift : ∀ m : ℕ, s + ↑n ≠ -↑m := by
      intro m hm
      exact hs (m + n) (by
        have : s = -↑m - (↑n : ℂ) := by linear_combination hm
        rw [this]; push_cast; ring)
    rw [ih, sum_range_succ]
    have heq := Complex.digamma_apply_add_one (s + ↑n) hs_shift
    have hcast : s + ↑(n + 1) = s + ↑n + 1 := by push_cast; ring
    rw [hcast, heq]; ring

/-- Norm of the digamma shift sum is bounded by N / |Im s|. -/
private lemma norm_digamma_shift_sum (s : ℂ) (him : 2 ≤ |s.im|) (N : ℕ) :
    ‖∑ k ∈ range N, (s + ↑k)⁻¹‖ ≤ ↑N / |s.im| := by
  calc ‖∑ k ∈ range N, (s + ↑k)⁻¹‖
      ≤ ∑ k ∈ range N, ‖(s + ↑k)⁻¹‖ := norm_sum_le _ _
    _ = ∑ k ∈ range N, (1 / ‖s + ↑k‖) := by
        congr 1; ext k; rw [norm_inv, one_div]
    _ ≤ ∑ k ∈ range N, (1 / |s.im|) := by
        apply sum_le_sum; intro k _
        exact div_le_div_of_nonneg_left (by positivity) (by linarith) (abs_im_le_norm_add_nat s k)
    _ = ↑N / |s.im| := by rw [sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-! ## Digamma growth bound -/

/-- The digamma function satisfies ‖ψ(s)‖ ≤ C · log|Im s| in vertical strips.
    This is the key growth estimate needed for the Stirling approximation. -/
theorem digamma_growth_bound (σ₁ σ₂ : ℝ) :
    ∃ C, 0 < C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 2 ≤ |s.im| →
      ‖Complex.digamma s‖ ≤ C * Real.log |s.im| := by
  -- Strategy: use ψ(s+1) = ψ(s) + 1/s iteratively N times (N depending on σ₁)
  -- to shift Re(s) into [1, σ₂+N+1]. The shift sum is bounded by N/|Im s| ≤ N/2.
  --
  -- For the shifted point w with |Im w| ≥ 2 and Re(w) in a fixed bounded range,
  -- we bound ψ(w) using the Weierstrass series representation
  --   ψ(s) = -γ + Σ_{k≥0} (1/(k+1) - 1/(s+k))
  -- which gives |ψ(w)| ≤ γ + C · (log|Im w| + 1) by splitting the series at k ≈ |Im w|.
  --
  -- The series representation is established by showing that g(s) = ψ(s) - f(s)
  -- is an entire periodic function of sub-exponential growth rate < 2π,
  -- hence constant by the Fourier expansion argument, and zero since g(1) = 0.
  -- The sub-exponential bound |ψ(s)| ≤ C·e^{π|Im s|} follows from
  -- |Γ(s)| ≤ Γ(Re s), the reflection formula, and Cauchy's estimate for Γ'.
  --
  -- See: Whittaker-Watson Ch. 12 or Titchmarsh, Theory of Functions, Ch. 4.
  sorry

/-- **Complex Stirling approximation.**

    In any vertical strip σ₁ ≤ Re s ≤ σ₂ with |Im s| ≥ 2:
    log‖Γ(s)‖ = (Re s - 1/2)·log|Im s| - |Im s|·π/2 + O(log|Im s|). -/
theorem complex_stirling_bound (σ₁ σ₂ : ℝ) (hσ : σ₁ ≤ σ₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      2 ≤ |s.im| →
      |Real.log ‖Complex.Gamma s‖ -
        ((s.re - 1/2) * Real.log |s.im| -
         |s.im| * (Real.pi / 2))| ≤ C * Real.log |s.im| := by
  obtain ⟨Cψ, hCψ_pos, hCψ⟩ := digamma_growth_bound (min σ₁ (1/2)) (max σ₂ (1/2))
  refine ⟨Cψ * (|σ₂ - 1/2| + |σ₁ - 1/2| + 1) + |σ₂| + |σ₁| + 10,
    by positivity, fun s hσ₁ hσ₂ him => ?_⟩
  sorry

end ArithmeticHodge.Analysis
