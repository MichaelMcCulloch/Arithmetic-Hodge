/-
  Complex Stirling Approximation for Γ(s)

  Provides:
  1. complex_stirling_bound: log|Γ(σ+it)| = (σ-1/2)·log|t| - π|t|/2 + O(log|t|)
  2. digamma_growth_bound: ‖ψ(s)‖ ≤ C·log|t| in vertical strips

  Strategy for Stirling: Use reflection formula Γ(s)Γ(1-s) = π/sin(πs) at integer
  real parts to get |Γ(M+it)|, then extend via functional equation.

  Strategy for digamma: Establish the series ψ(s) = -γ + Σ(1/(k+1) - 1/(s+k))
  via uniqueness (Liouville argument on g/sin(πs)), then bound the series.
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

/-- Bound: 1/(n+1) - 1/(s+n) = (s-1)/((n+1)·(s+n)). -/
private lemma series_term_eq (s : ℂ) (n : ℕ) :
    (1 : ℂ) / (↑n + 1) - 1 / (s + ↑n) =
    (s - 1) / ((↑n + 1) * (s + ↑n)) := by
  have h1 : (↑n : ℂ) + 1 ≠ 0 := by
    push_cast; exact_mod_cast Nat.succ_ne_zero n
  by_cases hs : s + ↑n = 0
  · simp [hs, div_zero]
  · field_simp

/-- The series terms are O(1/n²) for n large relative to |s|. -/
private lemma series_term_bound (s : ℂ) (n : ℕ) (hn : (n : ℝ) ≥ 2 * ‖s‖ + 2) :
    ‖(1 : ℂ) / (↑n + 1) - 1 / (s + ↑n)‖ ≤
    2 * (‖s‖ + 1) / (↑n : ℝ) ^ 2 := by
  rw [series_term_eq, norm_div, norm_mul]
  have hn_pos : (0 : ℝ) < n := by linarith
  have hn_cast_pos : (0 : ℝ) < (n : ℝ) := hn_pos
  -- Reverse triangle: ‖s + n‖ ≥ n - ‖s‖ ≥ n/2
  have h_sn : (n : ℝ) / 2 ≤ ‖s + ↑n‖ := by
    have h1 : ‖(↑n : ℂ)‖ ≤ ‖s + ↑n‖ + ‖s‖ := by
      calc ‖(↑n : ℂ)‖ = ‖(s + ↑n) + (-s)‖ := by ring_nf
        _ ≤ ‖s + ↑n‖ + ‖-s‖ := norm_add_le _ _
        _ = ‖s + ↑n‖ + ‖s‖ := by rw [norm_neg]
    have h2 : ‖(↑n : ℂ)‖ = (n : ℝ) := by
      simp [Complex.norm_natCast]
    linarith
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
  have h_prod_pos : 0 < ‖(↑n + 1 : ℂ)‖ * ‖s + ↑n‖ := by positivity
  calc ‖s - 1‖ / (‖(↑n : ℂ) + 1‖ * ‖s + ↑n‖)
      ≤ (‖s‖ + 1) / (‖(↑n : ℂ) + 1‖ * ‖s + ↑n‖) := by
        apply div_le_div_of_nonneg_right h_num (le_of_lt h_prod_pos)
    _ ≤ (‖s‖ + 1) / ((n : ℝ) ^ 2 / 2) := by
        apply div_le_div_of_nonneg_left _ h_denom_pos h_denom
        linarith [norm_nonneg s]
    _ = 2 * (‖s‖ + 1) / (n : ℝ) ^ 2 := by ring

/-! ## Digamma growth bound

  We prove: ‖ψ(s)‖ ≤ C · log|Im(s)| for Re(s) in a bounded range, |Im(s)| ≥ 2.

  The proof establishes the series representation
    ψ(s) = -γ + Σ_{k≥0} (1/(k+1) - 1/(s+k))
  via a uniqueness argument, then bounds the series.
-/

/-- The digamma function satisfies ‖ψ(s)‖ ≤ C · log|Im s| in vertical strips.
    This is the key growth estimate needed for the Stirling approximation. -/
theorem digamma_growth_bound (σ₁ σ₂ : ℝ) :
    ∃ C, 0 < C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 2 ≤ |s.im| →
      ‖Complex.digamma s‖ ≤ C * Real.log |s.im| := by
  -- We use the functional equation to reduce to Re(s) ∈ [1, 2], then apply
  -- a direct bound using the reflection formula and series estimates.
  --
  -- The key identity: ψ(s) = ψ(s+N) - Σ_{k=0}^{N-1} (s+k)⁻¹
  -- Each |(s+k)⁻¹| ≤ 1/|Im s| since |s+k| ≥ |Im s|.
  --
  -- For Re(w) ∈ [1, 2] and |Im w| ≥ 2, we bound |ψ(w)| using:
  -- The reflection formula derivative: ψ(s) - ψ(1-s) = -π·cot(πs)
  -- Combined with conjugation: ψ(z̄) = conj(ψ(z))
  -- And the recurrence to shift both ψ(s) and ψ(1-s) to bounded regions.
  --
  -- The constant C depends on σ₁ and σ₂.
  let N := max 0 (⌈2 - σ₁⌉₊)
  refine ⟨(N + 1) * (|σ₂| + |σ₁| + 10) + 1, by positivity, fun s hσ₁ hσ₂ him => ?_⟩
  -- For s not a non-positive integer (guaranteed by |Im s| ≥ 2)
  have hs_ne : ∀ m : ℕ, s ≠ -↑m := by
    intro m
    intro h
    have : s.im = (-↑m : ℂ).im := congr_arg Complex.im h
    simp at this
    linarith [abs_nonneg s.im]
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
  -- Strategy: Use reflection formula at integer real parts + functional equation.
  --
  -- Step 1: For integer M and |t| ≥ 2, the reflection formula gives
  --   |Γ(M+it)|² = π·|t|^{M-1} / (|sinh(πt)|·β) where β ≈ 1
  --   hence log|Γ(M+it)| = ((M-1)/2)·log|t| - π|t|/2 + O_M(1)
  --
  -- Step 2: For general s = σ+it, shift to Re = M using Γ(s) = Γ(s+N)/Π(s+k):
  --   log|Γ(s)| = log|Γ(M+it)| - Σ log|s+k| = ((M-1)/2 - N)·log|t| - π|t|/2 + O(1)
  --
  -- Step 3: The error from the Stirling main term (σ-1/2)·log|t| - π|t|/2:
  --   |((σ-1)/2 - (σ-1/2))·log|t|| = (1/2)|log|t|| = O(log|t|)
  obtain ⟨Cψ, hCψ_pos, hCψ⟩ := digamma_growth_bound (min σ₁ (1/2)) (max σ₂ (1/2))
  refine ⟨Cψ * (|σ₂ - 1/2| + |σ₁ - 1/2| + 1) + |σ₂| + |σ₁| + 10,
    by positivity, fun s hσ₁ hσ₂ him => ?_⟩
  sorry

end ArithmeticHodge.Analysis
