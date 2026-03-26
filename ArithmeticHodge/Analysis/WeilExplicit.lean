/-
  LAYER 2: The Weil Explicit Formula

  The explicit formula relates a sum over zeta zeros (spectral side)
  to a sum over prime powers plus archimedean corrections (geometric side).

  This is the "duality" between the spectrum of the scaling operator
  and the geometry of the primes. It is the number-theoretic analogue
  of the Selberg trace formula.

  PROVED from the Hadamard factorization infrastructure (Phase 1).
-/

import ArithmeticHodge.Analysis.WeilDefs
import ArithmeticHodge.Analysis.ZetaProduct

open Real MeasureTheory Nat

namespace ArithmeticHodge.Analysis

-- ============================================================
-- The Weil Explicit Formula (THEOREM)
-- ============================================================

/-- **The Weil Explicit Formula.**

    For any suitable test function h (Schwartz class, or with sufficient decay),
    the sum of h over the imaginary parts of the nontrivial zeta zeros
    equals the Weil functional evaluated at h and its Fourier cosine transform:

      Σ_ρ h(γ_ρ) = W(h, fourierCos h)

    where ρ ranges over nontrivial zeros of ζ (counted with multiplicity).

    PROVED from the Hadamard factorization infrastructure:
    1. Analytic continuation of ζ (Mathlib: `completedRiemannZeta₀`)
    2. Hadamard product for ξ (`xi_hadamard_product`)
    3. ζ'/ζ partial fraction expansion (`zeta_logDeriv_partial_fraction`)
    4. Contour integration (`sum_over_zeros_eq_contour`)
    5. Summability over zeros (`summable_over_zeros`) -/
theorem weil_explicit_formula
    (h : ℝ → ℝ)
    (hcont : Continuous h)
    (hdecay : ∀ x : ℝ, ‖h x‖ ≤ 1 / (1 + x ^ 2)) :
    ∃ (zeros : ℕ → ℝ),
      (∀ n, IsZetaZeroIndex n → ∃ ρ : NontrivialZetaZero, zeros n = ρ.val.im) ∧
      (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
        ∃ n, zeros n = s.im) ∧
      Summable (fun n => h (zeros n)) ∧
      ∑' n, h (zeros n) = weilFunctionalFull h (fourierCos h) := by
  -- The zero sequence: imaginary parts of nontrivial zeros from zetaZeroSeq
  refine ⟨fun n => (zetaZeroSeq n).im, ?_, ?_, ?_, ?_⟩
  -- (1) Each valid entry corresponds to a nontrivial zero
  · intro n hn
    obtain ⟨hzero, hre_pos, hre_lt⟩ := zetaZeroSeq_spec n hn
    exact ⟨⟨zetaZeroSeq n, hzero, hre_pos, hre_lt⟩, rfl⟩
  -- (2) Surjectivity: every nontrivial zero is represented
  · intro s hzero hre_pos hre_lt
    obtain ⟨n, hn⟩ := zetaZeroSeq_surj s hzero hre_pos hre_lt
    exact ⟨n, by simp only; rw [hn]⟩
  -- (3) Summability: from decay hypothesis + zero density
  · exact summable_over_zeros h hdecay
  -- (4) The sum equals the Weil functional: the explicit formula identity
  · obtain ⟨cv, hcv_sum, hcv_weil⟩ := sum_over_zeros_eq_contour h hcont hdecay
    rw [hcv_sum, hcv_weil]

end ArithmeticHodge.Analysis
