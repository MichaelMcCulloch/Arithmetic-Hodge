/-
  LAYER 2: The Weil Explicit Formula

  The explicit formula relates a sum over zeta zeros (spectral side)
  to a sum over prime powers plus archimedean corrections (geometric side).

  This is the "duality" between the spectrum of the scaling operator
  and the geometry of the primes. It is the number-theoretic analogue
  of the Selberg trace formula.

  The current theorem is conditional on RH and inherits the unresolved
  Hadamard and contour scaffolds from `ZetaProduct.lean`.
-/

import ArithmeticHodge.Analysis.WeilDefs
import ArithmeticHodge.Analysis.ZetaProduct

open Real MeasureTheory Nat

namespace ArithmeticHodge.Analysis

-- ============================================================
-- The Weil Explicit Formula (THEOREM)
-- ============================================================

/-- **Legacy conditional additive explicit-formula wrapper.**

    For any suitable test function h (Schwartz class, or with sufficient decay),
    the sum of h over the imaginary parts of the nontrivial zeta zeros
    equals the Weil functional evaluated at h and its Fourier cosine transform:

      Σ_ρ h(γ_ρ) = W(h, fourierCos h)

    where ρ ranges over nontrivial zeros of ζ (counted with multiplicity).

    The body delegates to two unresolved production theorems:
    `xi_hadamard_product` and `weil_contour_identity`.  Its provenance field
    says only that every sequence entry comes from some zero; it does not state
    exhaustivity or analytic multiplicity.  It therefore must not be used as
    an axiom-clean explicit formula yet.

    Intended dependency chain:
    1. Analytic continuation of ζ (Mathlib: `completedRiemannZeta₀`)
    2. Hadamard product for ξ (`xi_hadamard_product`)
    3. ζ'/ζ partial fraction expansion (`zeta_logDeriv_partial_fraction`)
    4. Contour integration (`sum_over_zeros_eq_contour`, requires RH)
    5. Summability over zeros (`summable_over_zeros`)

    Note: RH is required because this formulation uses h : ℝ → ℝ evaluated at
    Im(ρ). The spectral parameter γ_ρ = (ρ-1/2)/i is only real when Re(ρ) = 1/2.
    The downstream consumer `rh_implies_weil_positivity_from_explicit` already
    has RH as a hypothesis, so this condition propagates cleanly. -/
theorem weil_explicit_formula
    (h : ℝ → ℝ)
    (hcont : Continuous h)
    (hdecay : ∀ x : ℝ, ‖h x‖ ≤ 1 / (1 + x ^ 2))
    (hRH : RiemannHypothesis) :
    ∃ (zeros : ℕ → ℝ),
      (∀ n, ∃ ρ : NontrivialZetaZero, zeros n = ρ.val.im) ∧
      Summable (fun n => h (zeros n)) ∧
      ∑' n, h (zeros n) = weilFunctionalFull h (fourierCos h) := by
  -- The Hadamard sequence has no dummy entries: every term is a genuine
  -- nontrivial zero and its inverse-square norms form a summable family.
  refine ⟨fun n => (hadamardZeros n).im, ?_, summable_over_zeros h hdecay, ?_⟩
  · intro n
    have hre := hadamardZeros_re n
    exact ⟨⟨hadamardZeros n,
      (xiFunction_zero_iff hre.1 hre.2).mp (hadamardZeros_spec n),
      hre.1, hre.2⟩, rfl⟩
  -- The sum equals the Weil functional by the contour identity.
  · obtain ⟨cv, hcv_sum, hcv_weil⟩ := sum_over_zeros_eq_contour h hcont hdecay hRH
    rw [hcv_sum, hcv_weil]

end ArithmeticHodge.Analysis
