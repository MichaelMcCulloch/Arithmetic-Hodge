/-
  Shared definitions for the Weil explicit formula framework.

  Contains:
  - NontrivialZetaZero structure
  - Fourier cosine transform
  - Weil functional components (prime term, archimedean, polar)
  - WeilFunctionalFull

  These are imported by both WeilExplicit.lean (the theorem) and
  ZetaProduct.lean (the Hadamard product infrastructure).
-/

import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open Real MeasureTheory Nat

namespace ArithmeticHodge.Analysis

-- ============================================================
-- Nontrivial Zeta Zeros
-- ============================================================

/-- A nontrivial zero of the Riemann zeta function.
    These are zeros ρ with 0 < Re(ρ) < 1 (in the critical strip).
    The Riemann Hypothesis asserts they all have Re(ρ) = 1/2. -/
structure NontrivialZetaZero where
  /-- The zero in ℂ -/
  val : ℂ
  /-- It is a zero of ζ -/
  is_zero : riemannZeta val = 0
  /-- It is in the critical strip -/
  re_pos : 0 < val.re
  re_lt_one : val.re < 1

/-- RH is equivalent to: every nontrivial zero has Re = 1/2. -/
def RH_via_zeros : Prop :=
  ∀ ρ : NontrivialZetaZero, ρ.val.re = 1 / 2

-- ============================================================
-- Components of the Weil Functional
-- ============================================================

/-- The prime (multiplicative) term of the Weil functional:
    W_primes(f) = -Σ_p prime Σ_{m≥1} (log p / p^{m/2}) · [f(m log p) + f(-m log p)]

    This sums over all prime powers, weighted by log(p)/p^{m/2}.
    It encodes the multiplicative structure of ℤ. -/
noncomputable def weilPrimeTerm (f : ℝ → ℝ) : ℝ :=
  -∑' (p : Nat.Primes), ∑' (m : ℕ),
    (Real.log (p : ℝ) / (p : ℝ) ^ ((m + 1 : ℝ) / 2)) *
    (f ((m + 1) * Real.log (p : ℝ)) + f (-((m + 1) * Real.log (p : ℝ))))

/-- The archimedean kernel Ω(t) = Re[Γ'(1/4 + it/2) / Γ(1/4 + it/2)] + log π.

    This encodes the contribution of the archimedean place (ℝ) to the
    explicit formula. The digamma function Ψ = Γ'/Γ appears because
    the local zeta factor at infinity is π^{-s/2} Γ(s/2). -/
noncomputable def archimedeanKernel (t : ℝ) : ℝ :=
  (Complex.log (Complex.Gamma (1/4 + Complex.I * t/2))).re + Real.log π

/-- The archimedean (additive) term of the Weil functional:
    W_arch(f) = (1/2π) ∫ f̂(t) Ω(t) dt -/
noncomputable def weilArchimedean (fHat : ℝ → ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t : ℝ, fHat t * archimedeanKernel t

/-- The polar (blanket) term of the Weil functional:
    W_polar(f) = f̂(0) + f̂(1) -/
noncomputable def weilPolar (fHat_zero fHat_one : ℝ) : ℝ :=
  fHat_zero + fHat_one

/-- The Weil functional without archimedean term. -/
noncomputable def weilFunctional (f : ℝ → ℝ) (fHat_zero fHat_one : ℝ) : ℝ :=
  weilPolar fHat_zero fHat_one + weilPrimeTerm f

/-- The complete Weil functional with all three terms. -/
noncomputable def weilFunctionalFull (f fHat : ℝ → ℝ) : ℝ :=
  weilPolar (fHat 0) (fHat 1) + weilArchimedean fHat + weilPrimeTerm f

-- ============================================================
-- Fourier Cosine Transform
-- ============================================================

/-- The Fourier cosine transform: fourierCos f ξ = ∫ f(x) cos(2πξx) dx. -/
noncomputable def fourierCos (f : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ x : ℝ, f x * Real.cos (2 * Real.pi * ξ * x)

-- ============================================================
-- Autocorrelations
-- ============================================================

/-- A function f : ℝ → ℝ is an autocorrelation if f = g ∗ g̃ for some g. -/
def IsAutocorrelation (f : ℝ → ℝ) : Prop :=
  ∃ g : ℝ → ℝ, Integrable g volume ∧
    ∀ x : ℝ, f x = ∫ y : ℝ, g y * g (y + x) ∂volume

-- ============================================================
-- Weil Positivity Predicate
-- ============================================================

/-- **Weil positivity on autocorrelations.**
    The Weil functional W(f) is non-negative when evaluated on
    autocorrelation test functions f = g ∗ g̃.
    This is equivalent to the Riemann Hypothesis (Weil, 1952). -/
def WeilPositivity : Prop :=
  ∀ (f : ℝ → ℝ), IsAutocorrelation f →
    Continuous f →
    (∀ x : ℝ, ‖f x‖ ≤ 1 / (1 + x ^ 2)) →
    0 ≤ weilFunctionalFull f (fourierCos f)

end ArithmeticHodge.Analysis
