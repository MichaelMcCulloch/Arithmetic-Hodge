/-
  LAYER 1a: Poisson Summation Formula

  The Poisson summation formula is the bridge between the additive
  self-duality of ℤ ⊂ ℝ and the functional equation of ζ.

  Statement: For f in the Schwartz space of ℝ,
    Σ_{n ∈ ℤ} f(x+n) = Σ_{n ∈ ℤ} 𝓕 f(n) · e^{2πinx}

  GOOD NEWS: Mathlib already has this as `SchwartzMap.tsum_eq_tsum_fourier`
  in `Mathlib.Analysis.Fourier.PoissonSummation`. We wrap it here.

  This is where the 1/2 is BORN: the self-duality of the lattice ℤ
  under Pontryagin/Fourier duality creates the symmetry axis at Re(s) = 1/2.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open scoped SchwartzMap FourierTransform
open MeasureTheory Complex

namespace ArithmeticHodge.Analysis

/-- **Poisson Summation Formula for Schwartz functions.**

    For any Schwartz function f : ℝ → ℂ and any x ∈ ℝ,
      Σ_{n ∈ ℤ} f(x + n) = Σ_{n ∈ ℤ} 𝓕 f(n) · e^{2πinx}

    This encodes the self-duality of ℤ ⊂ ℝ under Pontryagin duality.

    SORRY COUNT: 0 — this is PROVED in Mathlib.
    Mathlib reference: `SchwartzMap.tsum_eq_tsum_fourier` -/
theorem poisson_summation (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ∑' n : ℤ, f (x + n) =
    ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle) :=
  SchwartzMap.tsum_eq_tsum_fourier f x

/-- Poisson summation at x = 0: the classical form. -/
theorem poisson_summation_zero (f : 𝓢(ℝ, ℂ)) :
    ∑' n : ℤ, f (↑n : ℝ) =
    ∑' n : ℤ, 𝓕 f n * fourier n (0 : UnitAddCircle) := by
  have h := poisson_summation f 0
  simp only [zero_add] at h
  exact h

end ArithmeticHodge.Analysis
