/-
  Helper: Zero summability for finite-order entire functions.

  Extracted to break the circular import:
  Order → ZetaProduct → Hadamard → WeierstraßProduct.
  The sorry corresponds to the same gap as Order.lean:452
  (Jensen's formula + Abel summation chain).
-/

import ArithmeticHodge.Analysis.EntireFunction.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

open Complex

namespace ArithmeticHodge.Analysis.EntireFunction

/-- For a finite-order entire function f with order ρ and genus p = ⌊ρ⌋,
    the series Σ ‖z_n‖^{-(p+1)} converges over the nonzero zeros.

    Proof: Jensen gives n(r) = O(r^{ρ+ε}), Abel summation gives
    convergence for σ = p+1 > ρ. Same content as Order.lean:452. -/
theorem finite_order_zero_summable_floor (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf_ne : ¬ f = 0) (hfin : HasFiniteOrder f) :
    let p := Nat.floor (entireOrder f).toReal
    Summable (fun z : { w : ℂ // f w = 0 ∧ w ≠ 0 } => ‖(z : ℂ)‖⁻¹ ^ ((p : ℝ) + 1)) := by
  sorry

end ArithmeticHodge.Analysis.EntireFunction
