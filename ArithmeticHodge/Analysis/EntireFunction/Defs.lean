/-
  Shared definitions for entire function theory.

  These definitions are used by both Order.lean and WeierstraßProduct.lean,
  extracted here to break an import cycle:
    WeierstraßProduct → Order → ZetaProduct → Hadamard → WeierstraßProduct
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic

open Complex Filter Topology Real

namespace ArithmeticHodge.Analysis.EntireFunction

-- ============================================================
-- Maximum Modulus and Order
-- ============================================================

/-- The maximum modulus function M(f, r) = sup_{|z|≤r} |f(z)|.
    For an entire function, this is always finite for finite r. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ (z : ℂ) (_ : ‖z‖ ≤ r), ‖f z‖

/-- The order of an entire function f, defined as
    ρ(f) = lim sup_{r→∞} log log M(f,r) / log r

    This measures the growth rate: f grows roughly like exp(r^ρ).
    - Polynomials have order 0
    - exp(z) has order 1
    - exp(exp(z)) has infinite order -/
noncomputable def entireOrder (f : ℂ → ℂ) : EReal :=
  Filter.limsup (fun r : ℝ => (Real.log (Real.log (maxModulus f r)) / Real.log r : ℝ)) Filter.atTop

/-- An entire function has finite order if its order is not +∞. -/
def HasFiniteOrder (f : ℂ → ℂ) : Prop :=
  entireOrder f < ⊤

end ArithmeticHodge.Analysis.EntireFunction
