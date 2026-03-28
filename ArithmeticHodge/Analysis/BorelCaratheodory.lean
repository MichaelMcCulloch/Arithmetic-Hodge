/-
  Borel-Carathéodory theorem

  Re-exports `Complex.borelCaratheodory` and `Complex.borelCaratheodory_zero`
  from Mathlib, plus a convenient closed-disk formulation for use in
  zero-free region and de la Vallée-Poussin estimates.
-/

import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Metric Set

namespace ArithmeticHodge.Analysis

/-! ### Closed-disk formulation

The Mathlib statement uses the open ball `ball 0 R` and strict inequality `(f z).re ≤ M`.
For number-theoretic applications we often know bounds on a closed disk of radius `R` and
want the estimate on a smaller closed disk of radius `r < R`.  The lemma below packages
this up. -/

/-- **Borel-Carathéodory theorem** (closed-disk version).

If `f` is differentiable on the open ball of radius `R`, `Re f(z) ≤ A` for all
`z` with `‖z‖ < R`, and `0 < r < R`, then for every `z` with `‖z‖ ≤ r`:

  `‖f z‖ ≤ 2 * r / (R - r) * A + (R + r) / (R - r) * ‖f 0‖`
-/
theorem borelCaratheodory_closedBall
    {f : ℂ → ℂ} {A R r : ℝ} {z : ℂ}
    (hA : 0 < A)
    (hR : 0 < R)
    (hrR : r < R)
    (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hbound : MapsTo f (ball 0 R) {z | z.re ≤ A})
    (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ 2 * A * r / (R - r) + ‖f 0‖ * (R + r) / (R - r) := by
  have hzR : z ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (hz.trans_lt hrR)
  have h := Complex.borelCaratheodory hA hf hbound hR hzR
  have hRr : 0 < R - r := by linarith
  have hRz : 0 < R - ‖z‖ := by linarith [mem_ball_zero_iff.mp hzR]
  -- ‖z‖ ≤ r  ⟹  the RHS of the Mathlib bound is ≤ the claimed RHS
  calc ‖f z‖
    _ ≤ 2 * A * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := h
    _ ≤ 2 * A * r / (R - r) + ‖f 0‖ * (R + r) / (R - r) := by
        gcongr <;> linarith

end ArithmeticHodge.Analysis
