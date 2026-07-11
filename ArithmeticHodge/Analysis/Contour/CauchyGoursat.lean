/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: Chris Birkbeck
Modified for the ArithmeticHodge namespace and current Mathlib API.
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Cauchy–Goursat for a pole-free meromorphic function

If `A` is meromorphic on a closed disc `C(c, R)` (`R ≥ 0`) and has non-negative meromorphic order at
every point of the disc, then the contour integral of `A` around the boundary circle vanishes:
`∮_{C(c,R)} A = 0`.

This is the pole-free base case shared by the argument principle and the classical residue theorem:
integrating a meromorphic function with no poles inside the disc gives `0`. No pointwise regularity
of the raw function `A` is required — the statement is up to the meromorphic normal form of `A`,
which is genuinely analytic throughout the disc.

## Main result

* `ArithmeticHodge.Analysis.Contour.circleIntegral_eq_zero_of_meromorphicOrderAt_nonneg` — the
  circle integral of a pole-free meromorphic function vanishes.

## Provenance

Ported from TauCeti commit `0c70accf71cf8085ca7661cc7cbf7dd6c2bca7be`, where the proof was
adapted from the AINTLIB `LeanModularForms` generalized residue theory and specialized to circles.
-/

public section

open Metric Complex

namespace ArithmeticHodge.Analysis.Contour

/-- **Cauchy–Goursat for a pole-free meromorphic function.** If `A` is meromorphic on the closed
disc `C(c, R)` (`R ≥ 0`) and has non-negative meromorphic order throughout the disc, then its
circle integral vanishes. -/
lemma circleIntegral_eq_zero_of_meromorphicOrderAt_nonneg {A : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hA : MeromorphicOn A (closedBall c R))
    (hord : ∀ z ∈ closedBall c R, 0 ≤ meromorphicOrderAt A z) :
    circleIntegral A c R = 0 := by
  rcases hR.eq_or_lt with hR0 | hR0
  · rw [← hR0]
    exact circleIntegral.integral_radius_zero A c
  have hB_nf : MeromorphicNFOn (toMeromorphicNFOn A (closedBall c R)) (closedBall c R) :=
    meromorphicNFOn_toMeromorphicNFOn A (closedBall c R)
  have hB_an : AnalyticOnNhd ℂ (toMeromorphicNFOn A (closedBall c R)) (closedBall c R) := by
    intro z hz
    refine (hB_nf hz).meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
    rw [meromorphicOrderAt_toMeromorphicNFOn hA hz]
    exact hord z hz
  have hB0 : circleIntegral (toMeromorphicNFOn A (closedBall c R)) c R = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hR0.le Set.countable_empty
      (fun z hz => (hB_an z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hB_an z (ball_subset_closedBall hz.1)).differentiableAt)
  rw [← hB0]
  refine circleIntegral.circleIntegral_congr_codiscreteWithin ?_ hR0.ne'
  have hspU : sphere c |R| ⊆ closedBall c R := by
    rw [abs_of_pos hR0]
    exact sphere_subset_closedBall
  exact (toMeromorphicNFOn_eqOn_codiscrete hA).filter_mono (Filter.codiscreteWithin.mono hspU)

end ArithmeticHodge.Analysis.Contour
