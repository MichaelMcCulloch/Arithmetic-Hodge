/-
  Logarithmic-derivative form of the zeta functional equation.

  Differentiating `xi(s) = xi(1-s)` makes the two xi logarithmic
  derivatives cancel.  Substitution of the exact zeta/xi gamma-factor
  identity then pairs the negative zeta logarithmic derivatives at `s` and
  `1-s` into the two digamma terms used in the symmetric contour.
-/

import ArithmeticHodge.Analysis.ZetaProduct

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis

/-- The logarithmic derivatives of xi at `s` and `1-s` cancel. -/
theorem xi_logDeriv_one_sub_add (s : ℂ) :
    deriv xiFunction s / xiFunction s +
        deriv xiFunction (1 - s) / xiFunction (1 - s) = 0 := by
  have hinner : HasDerivAt (fun z : ℂ ↦ 1 - z) (-1) s := by
    simpa using
      (hasDerivAt_const (x := s) (c := (1 : ℂ))).sub (hasDerivAt_id s)
  have houter : HasDerivAt xiFunction (deriv xiFunction (1 - s)) (1 - s) :=
    differentiable_xiFunction.differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun z : ℂ ↦ xiFunction (1 - z))
      (deriv xiFunction (1 - s) * (-1)) s :=
    houter.comp s hinner
  have hfun : (fun z : ℂ ↦ xiFunction (1 - z)) = xiFunction := by
    funext z
    exact xiFunction_one_sub z
  have hderiv : deriv xiFunction s = -deriv xiFunction (1 - s) := by
    have hc := hcomp.deriv
    rw [hfun] at hc
    rw [hc]
    ring
  have hvalue : xiFunction (1 - s) = xiFunction s := xiFunction_one_sub s
  rw [hderiv, hvalue]
  ring

/-- Away from zeros and the polar points, the paired negative logarithmic
derivatives of zeta equal the symmetric real-gamma logarithmic derivative.
This is the exact functional-equation identity used to replace a left
vertical contour by a right vertical contour and the archimedean term. -/
theorem neg_zeta_logDeriv_functional_pair
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0)
    (hzetaOneSub : riemannZeta (1 - s) ≠ 0) :
    -(deriv riemannZeta s / riemannZeta s) -
        deriv riemannZeta (1 - s) / riemannZeta (1 - s) =
      -(Real.log Real.pi : ℂ) +
        Complex.digamma (s / 2) / 2 +
        Complex.digamma ((1 - s) / 2) / 2 := by
  have ht0 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have ht1 : 1 - s ≠ 1 := by
    intro h
    apply hs0
    linear_combination -h
  have hs := zeta_logDeriv_from_xi_explicit s hs1 hs0 hzeta
  have ht := zeta_logDeriv_from_xi_explicit (1 - s) ht1 ht0 hzetaOneSub
  have hxi := xi_logDeriv_one_sub_add s
  rw [hs, ht]
  have hp :
      (1 / s + 1 / (s - 1)) +
          (1 / (1 - s) + 1 / ((1 - s) - 1)) = 0 := by
    have hsSub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hOneSub : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
    field_simp [hs0, hs1, hsSub, hOneSub]
    ring
  linear_combination -hxi + hp

end ArithmeticHodge.Analysis
