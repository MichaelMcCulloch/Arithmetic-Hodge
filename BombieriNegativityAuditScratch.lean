import ArithmeticHodge.Analysis.FourierTransform

/-!
# Audit of `bombieriAutocorrelation_weil_neg`

This file deliberately does not use the unresolved theorem.  It records the
actual information carried by its conclusion and reduces the missing sign to
an explicit inequality between the three implemented Weil-functional terms.
-/

open MeasureTheory Real Complex

namespace ArithmeticHodge.Analysis

/-- The scalar sign assertion hidden inside
`bombieriAutocorrelation_weil_neg`. -/
def BombieriGaussianNegative (sigma : ℝ) : Prop :=
  weilFunctionalFull (bombieriAutocorrelation sigma)
      (fourierCos (bombieriAutocorrelation sigma)) < 0

/-- The target theorem's conclusion remembers only the real part of the zero.
It contains neither its imaginary part nor its proof of being a zeta zero. -/
theorem bombieri_negativity_target_is_scalar (rho : NontrivialZetaZero) :
    (weilFunctionalFull (bombieriAutocorrelation rho.val.re)
        (fourierCos (bombieriAutocorrelation rho.val.re)) < 0) ↔
      BombieriGaussianNegative rho.val.re :=
  Iff.rfl

/-- Any independently proved scalar sign can be transported to every zero
with that real part.  No zeta-zero fact or height enters the argument. -/
theorem bombieri_negativity_transport
    (sigma : ℝ) (hnegative : BombieriGaussianNegative sigma)
    (rho : NontrivialZetaZero) (hre : rho.val.re = sigma) :
    weilFunctionalFull (bombieriAutocorrelation rho.val.re)
        (fourierCos (bombieriAutocorrelation rho.val.re)) < 0 := by
  simpa only [hre] using hnegative

/-- Even the complete numerical candidate value cannot distinguish two zeta
zeros at different heights when their real parts agree. -/
theorem bombieriWeilValue_eq_of_zero_re_eq
    (rho tau : NontrivialZetaZero) (hre : rho.val.re = tau.val.re) :
    weilFunctionalFull (bombieriAutocorrelation rho.val.re)
        (fourierCos (bombieriAutocorrelation rho.val.re)) =
      weilFunctionalFull (bombieriAutocorrelation tau.val.re)
        (fourierCos (bombieriAutocorrelation tau.val.re)) := by
  rw [hre]

/-- An off-critical-line nontrivial zero refutes RH directly.  In particular,
the current `weil_explicit_formula`, whose final argument is RH, is unavailable
in exactly the case where the missing negativity theorem is meant to run. -/
theorem not_riemannHypothesis_of_nontrivial_zero_off_line
    (rho : NontrivialZetaZero) (hoff : rho.val.re ≠ 1 / 2) :
    ¬RiemannHypothesis := by
  intro hRH
  apply hoff
  apply hRH rho.val rho.is_zero
  · rintro ⟨n, hn⟩
    have hre := rho.re_pos
    rw [hn] at hre
    norm_num [Complex.mul_re, Complex.add_re] at hre
    have hn_nonnegative : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · intro hone
    have hre := rho.re_lt_one
    rw [hone] at hre
    norm_num at hre

/-- Reflecting the parameter across the critical line does not change the
modulated Gaussian. -/
theorem bombieriTestFn_one_sub (sigma : ℝ) :
    bombieriTestFn (1 - sigma) = bombieriTestFn sigma := by
  funext x
  unfold bombieriTestFn
  congr 1
  rw [show 2 * Real.pi * (1 - sigma - 1 / 2) * x =
      -(2 * Real.pi * (sigma - 1 / 2) * x) by ring]
  exact Real.cos_neg _

/-- Consequently the autocorrelation also depends only on the unsigned
distance from the critical line. -/
theorem bombieriAutocorrelation_one_sub (sigma : ℝ) :
    bombieriAutocorrelation (1 - sigma) = bombieriAutocorrelation sigma := by
  unfold bombieriAutocorrelation
  rw [bombieriTestFn_one_sub]

/-- The complete implemented Weil value is invariant under the same
reflection. -/
theorem bombieriWeilValue_one_sub (sigma : ℝ) :
    weilFunctionalFull (bombieriAutocorrelation (1 - sigma))
        (fourierCos (bombieriAutocorrelation (1 - sigma))) =
      weilFunctionalFull (bombieriAutocorrelation sigma)
        (fourierCos (bombieriAutocorrelation sigma)) := by
  rw [bombieriAutocorrelation_one_sub]

theorem bombieriGaussianNegative_one_sub (sigma : ℝ) :
    BombieriGaussianNegative (1 - sigma) ↔
      BombieriGaussianNegative sigma := by
  unfold BombieriGaussianNegative
  rw [bombieriWeilValue_one_sub]

/-- The proved Fourier fact has the opposite logical shape from the missing
claim: the transform of every member of the candidate family is nonnegative.
It supplies no sign for the full Weil functional. -/
theorem bombieriAutocorrelation_fourier_nonnegative (sigma xi : ℝ) :
    0 ≤ fourierCos (bombieriAutocorrelation sigma) xi := by
  exact fourierCos_autocorrelation_nonneg
    (bombieriTestFn sigma)
    (bombieriTestFn_integrable sigma)
    (bombieriTestFn_sq_integrable sigma)
    (bombieriAutocorrelation sigma)
    (fun _ ↦ rfl)
    xi

/-- Exact structural reduction of the unresolved sign.  The missing theorem
must prove that the prime term dominates the polar and implemented
archimedean terms.  None of the fields of a zeta zero occurs in this
inequality. -/
theorem bombieriGaussianNegative_iff_component_inequality (sigma : ℝ) :
    BombieriGaussianNegative sigma ↔
      weilPolar
          (fourierCos (bombieriAutocorrelation sigma) 0)
          (fourierCos (bombieriAutocorrelation sigma) 1) +
          weilArchimedean (fourierCos (bombieriAutocorrelation sigma)) <
        -weilPrimeTerm (bombieriAutocorrelation sigma) := by
  unfold BombieriGaussianNegative weilFunctionalFull
  constructor <;> intro h <;> linarith

/-- Strongest unconditional replacement available from the current API: a
component inequality proves the candidate sign.  The off-critical-line
hypothesis is not a substitute for this missing analytic estimate. -/
theorem bombieriAutocorrelation_weil_neg_of_component_inequality
    (rho : NontrivialZetaZero)
    (hcomponents :
      weilPolar
          (fourierCos (bombieriAutocorrelation rho.val.re) 0)
          (fourierCos (bombieriAutocorrelation rho.val.re) 1) +
          weilArchimedean (fourierCos (bombieriAutocorrelation rho.val.re)) <
        -weilPrimeTerm (bombieriAutocorrelation rho.val.re)) :
    weilFunctionalFull (bombieriAutocorrelation rho.val.re)
        (fourierCos (bombieriAutocorrelation rho.val.re)) < 0 :=
  (bombieriGaussianNegative_iff_component_inequality rho.val.re).2 hcomponents

#print axioms bombieri_negativity_target_is_scalar
#print axioms bombieri_negativity_transport
#print axioms bombieriWeilValue_eq_of_zero_re_eq
#print axioms not_riemannHypothesis_of_nontrivial_zero_off_line
#print axioms bombieriTestFn_one_sub
#print axioms bombieriAutocorrelation_one_sub
#print axioms bombieriWeilValue_one_sub
#print axioms bombieriGaussianNegative_one_sub
#print axioms bombieriAutocorrelation_fourier_nonnegative
#print axioms bombieriGaussianNegative_iff_component_inequality
#print axioms bombieriAutocorrelation_weil_neg_of_component_inequality
#print axioms bombieriAutocorrelation_weil_neg

end ArithmeticHodge.Analysis
