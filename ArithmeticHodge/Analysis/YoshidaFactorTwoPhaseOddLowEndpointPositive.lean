import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddLowSchur

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddLowEndpointPositive

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddFullPolarization
open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddLowSchur
open YoshidaFactorTwoPhaseOddStructuralPerturbation

/-!
# Structural reduction of the odd low endpoint pencil

The signed endpoint problem is kept as a quadratic-form problem on the
intrinsic shifted-Legendre modes `P₁,P₃`.  The correlation entries below
are exact polynomial identities.  In particular, the only remaining analytic
input is positivity of the two complete signed forms; there is no phase grid,
mode cutoff, or finite search hidden in the reduction.
-/

private theorem integral_sextic
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ l r : ℝ) :
    (∫ x : ℝ in l..r,
        a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
          (a₃ * x ^ 3 + (a₄ * x ^ 4 +
            (a₅ * x ^ 5 + a₆ * x ^ 6)))))) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 +
        a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 +
        a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-- Exact centered autocorrelation of the degree-one odd mode. -/
theorem factorTwoCenteredCorrelationBilinear_p1_p1 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredP1 centeredP1 t =
      (t - 2) * (t ^ 2 + 2 * t - 2) / 6 := by
  rw [factorTwoCenteredCorrelationBilinear_self]
  unfold CenteredEndpointCorrelation.centeredEndpointCorrelation centeredP1
  rw [show (fun x : ℝ ↦ (t + x) * x) =
      fun x ↦ 0 * x ^ 0 + (t * x ^ 1 + (1 * x ^ 2 +
        (0 * x ^ 3 + (0 * x ^ 4 + (0 * x ^ 5 + 0 * x ^ 6))))) by
    funext x
    ring,
    integral_sextic]
  ring

/-- Exact centered polarization between the degree-one and degree-three odd
modes. -/
theorem factorTwoCenteredCorrelationBilinear_p1_p3 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredP1 centeredP3 t =
      t * (t - 2) * (t ^ 3 + 2 * t ^ 2 - 8 * t + 4) / 8 := by
  unfold factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation centeredP1 centeredP3
  rw [show (fun x : ℝ ↦
      (t + x) * ((5 * x ^ 3 - 3 * x) / 2)) =
      fun x ↦ 0 * x ^ 0 + ((-(3 : ℝ) * t / 2) * x ^ 1 +
        ((-3 / 2 : ℝ) * x ^ 2 + ((5 * t / 2 : ℝ) * x ^ 3 +
          ((5 / 2 : ℝ) * x ^ 4 + (0 * x ^ 5 + 0 * x ^ 6))))) by
    funext x
    ring,
    integral_sextic]
  rw [show (fun x : ℝ ↦
      ((5 * (t + x) ^ 3 - 3 * (t + x)) / 2) * x) =
      fun x ↦ 0 * x ^ 0 + (((5 * t ^ 3 - 3 * t) / 2) * x ^ 1 +
        (((15 * t ^ 2 - 3) / 2) * x ^ 2 +
          ((15 * t / 2 : ℝ) * x ^ 3 +
            ((5 / 2 : ℝ) * x ^ 4 + (0 * x ^ 5 + 0 * x ^ 6))))) by
    funext x
    ring,
    integral_sextic]
  ring

/-- Exact centered autocorrelation of the degree-three odd mode. -/
theorem factorTwoCenteredCorrelationBilinear_p3_p3 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredP3 centeredP3 t =
      (t - 2) *
        (5 * t ^ 6 + 10 * t ^ 5 - 22 * t ^ 4 - 44 * t ^ 3 +
          24 * t ^ 2 + 48 * t - 16) / 112 := by
  rw [factorTwoCenteredCorrelationBilinear_self]
  unfold CenteredEndpointCorrelation.centeredEndpointCorrelation centeredP3
  rw [show (fun x : ℝ ↦
      ((5 * (t + x) ^ 3 - 3 * (t + x)) / 2) *
        ((5 * x ^ 3 - 3 * x) / 2)) =
      fun x ↦ 0 * x ^ 0 +
        (((-15 * t ^ 3 + 9 * t) / 4) * x ^ 1 +
          (((-45 * t ^ 2 + 9) / 4) * x ^ 2 +
            (((25 * t ^ 3 - 60 * t) / 4) * x ^ 3 +
              (((75 * t ^ 2 - 30) / 4) * x ^ 4 +
                ((75 * t / 4 : ℝ) * x ^ 5 +
                  (25 / 4 : ℝ) * x ^ 6))))) by
    funext x
    ring,
    integral_sextic]
  ring

/-! ## Exact perturbation entries -/

theorem factorTwoCenteredSymmetricPerturbation_p1_eq :
    factorTwoCenteredSymmetricPerturbation centeredP1 =
      yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoSymmetricWeight (yoshidaEndpointA * t) *
              ((t - 2) * (t ^ 2 + 2 * t - 2) / 6)) -
        (Real.log 2 / Real.sqrt 2) * (2 / 3) -
        (Real.log 3 / Real.sqrt 3) *
          ((factorTwoPrimeShift / yoshidaEndpointA - 2) *
            ((factorTwoPrimeShift / yoshidaEndpointA) ^ 2 +
              2 * (factorTwoPrimeShift / yoshidaEndpointA) - 2) / 6) := by
  rw [← factorTwoCenteredSymmetricPerturbationBilinear_self]
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_p1_p1]
  norm_num

theorem factorTwoCenteredSymmetricPerturbationBilinear_p1_p3_eq :
    factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3 =
      yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoSymmetricWeight (yoshidaEndpointA * t) *
              (t * (t - 2) * (t ^ 3 + 2 * t ^ 2 - 8 * t + 4) / 8)) -
        (Real.log 3 / Real.sqrt 3) *
          ((factorTwoPrimeShift / yoshidaEndpointA) *
            (factorTwoPrimeShift / yoshidaEndpointA - 2) *
            ((factorTwoPrimeShift / yoshidaEndpointA) ^ 3 +
              2 * (factorTwoPrimeShift / yoshidaEndpointA) ^ 2 -
              8 * (factorTwoPrimeShift / yoshidaEndpointA) + 4) / 8) := by
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_p1_p3]
  norm_num

theorem factorTwoCenteredSymmetricPerturbation_p3_eq :
    factorTwoCenteredSymmetricPerturbation centeredP3 =
      yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoSymmetricWeight (yoshidaEndpointA * t) *
              ((t - 2) *
                (5 * t ^ 6 + 10 * t ^ 5 - 22 * t ^ 4 - 44 * t ^ 3 +
                  24 * t ^ 2 + 48 * t - 16) / 112)) -
        (Real.log 2 / Real.sqrt 2) * (2 / 7) -
        (Real.log 3 / Real.sqrt 3) *
          ((factorTwoPrimeShift / yoshidaEndpointA - 2) *
            (5 * (factorTwoPrimeShift / yoshidaEndpointA) ^ 6 +
              10 * (factorTwoPrimeShift / yoshidaEndpointA) ^ 5 -
              22 * (factorTwoPrimeShift / yoshidaEndpointA) ^ 4 -
              44 * (factorTwoPrimeShift / yoshidaEndpointA) ^ 3 +
              24 * (factorTwoPrimeShift / yoshidaEndpointA) ^ 2 +
              48 * (factorTwoPrimeShift / yoshidaEndpointA) - 16) / 112) := by
  rw [← factorTwoCenteredSymmetricPerturbationBilinear_self]
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_p3_p3]
  norm_num

/-! ## The two structural endpoint obligations -/

/-- The coefficient pencil at any real sign is exactly the complete clean
quadratic plus that sign times the complete symmetric perturbation. -/
theorem factorTwoOddStructuralPhaseLow_quadratic
    (sigma c d : ℝ) :
    factorTwoOddStructuralPhaseLow11 sigma * c ^ 2 +
        2 * factorTwoOddStructuralPhaseLow13 sigma * c * d +
        factorTwoOddStructuralPhaseLow33 sigma * d ^ 2 =
      yoshidaEndpointOddCleanQuadratic
          (factorTwoOddStructuralLowProfile c d) +
        sigma * factorTwoCenteredSymmetricPerturbation
          (factorTwoOddStructuralLowProfile c d) := by
  rw [yoshidaEndpointOddLowGram_quadratic,
    factorTwoCenteredSymmetricPerturbation_oddStructuralLow]
  unfold factorTwoOddStructuralPhaseLow11
    factorTwoOddStructuralPhaseLow13 factorTwoOddStructuralPhaseLow33
  ring

/-- The four scalar endpoint hypotheses are equivalent to two intrinsic
strict quadratic-form inequalities.  This is the exact analytic boundary:
the current general odd estimates do not prove either signed inequality after
discarding the `P₁/P₃` orientation. -/
theorem factorTwoOddStructuralPhaseLow_endpoint_hypotheses_iff_signed_forms :
    (0 < factorTwoOddStructuralPhaseLow11 1 ∧
        0 < factorTwoOddStructuralPhaseLow11 1 *
            factorTwoOddStructuralPhaseLow33 1 -
          factorTwoOddStructuralPhaseLow13 1 ^ 2 ∧
      0 < factorTwoOddStructuralPhaseLow11 (-1) ∧
        0 < factorTwoOddStructuralPhaseLow11 (-1) *
            factorTwoOddStructuralPhaseLow33 (-1) -
          factorTwoOddStructuralPhaseLow13 (-1) ^ 2) ↔
      ((∀ c d : ℝ, c ≠ 0 ∨ d ≠ 0 →
          0 < yoshidaEndpointOddCleanQuadratic
                (factorTwoOddStructuralLowProfile c d) +
              factorTwoCenteredSymmetricPerturbation
                (factorTwoOddStructuralLowProfile c d)) ∧
        (∀ c d : ℝ, c ≠ 0 ∨ d ≠ 0 →
          0 < yoshidaEndpointOddCleanQuadratic
                (factorTwoOddStructuralLowProfile c d) -
              factorTwoCenteredSymmetricPerturbation
                (factorTwoOddStructuralLowProfile c d))) := by
  constructor
  · rintro ⟨hp11, hpdet, hm11, hmdet⟩
    constructor
    · intro c d hne
      have h := real_twoByTwo_quadratic_pos _ _ _ c d hp11 hpdet hne
      rw [factorTwoOddStructuralPhaseLow_quadratic] at h
      simpa only [one_mul] using h
    · intro c d hne
      rw [show yoshidaEndpointOddCleanQuadratic
            (factorTwoOddStructuralLowProfile c d) -
            factorTwoCenteredSymmetricPerturbation
              (factorTwoOddStructuralLowProfile c d) =
          yoshidaEndpointOddCleanQuadratic
              (factorTwoOddStructuralLowProfile c d) +
            (-1 : ℝ) * factorTwoCenteredSymmetricPerturbation
              (factorTwoOddStructuralLowProfile c d) by ring,
        ← factorTwoOddStructuralPhaseLow_quadratic (-1) c d]
      exact real_twoByTwo_quadratic_pos _ _ _ c d hm11 hmdet hne
  · rintro ⟨hplus, hminus⟩
    have hpquad (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
        0 < factorTwoOddStructuralPhaseLow11 1 * c ^ 2 +
          2 * factorTwoOddStructuralPhaseLow13 1 * c * d +
          factorTwoOddStructuralPhaseLow33 1 * d ^ 2 := by
      rw [factorTwoOddStructuralPhaseLow_quadratic]
      simpa using hplus c d hne
    have hmquad (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
        0 < factorTwoOddStructuralPhaseLow11 (-1) * c ^ 2 +
          2 * factorTwoOddStructuralPhaseLow13 (-1) * c * d +
          factorTwoOddStructuralPhaseLow33 (-1) * d ^ 2 := by
      rw [factorTwoOddStructuralPhaseLow_quadratic]
      simpa only [neg_mul, one_mul] using hminus c d hne
    have hp := real_twoByTwo_coefficients_pos_of_quadratic_pos
      _ _ _ hpquad
    have hm := real_twoByTwo_coefficients_pos_of_quadratic_pos
      _ _ _ hmquad
    exact ⟨hp.1, hp.2, hm.1, hm.2⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddLowEndpointPositive
