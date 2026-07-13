import ArithmeticHodge.Analysis.YoshidaCriticalLogCorrelation
import ArithmeticHodge.Analysis.YoshidaFactorTwoMomentFormula

set_option autoImplicit false

open Complex Real
open scoped ArithmeticFunction

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeCorrelationSymbol

noncomputable section

open MultiplicativeWeil
open YoshidaCriticalLogCorrelation
open YoshidaFactorTwoCrossDistribution

/-!
# The two prime atoms in critical logarithmic correlation coordinates

This places the `p = 2, 3` terms in the same orientation as the exact
archimedean moment formula.  No prime table is evaluated: the only inputs are
the prime-value theorem for von Mangoldt and the critical log/dilation
isometry.
-/

def factorTwoPrimeCorrelationSymbol (g : BombieriTest) : ℂ :=
  (((Real.log 2 / Real.sqrt 2 : ℝ) : ℂ) *
      factorTwoSelfCorrelation g 0) +
    (((Real.log 3 / Real.sqrt 3 : ℝ) : ℂ) *
      factorTwoSelfCorrelation g (Real.log (3 / 2 : ℝ)))

theorem factorTwoPrimeCrossSymbol_eq_correlation
    (g : BombieriTest) :
    factorTwoPrimeCrossSymbol g = factorTwoPrimeCorrelationSymbol g := by
  have hone := star_quadratic_eq_inv_sqrt_mul_selfCorrelation
    g 1 (by norm_num : (0 : ℝ) < 1)
  have hone' :
      starRingEnd ℂ (bombieriQuadraticTest g 1) =
        factorTwoSelfCorrelation g 0 := by
    calc
      starRingEnd ℂ (bombieriQuadraticTest g 1) =
          (((Real.sqrt 1)⁻¹ : ℝ) : ℂ) *
            factorTwoSelfCorrelation g (Real.log 1) := hone
      _ = factorTwoSelfCorrelation g 0 := by norm_num
  have hthree := star_quadratic_eq_inv_sqrt_mul_selfCorrelation
    g (3 / 2 : ℝ) (by norm_num : (0 : ℝ) < 3 / 2)
  have hsqrt :
      Real.sqrt 2 * Real.sqrt (3 / 2 : ℝ) = Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hroot2 : Real.sqrt 2 ≠ 0 := by positivity
  have hrootThreeHalves : Real.sqrt (3 / 2 : ℝ) ≠ 0 := by positivity
  have hroot3 : Real.sqrt 3 ≠ 0 := by positivity
  have hcoef :
      (Real.sqrt 2)⁻¹ * (Real.sqrt (3 / 2 : ℝ))⁻¹ =
        (Real.sqrt 3)⁻¹ := by
    field_simp [hroot2, hrootThreeHalves, hroot3]
    exact hsqrt.symm
  have hcoefC :
      ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
        (((Real.sqrt (3 * 2⁻¹ : ℝ) : ℝ) : ℂ)⁻¹)) =
        (((Real.sqrt 3 : ℝ) : ℂ)⁻¹) := by
    have harg : (3 * 2⁻¹ : ℝ) = 3 / 2 := by norm_num
    rw [harg]
    exact_mod_cast hcoef
  unfold factorTwoPrimeCrossSymbol factorTwoPrimeCorrelationSymbol
  rw [ArithmeticFunction.vonMangoldt_apply_prime
      (by norm_num : Nat.Prime 2),
    ArithmeticFunction.vonMangoldt_apply_prime
      (by norm_num : Nat.Prime 3),
    hone', hthree]
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  calc
    _ = ((Real.log 2 : ℝ) : ℂ) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
          factorTwoSelfCorrelation g 0 +
        ((Real.log 3 : ℝ) : ℂ) *
          (((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
            (((Real.sqrt (3 * 2⁻¹ : ℝ) : ℝ) : ℂ)⁻¹)) *
            factorTwoSelfCorrelation g (Real.log (3 * 2⁻¹ : ℝ))) := by
      ring
    _ = ((Real.log 2 : ℝ) : ℂ) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
          factorTwoSelfCorrelation g 0 +
        ((Real.log 3 : ℝ) : ℂ) *
          ((((Real.sqrt 3 : ℝ) : ℂ)⁻¹) *
            factorTwoSelfCorrelation g (Real.log (3 * 2⁻¹ : ℝ))) := by
      rw [hcoefC]
    _ = _ := by ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeCorrelationSymbol
