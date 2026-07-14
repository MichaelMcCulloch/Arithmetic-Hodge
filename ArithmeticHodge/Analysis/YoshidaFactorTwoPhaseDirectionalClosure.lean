import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDirectionalBudget
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailCoercivity

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDirectionalClosure

noncomputable section

open YoshidaEndpointScaledCorrelation
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseDirectionalBudget
open YoshidaFactorTwoPhaseTailCoercivity

/-!
# Directional closure of the factor-two phase pencil

The total even--odd pencil needs only asymmetric one-sided estimates.  This
module transports the existing tail coercivities and feeds those estimates
directly to the exact directional budget.
-/

/-- Endpoint-tail phase positivity from one-sided symmetric-channel bounds.
Unlike the older blockwise closure, the even lower hypothesis is only `-3E`
and the other three sides retain their sharper natural constants. -/
theorem endpoint_tail_phase_uniform_of_directional_bounds
    (re ro : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (heTail : re ∈ yoshidaPeriodicCoreEvenTailSubmodule
      yoshidaEndpointA_pos 199)
    (hoTail : ro ∈ yoshidaPeriodicCoreOddTailSubmodule
      yoshidaEndpointA_pos 10)
    (heReal : ∀ x : ℝ,
      ((re : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hoReal : ∀ x : ℝ,
      ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (heNeg : (re : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0)
    (hePos : (re : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0)
    (hoNeg : (ro : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0)
    (hoPos : (ro : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0)
    (hPeLower :
      let e := centeredRescale yoshidaEndpointA (fun x ↦
        ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re);
      -(3 : ℝ) * (∫ x : ℝ in -1..1, e x ^ 2) ≤
        factorTwoCenteredSymmetricPerturbation e)
    (hPeUpper :
      let e := centeredRescale yoshidaEndpointA (fun x ↦
        ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re);
      factorTwoCenteredSymmetricPerturbation e ≤
        ∫ x : ℝ in -1..1, e x ^ 2)
    (hPoLower :
      let o := centeredRescale yoshidaEndpointA (fun x ↦
        ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re);
      -(∫ x : ℝ in -1..1, o x ^ 2) ≤
        factorTwoCenteredSymmetricPerturbation o)
    (hPoUpper :
      let o := centeredRescale yoshidaEndpointA (fun x ↦
        ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re);
      factorTwoCenteredSymmetricPerturbation o ≤
        (3 / 2 : ℝ) * ∫ x : ℝ in -1..1, o x ^ 2)
    (hJ :
      let e := centeredRescale yoshidaEndpointA (fun x ↦
        ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re);
      let o := centeredRescale yoshidaEndpointA (fun x ↦
        ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re);
      factorTwoCenteredAlternatingCoupling e o ^ 2 ≤
        (625 / 64 : ℝ) *
          (∫ x : ℝ in -1..1, e x ^ 2) *
          (∫ x : ℝ in -1..1, o x ^ 2))
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let e := centeredRescale yoshidaEndpointA (fun x ↦
      ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re);
    let o := centeredRescale yoshidaEndpointA (fun x ↦
      ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re);
    0 ≤ yoshidaEndpointOddCleanQuadratic e +
        yoshidaEndpointOddCleanQuadratic o +
      a * (factorTwoCenteredSymmetricPerturbation e +
        factorTwoCenteredSymmetricPerturbation o) +
      b * factorTwoCenteredAlternatingCoupling e o := by
  dsimp only at hPeLower hPeUpper hPoLower hPoUpper hJ ⊢
  let e : ℝ → ℝ := centeredRescale yoshidaEndpointA (fun x ↦
    ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re)
  let o : ℝ → ℝ := centeredRescale yoshidaEndpointA (fun x ↦
    ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re)
  let Ee : ℝ := ∫ x : ℝ in -1..1, e x ^ 2
  let Eo : ℝ := ∫ x : ℝ in -1..1, o x ^ 2
  have hEe : 0 ≤ Ee := by
    dsimp only [Ee]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ ↦ sq_nonneg (e x))
  have hEo : 0 ≤ Eo := by
    dsimp only [Eo]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ ↦ sq_nonneg (o x))
  have hQe : (102 / 25 : ℝ) * Ee ≤
      yoshidaEndpointOddCleanQuadratic e := by
    simpa only [e, Ee] using evenTail_endpoint_clean_coercive
      re heTail heReal heNeg hePos
  have hQo : (38 / 25 : ℝ) * Eo ≤
      yoshidaEndpointOddCleanQuadratic o := by
    simpa only [o, Eo] using oddTail_endpoint_clean_coercive
      ro hoTail hoReal hoNeg hoPos
  apply phase_uniform_of_directional_tail_bounds
    Ee Eo
    (yoshidaEndpointOddCleanQuadratic e)
    (yoshidaEndpointOddCleanQuadratic o)
    (factorTwoCenteredSymmetricPerturbation e)
    (factorTwoCenteredSymmetricPerturbation o)
    (factorTwoCenteredAlternatingCoupling e o)
    a b hEe hEo hQe hQo
  · simpa only [e, Ee] using hPeLower
  · simpa only [e, Ee] using hPeUpper
  · simpa only [o, Eo] using hPoLower
  · simpa only [o, Eo] using hPoUpper
  · simpa only [e, o, Ee, Eo] using hJ
  · exact hphase

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDirectionalClosure
