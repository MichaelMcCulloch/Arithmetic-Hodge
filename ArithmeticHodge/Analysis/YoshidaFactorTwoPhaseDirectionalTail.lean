import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDirectionalClosure
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenSchurClosure
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddSymmetricBound
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRadiusClosure

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDirectionalTail

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointEvenTailReserve
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseAlternatingCoercivity
open YoshidaFactorTwoPhaseDirectionalClosure
open YoshidaFactorTwoPhaseEvenSchurClosure
open YoshidaFactorTwoPhaseEvenSymmetricBound
open YoshidaFactorTwoPhaseOddSymmetricBound
open YoshidaFactorTwoPhaseRadiusClosure
open YoshidaFactorTwoPhaseTailCoercivity
open YoshidaEvenHomogeneousCoercivity
open YoshidaOddSpectralMassBridge

/-!
# Unconditional endpoint-tail directional closure

The coupled directional budget does not need the former absolute `3 / 2`
bound on the even symmetric channel.  The complete infinite Schur estimate
supplies its weaker lower side, while the rank expansion supplies the upper
side; the odd and alternating bounds were already closed structurally.
-/

/-- The complete even--odd endpoint-tail phase pencil is unconditionally
nonnegative throughout the closed unit phase disk. -/
theorem endpoint_tail_phase_uniform
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
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let e := centeredRescale yoshidaEndpointA (fun x ↦
      ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re)
    let o := centeredRescale yoshidaEndpointA (fun x ↦
      ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re)
    0 ≤ yoshidaEndpointOddCleanQuadratic e +
        yoshidaEndpointOddCleanQuadratic o +
      a * (factorTwoCenteredSymmetricPerturbation e +
        factorTwoCenteredSymmetricPerturbation o) +
      b * factorTwoCenteredAlternatingCoupling e o := by
  dsimp only
  let e : ℝ → ℝ := centeredRescale yoshidaEndpointA (fun x ↦
    ((re : YoshidaClippedSmooth yoshidaEndpointA) x).re)
  let o : ℝ → ℝ := centeredRescale yoshidaEndpointA (fun x ↦
    ((ro : YoshidaClippedSmooth yoshidaEndpointA) x).re)
  have hec : Continuous e := by
    simpa only [e] using
      continuous_centeredRescale_re_of_endpoints_zero
        yoshidaEndpointA_pos re heNeg hePos
  have hoc : Continuous o := by
    simpa only [o] using
      continuous_centeredRescale_re_of_endpoints_zero
        yoshidaEndpointA_pos ro hoNeg hoPos
  have heven : Function.Even e := by
    intro x
    dsimp only [e, centeredRescale]
    rw [show yoshidaEndpointA * -x = -(yoshidaEndpointA * x) by ring,
      evenTail_pointwise_even yoshidaEndpointA_pos 199 re heTail
        (yoshidaEndpointA * x)]
  have hood : Function.Odd o := by
    intro x
    dsimp only [o, centeredRescale]
    rw [show yoshidaEndpointA * -x = -(yoshidaEndpointA * x) by ring,
      oddTail_pointwise_odd yoshidaEndpointA_pos 10 ro hoTail
        (yoshidaEndpointA * x)]
    rfl
  have hPeLower :
      -(3 : ℝ) * (∫ x : ℝ in -1..1, e x ^ 2) ≤
        factorTwoCenteredSymmetricPerturbation e :=
    neg_three_energy_le_even_symmetricPerturbation e hec heven
  have hPeUpper :
      factorTwoCenteredSymmetricPerturbation e ≤
        ∫ x : ℝ in -1..1, e x ^ 2 :=
    even_symmetricPerturbation_le_energy e hec heven
  have hPoLower :
      -(∫ x : ℝ in -1..1, o x ^ 2) ≤
        factorTwoCenteredSymmetricPerturbation o :=
    neg_energy_le_odd_symmetricPerturbation o hoc hood
  have hPoUpper :
      factorTwoCenteredSymmetricPerturbation o ≤
        (3 / 2 : ℝ) * ∫ x : ℝ in -1..1, o x ^ 2 :=
    odd_symmetricPerturbation_le_three_halves_energy o hoc hood
  have hJ := factorTwoCenteredAlternatingCoupling_sq_le_energy_mul
    e o hec hoc heven hood
  apply endpoint_tail_phase_uniform_of_directional_bounds
    re ro heTail hoTail heReal hoReal heNeg hePos hoNeg hoPos
  · simpa only [e] using hPeLower
  · simpa only [e] using hPeUpper
  · simpa only [o] using hPoLower
  · simpa only [o] using hPoUpper
  · simpa only [e, o, mul_assoc] using hJ
  · exact hphase

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDirectionalTail
