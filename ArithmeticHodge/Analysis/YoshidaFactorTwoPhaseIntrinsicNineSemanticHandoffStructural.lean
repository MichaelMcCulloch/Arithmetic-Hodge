import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineEnhancedTailReserveStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineSemanticHandoffStructural

noncomputable section

open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineEnhancedTailReserveStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural

/-!
# Semantic cutoff-nine survivor handoff

The scaled-range interface is useful when the survivor has already been
represented by a finite vector.  For the aggregate weighted proof it is
shorter to retain the survivor as its actual scalar mixed form.  The single
determinant below automatically includes the range condition and all kernel
annihilation at singular boundary phases.
-/

/-- The aggregate survivor determinant, measured against the full enhanced
residual reserve, closes the complete cutoff-nine low--tail Schur bound. -/
theorem factorTwoEndpointLowTailMixed_intrinsicNine_sq_le_of_semantic_survivor
    (eR oR : ℝ → ℝ) (heRc : Continuous eR) (hoRc : Continuous oR)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heRe : Function.Even eR) (hoRo : Function.Odd oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 9)
    (hoGap : centeredLegendreMomentsVanishBelow oR 9)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hlowBalanced :
      0 ≤ factorTwoEndpointChannelPhase
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b -
        (15 / 16 : ℝ) *
          factorTwoIntrinsicNineP678LowReserve c6 c7 c8)
    (hsurvivor :
      15 * factorTwoIntrinsicNineRemainingMixed eR oR
            c0 c2 c4 c6 c8 c1 c3 c5 c7 a b ^ 2 ≤
        (factorTwoEndpointChannelPhase
              (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
              (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b -
            (15 / 16 : ℝ) *
              factorTwoIntrinsicNineP678LowReserve c6 c7 c8) *
          factorTwoIntrinsicNineSurvivorResidualReserve eR oR) :
    factorTwoEndpointLowTailMixed
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8) eR
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) oR a b ^ 2 ≤
      factorTwoEndpointChannelPhase
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b *
        factorTwoEndpointChannelPhase eR oR a b := by
  let L := factorTwoEndpointChannelPhase
      (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
      (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b -
    (15 / 16 : ℝ) * factorTwoIntrinsicNineP678LowReserve c6 c7 c8
  let T := factorTwoEndpointChannelPhase eR oR a b -
    (14 / 15 : ℝ) * factorTwoIntrinsicNineResidualReserve eR oR
  let W := factorTwoIntrinsicNineSurvivorResidualReserve eR oR
  let S := factorTwoIntrinsicNineRemainingMixed eR oR
    c0 c2 c4 c6 c8 c1 c3 c5 c7 a b
  have hL : 0 ≤ L := by
    simpa only [L] using hlowBalanced
  have hW : 0 ≤ W := by
    simpa only [W] using
      factorTwoIntrinsicNineSurvivorResidualReserve_nonneg eR oR
  have hWT : W ≤ 15 * T := by
    simpa only [W, T] using
      factorTwoIntrinsicNineSurvivorResidualReserve_le_fifteen_mul_balancedTail
        eR oR heRc hoRc heLocal hoLocal heRe hoRo heGap hoGap a b hab
  have hT : 0 ≤ T := by
    nlinarith
  have hS : S ^ 2 ≤ L * T := by
    have hLW : L * W ≤ L * (15 * T) :=
      mul_le_mul_of_nonneg_left hWT hL
    have hscaled : 15 * S ^ 2 ≤ 15 * (L * T) := by
      calc
        15 * S ^ 2 ≤ L * W := by
          simpa only [L, W, S] using hsurvivor
        _ ≤ L * (15 * T) := hLW
        _ = 15 * (L * T) := by ring
    nlinarith
  apply
    factorTwoEndpointLowTailMixed_intrinsicNine_sq_le_of_direct_balanced_complement
      eR oR heRc hoRc heLocal hoLocal heRe hoRo heGap hoGap
        c0 c2 c4 c6 c8 c1 c3 c5 c7 a b hab
  · simpa only [L] using hL
  · simpa only [T] using hT
  · simpa only [L, T, S] using hS

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineSemanticHandoffStructural
