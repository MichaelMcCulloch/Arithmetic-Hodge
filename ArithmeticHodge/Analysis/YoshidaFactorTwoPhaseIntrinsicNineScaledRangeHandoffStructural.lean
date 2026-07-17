import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineBalancedPencilStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineEnhancedTailReserveStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseScaledRangePencilStructural

set_option autoImplicit false

open Matrix MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineScaledRangeHandoffStructural

noncomputable section

open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineBalancedPencilStructural
open YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineEnhancedTailReserveStructural
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseP678CombinedResidualSchurStructural
open YoshidaFactorTwoPhaseScaledRangePencilStructural

/-!
# Scaled-range handoff for the cutoff-nine survivor

This is the exact interface between a phase-native finite matrix certificate
and the already-proved balanced `P6/P7/P8` outer Schur theorem.  The residual
tail contributes its compiled quantitative reserve, so the only hypotheses
left here are the low-matrix representation, the survivor linear-functional
representation, and the fraction-free range certificate.
-/

/-- A scaled range certificate for the balanced cutoff-nine low matrix closes
the complete low--tail determinant.  The tail budget is discharged internally
from the cutoff-nine moment gaps. -/
theorem factorTwoEndpointLowTailMixed_intrinsicNine_sq_le_of_scaledRange
    {ι : Type*} [Fintype ι]
    (eR oR : ℝ → ℝ) (heRc : Continuous eR) (hoRc : Continuous oR)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heRe : Function.Even eR) (hoRo : Function.Odd oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 9)
    (hoGap : centeredLegendreMomentsVanishBelow oR 9)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (A : Matrix ι ι ℝ) (x h v : ι → ℝ) (d : ℝ)
    (hlow :
      x ⬝ᵥ (A *ᵥ x) =
        factorTwoEndpointChannelPhase
            (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
            (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b -
          (15 / 16 : ℝ) *
            factorTwoIntrinsicNineP678LowReserve c6 c7 c8)
    (hsurvivor :
      h ⬝ᵥ x = factorTwoIntrinsicNineRemainingMixed eR oR
        c0 c2 c4 c6 c8 c1 c3 c5 c7 a b)
    (hA : A.PosSemidef)
    (hd : 0 < d)
    (hrange : A *ᵥ v = d • h)
    (hbudget :
      15 * (h ⬝ᵥ v) ≤
        d * factorTwoIntrinsicNineSurvivorResidualReserve eR oR) :
    factorTwoEndpointLowTailMixed
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8) eR
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) oR a b ^ 2 ≤
      factorTwoEndpointChannelPhase
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b *
        factorTwoEndpointChannelPhase eR oR a b := by
  let low := factorTwoEndpointChannelPhase
    (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
    (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b
  let tail := factorTwoEndpointChannelPhase eR oR a b
  let X := factorTwoIntrinsicNineP678LowReserve c6 c7 c8
  let Y := factorTwoIntrinsicNineSurvivorResidualReserve eR oR
  let Yold := factorTwoIntrinsicNineResidualReserve eR oR
  let Z := factorTwoP678ResidualCombinedForwardMixed
    eR oR c6 c7 c8 a b
  let S := factorTwoIntrinsicNineRemainingMixed eR oR
    c0 c2 c4 c6 c8 c1 c3 c5 c7 a b
  let M := factorTwoEndpointLowTailMixed
    (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8) eR
    (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) oR a b
  have hlow' : x ⬝ᵥ (A *ᵥ x) = low - (15 / 16 : ℝ) * X := by
    simpa only [low, X] using hlow
  have hsurvivor' : h ⬝ᵥ x = S := by
    simpa only [S] using hsurvivor
  have hmix : M = Z + S := by
    simpa only [M, Z, S] using
      factorTwoEndpointLowTailMixed_intrinsicNine_eq_P678_add_remaining
        eR oR heRc hoRc heLocal hoLocal hoRo heGap hoGap
          c0 c2 c4 c6 c8 c1 c3 c5 c7 a b
  have hlowBalanced : 0 ≤ low - (15 / 16 : ℝ) * X := by
    rw [← hlow']
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg x
  have htailScaled : Y ≤ 15 * (tail - (14 / 15 : ℝ) * Yold) := by
    simpa only [tail, Y, Yold] using
      factorTwoIntrinsicNineSurvivorResidualReserve_le_fifteen_mul_balancedTail
        eR oR heRc hoRc heLocal hoLocal heRe hoRo heGap hoGap a b hab
  have hpencil : ∀ c r : ℝ,
      0 ≤ low * c ^ 2 + 2 * M * c * r + tail * r ^ 2 -
        ((15 / 16 : ℝ) * X * c ^ 2 + 2 * Z * c * r +
          (14 / 15 : ℝ) * Yold * r ^ 2) := by
    intro c r
    have hq := scaledRange_quadratic_pencil_nonneg
      A h v x d Y (tail - (14 / 15 : ℝ) * Yold)
      hA hd hrange (by simpa only [Y] using hbudget) htailScaled c r
    rw [hlow', hsurvivor'] at hq
    rw [hmix]
    nlinarith
  apply
    factorTwoEndpointLowTailMixed_intrinsicNine_sq_le_of_direct_balanced_full_pencil
      eR oR heRc hoRc heLocal hoLocal heRe hoRo heGap hoGap
        c0 c2 c4 c6 c8 c1 c3 c5 c7 a b hab
        (by simpa only [low, X] using hlowBalanced)
        (by
          have hY := factorTwoIntrinsicNineResidualReserve_le_phase
            eR oR heRc hoRc heLocal hoLocal heRe hoRo
              heGap hoGap a b hab
          simpa only [tail, Yold] using
            sub_nonneg.mpr
              ((mul_le_of_le_one_left
                (factorTwoIntrinsicNineResidualReserve_nonneg eR oR)
                (by norm_num : (14 / 15 : ℝ) ≤ 1)).trans hY))
  simpa only [low, tail, X, Yold, Z, M] using hpencil

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineScaledRangeHandoffStructural
