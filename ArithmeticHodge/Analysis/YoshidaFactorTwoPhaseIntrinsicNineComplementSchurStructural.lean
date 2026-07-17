import ArithmeticHodge.Analysis.TwoByTwoSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP678CombinedResidualSchurStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural

noncomputable section

open TwoByTwoSchur
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseP67ResidualRegularDecompositionStructural
open YoshidaFactorTwoPhaseP678CombinedResidualSchurStructural

/-!
# Complement Schur handoff for the cutoff-nine mixed term

The exact mixed decomposition has one already-certified `P6/P7/P8` family
and one genuinely coupled survivor.  The certified family spends named low
and residual reserves.  This file records the lossless algebraic handoff:
it is enough to place the survivor in the exact complementary diagonal
forms.  No triangle inequality between the two families is used.
-/

/-- Low reserve already assigned to the certified `P6/P7/P8` mixed family. -/
def factorTwoIntrinsicNineP678LowReserve
    (c6 c7 c8 : ℝ) : ℝ :=
  (1 / 100 : ℝ) *
      (factorTwoIntrinsicEnergy factorTwoCenteredP6 * c6 ^ 2 +
        factorTwoIntrinsicEnergy factorTwoCenteredP7 * c7 ^ 2) +
    (33 / 100 : ℝ) *
      factorTwoIntrinsicEnergy factorTwoCenteredP8 * c8 ^ 2

/-- Quantitative cutoff-nine residual reserve assigned to the certified
upper mixed family. -/
def factorTwoIntrinsicNineResidualReserve
    (eR oR : ℝ → ℝ) : ℝ :=
  (1 / 250 : ℝ) * factorTwoIntrinsicEnergy eR +
    (1 / 2500 : ℝ) * factorTwoIntrinsicEnergy oR +
    (1 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy oR

/-- Everything in the exact cutoff-nine half-cross except the certified
`P6/P7/P8` forward family.  The lower smooth rows and all five
nonpolynomial survivors stay coupled. -/
def factorTwoIntrinsicNineRemainingMixed
    (eR oR : ℝ → ℝ)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∫ t : ℝ in 0..2,
      factorTwoP67ResidualSmoothMixedIntegrand
        (factorTwoEvenStructuralLowProfile c0 c2 +
          factorTwoIntrinsicSixEvenTail c4)
        (factorTwoIntrinsicSixOddTail c1 c3 c5)
        eR oR a b t) +
    factorTwoIntrinsicNineNonpolynomialMixed
      (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
      (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7)
      eR oR a b

theorem factorTwoIntrinsicNineP678LowReserve_nonneg
    (c6 c7 c8 : ℝ) :
    0 ≤ factorTwoIntrinsicNineP678LowReserve c6 c7 c8 := by
  unfold factorTwoIntrinsicNineP678LowReserve
  exact add_nonneg
    (mul_nonneg (by norm_num) (add_nonneg
      (mul_nonneg
        (factorTwoIntrinsicEnergy_nonneg factorTwoCenteredP6) (sq_nonneg c6))
      (mul_nonneg
        (factorTwoIntrinsicEnergy_nonneg factorTwoCenteredP7) (sq_nonneg c7))))
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (factorTwoIntrinsicEnergy_nonneg factorTwoCenteredP8)) (sq_nonneg c8))

theorem factorTwoIntrinsicNineResidualReserve_nonneg
    (eR oR : ℝ → ℝ) :
    0 ≤ factorTwoIntrinsicNineResidualReserve eR oR := by
  unfold factorTwoIntrinsicNineResidualReserve
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (by norm_num) (factorTwoIntrinsicEnergy_nonneg eR))
      (mul_nonneg (by norm_num) (factorTwoIntrinsicEnergy_nonneg oR)))
    (mul_nonneg (by norm_num) (factorTwoIntrinsicPotentialEnergy_nonneg oR))

/-- Exact two-family presentation of the cutoff-nine mixed term. -/
theorem factorTwoEndpointLowTailMixed_intrinsicNine_eq_P678_add_remaining
    (eR oR : ℝ → ℝ) (heRc : Continuous eR) (hoRc : Continuous oR)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (hoRo : Function.Odd oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 9)
    (hoGap : centeredLegendreMomentsVanishBelow oR 9)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 a b : ℝ) :
    factorTwoEndpointLowTailMixed
        (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8) eR
        (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) oR a b =
      factorTwoP678ResidualCombinedForwardMixed eR oR c6 c7 c8 a b +
        factorTwoIntrinsicNineRemainingMixed eR oR
          c0 c2 c4 c6 c8 c1 c3 c5 c7 a b := by
  rw [factorTwoEndpointLowTailMixed_intrinsicNine_eq
    eR oR heRc hoRc heLocal hoLocal hoRo heGap hoGap
      c0 c2 c4 c6 c8 c1 c3 c5 c7 a b]
  unfold factorTwoIntrinsicNineRemainingMixed
  ring

/-- Sharp complement target for the cutoff-nine outer Schur step.  The
existing theorem supplies the `P678` determinant bound; the only substantive
new analytic input is `hremaining`, a determinant bound for the honest
survivor against the diagonal complements. -/
theorem factorTwoEndpointLowTailMixed_intrinsicNine_sq_le_of_complement
    (eR oR : ℝ → ℝ) (heRc : Continuous eR) (hoRc : Continuous oR)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heRe : Function.Even eR) (hoRo : Function.Odd oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 9)
    (hoGap : centeredLegendreMomentsVanishBelow oR 9)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hlowComplement :
      0 ≤ factorTwoEndpointChannelPhase
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b -
        factorTwoIntrinsicNineP678LowReserve c6 c7 c8)
    (htailComplement :
      0 ≤ factorTwoEndpointChannelPhase eR oR a b -
        factorTwoIntrinsicNineResidualReserve eR oR)
    (hremaining :
      factorTwoIntrinsicNineRemainingMixed eR oR
            c0 c2 c4 c6 c8 c1 c3 c5 c7 a b ^ 2 ≤
        (factorTwoEndpointChannelPhase
              (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
              (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b -
            factorTwoIntrinsicNineP678LowReserve c6 c7 c8) *
          (factorTwoEndpointChannelPhase eR oR a b -
            factorTwoIntrinsicNineResidualReserve eR oR)) :
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
  let Y := factorTwoIntrinsicNineResidualReserve eR oR
  let Z := factorTwoP678ResidualCombinedForwardMixed
    eR oR c6 c7 c8 a b
  let S := factorTwoIntrinsicNineRemainingMixed eR oR
    c0 c2 c4 c6 c8 c1 c3 c5 c7 a b
  have hZ : Z ^ 2 ≤ X * Y := by
    simpa only [Z, X, Y, factorTwoIntrinsicNineP678LowReserve,
      factorTwoIntrinsicNineResidualReserve] using
      factorTwoP678ResidualCombinedForwardMixed_sq_le_reserve_mul
        eR oR heRc hoRc heRe hoRo heGap hoGap c6 c7 c8 a b hab
  have hdet : (Z + S) ^ 2 ≤ low * tail :=
    determinant_bound_add_complements low tail X Y Z S
      (factorTwoIntrinsicNineP678LowReserve_nonneg c6 c7 c8)
      (factorTwoIntrinsicNineResidualReserve_nonneg eR oR)
      (by simpa only [low, X] using hlowComplement)
      (by simpa only [tail, Y] using htailComplement)
      hZ (by simpa only [low, tail, X, Y, S] using hremaining)
  rw [factorTwoEndpointLowTailMixed_intrinsicNine_eq_P678_add_remaining
    eR oR heRc hoRc heLocal hoLocal hoRo heGap hoGap
      c0 c2 c4 c6 c8 c1 c3 c5 c7 a b]
  simpa only [low, tail, Z, S] using hdet

/-- Balanced use of the sharp `7 / 8` P678 estimate.  Factoring
`7 / 8 = (15 / 16) * (14 / 15)` leaves a rational fraction of the P678
reserve on both diagonals.  Consequently the survivor only has to fit inside
the larger balanced complements. -/
theorem factorTwoEndpointLowTailMixed_intrinsicNine_sq_le_of_balanced_complement
    (eR oR : ℝ → ℝ) (heRc : Continuous eR) (hoRc : Continuous oR)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heRe : Function.Even eR) (hoRo : Function.Odd oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 9)
    (hoGap : centeredLegendreMomentsVanishBelow oR 9)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hlowComplement :
      0 ≤ factorTwoEndpointChannelPhase
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b -
        factorTwoIntrinsicNineP678LowReserve c6 c7 c8)
    (htailComplement :
      0 ≤ factorTwoEndpointChannelPhase eR oR a b -
        factorTwoIntrinsicNineResidualReserve eR oR)
    (hremaining :
      factorTwoIntrinsicNineRemainingMixed eR oR
            c0 c2 c4 c6 c8 c1 c3 c5 c7 a b ^ 2 ≤
        (factorTwoEndpointChannelPhase
              (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
              (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b -
            (15 / 16 : ℝ) *
              factorTwoIntrinsicNineP678LowReserve c6 c7 c8) *
          (factorTwoEndpointChannelPhase eR oR a b -
            (14 / 15 : ℝ) *
              factorTwoIntrinsicNineResidualReserve eR oR)) :
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
  let Y := factorTwoIntrinsicNineResidualReserve eR oR
  let X' := (15 / 16 : ℝ) * X
  let Y' := (14 / 15 : ℝ) * Y
  let Z := factorTwoP678ResidualCombinedForwardMixed
    eR oR c6 c7 c8 a b
  let S := factorTwoIntrinsicNineRemainingMixed eR oR
    c0 c2 c4 c6 c8 c1 c3 c5 c7 a b
  have hX : 0 ≤ X := by
    simpa only [X] using
      factorTwoIntrinsicNineP678LowReserve_nonneg c6 c7 c8
  have hY : 0 ≤ Y := by
    simpa only [Y] using
      factorTwoIntrinsicNineResidualReserve_nonneg eR oR
  have hX' : 0 ≤ X' := by
    exact mul_nonneg (by norm_num) hX
  have hY' : 0 ≤ Y' := by
    exact mul_nonneg (by norm_num) hY
  have hlow' : 0 ≤ low - X' := by
    have hlow : 0 ≤ low - X := by
      simpa only [low, X] using hlowComplement
    dsimp only [X']
    linarith
  have htail' : 0 ≤ tail - Y' := by
    have htail : 0 ≤ tail - Y := by
      simpa only [tail, Y] using htailComplement
    dsimp only [Y']
    linarith
  have hZ : Z ^ 2 ≤ X' * Y' := by
    have hsharp : Z ^ 2 ≤ (7 / 8 : ℝ) * (X * Y) := by
      simpa only [Z, X, Y, factorTwoIntrinsicNineP678LowReserve,
        factorTwoIntrinsicNineResidualReserve] using
        factorTwoP678ResidualCombinedForwardMixed_sq_le_seven_eighths_mul_reserve_mul
          eR oR heRc hoRc heRe hoRo heGap hoGap c6 c7 c8 a b hab
    calc
      Z ^ 2 ≤ (7 / 8 : ℝ) * (X * Y) := hsharp
      _ = X' * Y' := by simp only [X', Y']; ring
  have hdet : (Z + S) ^ 2 ≤ low * tail :=
    determinant_bound_add_complements low tail X' Y' Z S
      hX' hY' hlow' htail' hZ
      (by simpa only [low, tail, X', Y', X, Y, S] using hremaining)
  rw [factorTwoEndpointLowTailMixed_intrinsicNine_eq_P678_add_remaining
    eR oR heRc hoRc heLocal hoLocal hoRo heGap hoGap
      c0 c2 c4 c6 c8 c1 c3 c5 c7 a b]
  simpa only [low, tail, Z, S] using hdet

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
