import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotMixedStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStructuralPositive

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC1Structural

noncomputable section

open Polynomial
open CenteredOddOneThreeEnergy
open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusStructural
open YoshidaFactorTwoPhaseIntrinsicLowStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01Slope23FifthsStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotMixedStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# The first mixed raw four-mode coefficient

The proof is a Schur-complement argument.  Its only rational estimate is a
single positive definite lower form for the endpoint budget `E₋ + 3 E₊`.
No projective parameter is sampled and no coefficient is established by
exhaustive evaluation.
-/

private def k00 : ℝ := 20157 / 20000
private def k02 : ℝ := 23779 / 25000
private def k22 : ℝ := 18583 / 20000

private def k04 : ℝ :=
  factorTwoIntrinsicFourP45Cross04 (-1) +
    3 * factorTwoIntrinsicFourP45Cross04 1

private def k24 : ℝ :=
  factorTwoIntrinsicFourP45Cross24 (-1) +
    3 * factorTwoIntrinsicFourP45Cross24 1

private def k44 : ℝ := 891 / 1000

private def kCrossSum : ℝ := k04 + k24
private def kCrossDifference : ℝ := k24 - k04

private theorem kCross_sum_difference_bounds :
    (107 / 125 : ℝ) < kCrossSum ∧
      kCrossSum < (879 / 1000 : ℝ) ∧
      (29 / 250 : ℝ) < kCrossDifference ∧
      kCrossDifference < (129 / 1000 : ℝ) := by
  let plusSum : ℝ := factorTwoIntrinsicP4PlusCrossSum
  let plusDiff : ℝ := factorTwoIntrinsicP4PlusCrossDifference
  let minusSum : ℝ := factorTwoIntrinsicP4MinusCrossSum
  let minusDiff : ℝ := factorTwoIntrinsicP4MinusCrossDifference
  let cleanSum : ℝ :=
    yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 +
      yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4
  let cleanDiff : ℝ :=
    yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 -
      yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4
  have hpS := factorTwoIntrinsicP4PlusCrossSum_bounds
  have hpD := factorTwoIntrinsicP4PlusCrossDifference_bounds
  have hm := factorTwoIntrinsicP4MinusCross_sum_difference_bounds
  have hcS :=
    factorTwoIntrinsicP4CleanCross_sum_sub_seventeen_seventieths_abs_lt
  have hcD :=
    factorTwoIntrinsicP4CleanCross_difference_sub_three_seventieths_abs_lt
  have hsum : plusSum + minusSum = 2 * cleanSum := by
    dsimp only [plusSum, minusSum, cleanSum]
    unfold factorTwoIntrinsicP4PlusCrossSum
      factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
    ring
  have hdiff : plusDiff + minusDiff = 2 * cleanDiff := by
    dsimp only [plusDiff, minusDiff, cleanDiff]
    unfold factorTwoIntrinsicP4PlusCrossDifference
      factorTwoIntrinsicP4MinusCrossDifference
      factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
    ring
  have hkS : kCrossSum = minusSum + 3 * plusSum := by
    dsimp only [kCrossSum, k04, k24, minusSum, plusSum]
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicP4PlusCrossSum
    ring
  have hkD : kCrossDifference = minusDiff + 3 * plusDiff := by
    dsimp only [kCrossDifference, k04, k24, minusDiff, plusDiff]
    unfold factorTwoIntrinsicP4MinusCrossDifference
      factorTwoIntrinsicP4PlusCrossDifference
    ring
  rw [abs_lt] at hcS hcD
  change -(1 / 25000 : ℝ) < cleanSum - 17 / 70 ∧
    cleanSum - 17 / 70 < (1 / 25000 : ℝ) at hcS
  change -(1 / 25000 : ℝ) < cleanDiff - 3 / 70 ∧
    cleanDiff - 3 / 70 < (1 / 25000 : ℝ) at hcD
  change 0 < plusSum ∧ plusSum < (193 / 1000 : ℝ) at hpS
  change 0 < plusDiff ∧ plusDiff < (39 / 2000 : ℝ) at hpD
  change 0 < minusSum ∧ minusSum < (3 / 10 : ℝ) ∧
    0 < minusDiff ∧ minusDiff < (7 / 100 : ℝ) at hm
  constructor
  · rw [hkS]
    nlinarith [hsum]
  constructor
  · rw [hkS]
    nlinarith [hpS.2, hm.2.1]
  constructor
  · rw [hkD]
    nlinarith [hdiff]
  · rw [hkD]
    nlinarith [hpD.2, hm.2.2.2]

private def kLowDet : ℝ := k00 * k22 - k02 ^ 2

private def kDet : ℝ :=
  symmetricDeterminant k00 k02 k04 k22 k24 k44

private theorem kLowDet_pos : 0 < kLowDet := by
  norm_num [kLowDet, k00, k02, k22]

private theorem kDet_gt : (1 / 1000 : ℝ) < kDet := by
  let S : ℝ := kCrossSum
  let T : ℝ := kCrossDifference
  rcases kCross_sum_difference_bounds with ⟨hSL, hSU, hTL, hTU⟩
  have hS0 : 0 < S := by dsimp only [S]; linarith
  have hT0 : 0 < T := by dsimp only [T]; linarith
  have hSsq : S ^ 2 < (879 / 1000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ (by simpa only [S] using hSU) hS0.le (by norm_num)
  have hTsq : T ^ 2 < (129 / 1000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ (by simpa only [T] using hTU) hT0.le (by norm_num)
  have hST : S * T < (879 / 1000 : ℝ) * (129 / 1000 : ℝ) := by
    calc
      S * T < (879 / 1000 : ℝ) * T :=
        mul_lt_mul_of_pos_right (by simpa only [S] using hSU) hT0
      _ < (879 / 1000 : ℝ) * (129 / 1000 : ℝ) :=
        mul_lt_mul_of_pos_left (by simpa only [T] using hTU) (by norm_num)
  have hadj :
      k22 * k04 ^ 2 - 2 * k02 * k04 * k24 + k00 * k24 ^ 2 =
        ((k00 + k22 - 2 * k02) * S ^ 2 +
          2 * (k00 - k22) * S * T +
          (k00 + k22 + 2 * k02) * T ^ 2) / 4 := by
    dsimp only [S, T, kCrossSum, kCrossDifference]
    ring
  unfold kDet symmetricDeterminant
  rw [show
      k00 * (k22 * k44 - k24 ^ 2) -
          k02 * (k02 * k44 - k04 * k24) +
          k04 * (k02 * k24 - k04 * k22) =
        (k00 * k22 - k02 ^ 2) * k44 -
          (k22 * k04 ^ 2 - 2 * k02 * k04 * k24 + k00 * k24 ^ 2) by
    ring, hadj]
  norm_num [k00, k02, k22, k44] at hSsq hTsq hST ⊢
  nlinarith only [hSsq, hTsq, hST]

private theorem k_principal_gates :
    0 < k00 ∧ 0 < leadingMinorTwo k00 k02 k22 ∧ 0 < kDet := by
  refine ⟨by norm_num [k00], ?_, (by linarith [kDet_gt])⟩
  simpa only [leadingMinorTwo, kLowDet] using kLowDet_pos

private def lowAlternatingAdjugate : ℝ :=
  k22 * factorTwoIntrinsicAlternating01 ^ 2 -
    2 * k02 * factorTwoIntrinsicAlternating01 *
      factorTwoIntrinsicAlternating21 +
    k00 * factorTwoIntrinsicAlternating21 ^ 2

private def p4AlternatingPolar : ℝ :=
  k22 * k04 * factorTwoIntrinsicAlternating01 -
    k02 * (k04 * factorTwoIntrinsicAlternating21 +
      k24 * factorTwoIntrinsicAlternating01) +
    k00 * k24 * factorTwoIntrinsicAlternating21

private theorem lowAlternatingAdjugate_lt :
    lowAlternatingAdjugate < (27 / 10000 : ℝ) := by
  let x : ℝ := factorTwoIntrinsicAlternating01 +
    factorTwoIntrinsicAlternating21
  let y : ℝ := factorTwoIntrinsicAlternating01 -
    factorTwoIntrinsicAlternating21
  rcases factorTwoIntrinsicAlternatingSharpBounds with
    ⟨hxL, hxU, hyL, hyU, _⟩
  have hx0 : 0 < x := by dsimp only [x]; linarith
  have hy0 : 0 < y := by dsimp only [y]; linarith
  have hxsq : x ^ 2 < (56173 / 100000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ (by simpa only [x] using hxU) hx0.le (by norm_num)
  have hysq : y ^ 2 < (1692 / 100000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ (by simpa only [y] using hyU) hy0.le (by norm_num)
  have hxy : (56168 / 100000 : ℝ) * (1687 / 100000 : ℝ) < x * y := by
    calc
      (56168 / 100000 : ℝ) * (1687 / 100000 : ℝ) <
          x * (1687 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_right (by simpa only [x] using hxL) (by norm_num)
      _ < x * y := mul_lt_mul_of_pos_left (by simpa only [y] using hyL) hx0
  have heq : lowAlternatingAdjugate =
      ((k00 + k22 - 2 * k02) * x ^ 2 +
        (k00 + k22 + 2 * k02) * y ^ 2 +
        2 * (k22 - k00) * x * y) / 4 := by
    dsimp only [lowAlternatingAdjugate, x, y]
    ring
  rw [heq]
  norm_num [k00, k02, k22] at hxsq hysq hxy ⊢
  nlinarith only [hxsq, hysq, hxy]

private theorem p4AlternatingPolar_bounds :
    (16 / 5000 : ℝ) < p4AlternatingPolar ∧
      p4AlternatingPolar < (7 / 2000 : ℝ) := by
  let S : ℝ := kCrossSum
  let T : ℝ := kCrossDifference
  let x : ℝ := factorTwoIntrinsicAlternating01 +
    factorTwoIntrinsicAlternating21
  let y : ℝ := factorTwoIntrinsicAlternating01 -
    factorTwoIntrinsicAlternating21
  rcases kCross_sum_difference_bounds with ⟨hSL, hSU, hTL, hTU⟩
  rcases factorTwoIntrinsicAlternatingSharpBounds with
    ⟨hxL, hxU, hyL, hyU, _⟩
  let alpha : ℝ :=
    (k00 + k22 - 2 * k02) * S + (k00 - k22) * T
  let beta : ℝ :=
    (k00 + k22 + 2 * k02) * T + (k00 - k22) * S
  have halpha0 : 0 < alpha := by
    dsimp only [alpha]
    have hS0 : 0 < S := by dsimp only [S]; linarith
    have hT0 : 0 < T := by dsimp only [T]; linarith
    norm_num [k00, k02, k22]
    positivity
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    have hS0 : 0 < S := by dsimp only [S]; linarith
    have hT0 : 0 < T := by dsimp only [T]; linarith
    norm_num [k00, k02, k22]
    positivity
  have hx0 : 0 < x := by dsimp only [x]; linarith
  have hy0 : 0 < y := by dsimp only [y]; linarith
  have hxLower : alpha * (56168 / 100000 : ℝ) < alpha * x :=
    mul_lt_mul_of_pos_left (by simpa only [x] using hxL) halpha0
  have hxUpper : alpha * x < alpha * (56173 / 100000 : ℝ) :=
    mul_lt_mul_of_pos_left (by simpa only [x] using hxU) halpha0
  have hyLower : beta * (1687 / 100000 : ℝ) < beta * y :=
    mul_lt_mul_of_pos_left (by simpa only [y] using hyL) hbeta0
  have hyUpper : beta * y < beta * (1692 / 100000 : ℝ) :=
    mul_lt_mul_of_pos_left (by simpa only [y] using hyU) hbeta0
  have hcornerLower :
      (16 / 5000 : ℝ) <
        (((k00 + k22 - 2 * k02) * (107 / 125 : ℝ) +
            (k00 - k22) * (129 / 1000 : ℝ)) *
              (56168 / 100000 : ℝ) -
          ((k00 + k22 + 2 * k02) * (129 / 1000 : ℝ) +
            (k00 - k22) * (107 / 125 : ℝ)) *
              (1692 / 100000 : ℝ)) / 4 := by
    norm_num [k00, k02, k22]
  have hlinearLower :
      (((k00 + k22 - 2 * k02) * (107 / 125 : ℝ) +
          (k00 - k22) * (129 / 1000 : ℝ)) *
            (56168 / 100000 : ℝ) -
        ((k00 + k22 + 2 * k02) * (129 / 1000 : ℝ) +
          (k00 - k22) * (107 / 125 : ℝ)) *
            (1692 / 100000 : ℝ)) / 4 <
        (alpha * (56168 / 100000 : ℝ) -
          beta * (1692 / 100000 : ℝ)) / 4 := by
    dsimp only [alpha, beta]
    norm_num [k00, k02, k22] at ⊢
    nlinarith [hSL, hTU]
  have hcornerUpper :
      (((k00 + k22 - 2 * k02) * (879 / 1000 : ℝ) +
          (k00 - k22) * (29 / 250 : ℝ)) *
            (56173 / 100000 : ℝ) -
        ((k00 + k22 + 2 * k02) * (29 / 250 : ℝ) +
          (k00 - k22) * (879 / 1000 : ℝ)) *
            (1687 / 100000 : ℝ)) / 4 < (7 / 2000 : ℝ) := by
    norm_num [k00, k02, k22]
  have hlinearUpper :
      (alpha * (56173 / 100000 : ℝ) -
          beta * (1687 / 100000 : ℝ)) / 4 <
        (((k00 + k22 - 2 * k02) * (879 / 1000 : ℝ) +
            (k00 - k22) * (29 / 250 : ℝ)) *
              (56173 / 100000 : ℝ) -
          ((k00 + k22 + 2 * k02) * (29 / 250 : ℝ) +
            (k00 - k22) * (879 / 1000 : ℝ)) *
              (1687 / 100000 : ℝ)) / 4 := by
    dsimp only [alpha, beta]
    norm_num [k00, k02, k22] at ⊢
    nlinarith [hSU, hTL]
  have heq : p4AlternatingPolar = (alpha * x - beta * y) / 4 := by
    dsimp only [p4AlternatingPolar, alpha, beta, S, T, x, y,
      kCrossSum, kCrossDifference]
    ring
  rw [heq]
  constructor
  · nlinarith [hcornerLower, hlinearLower, hxLower, hyUpper]
  · nlinarith [hcornerUpper, hlinearUpper, hxUpper, hyLower]

private theorem p4AlternatingResidual_bounds :
    0 < kLowDet * factorTwoIntrinsicFourP45Cross41 -
        p4AlternatingPolar ∧
      kLowDet * factorTwoIntrinsicFourP45Cross41 -
        p4AlternatingPolar < (3 / 2000 : ℝ) := by
  have h41 := factorTwoIntrinsicFourP45Cross41_bounds
  have hB := p4AlternatingPolar_bounds
  have hD := kLowDet_pos
  have h41L :
      kLowDet * (141 / 1000 : ℝ) <
        kLowDet * factorTwoIntrinsicFourP45Cross41 :=
    mul_lt_mul_of_pos_left h41.1 hD
  have h41U :
      kLowDet * factorTwoIntrinsicFourP45Cross41 <
        kLowDet * (144 / 1000 : ℝ) :=
    mul_lt_mul_of_pos_left h41.2 hD
  norm_num [kLowDet, k00, k02, k22] at h41L h41U ⊢
  constructor <;> nlinarith [hB.1, hB.2]

private theorem k_adjugate_alternating_le :
    adjugateQuadratic k00 k02 k04 k22 k24 k44
        factorTwoIntrinsicAlternating01
        factorTwoIntrinsicAlternating21
        factorTwoIntrinsicFourP45Cross41 ≤
      (19 / 100 : ℝ) * kDet := by
  let R : ℝ := kLowDet * factorTwoIntrinsicFourP45Cross41 -
    p4AlternatingPolar
  have hR : 0 < R ∧ R < (3 / 2000 : ℝ) := by
    simpa only [R] using p4AlternatingResidual_bounds
  have hRsq : R ^ 2 < (3 / 2000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hR.2 hR.1.le (by norm_num)
  have hA := lowAlternatingAdjugate_lt
  have hgap : (33 / 10000 : ℝ) <
      (19 / 100 : ℝ) * kLowDet - lowAlternatingAdjugate := by
    norm_num [kLowDet, k00, k02, k22] at hA ⊢
    linarith
  have hdet0 : 0 < kDet := by linarith [kDet_gt]
  have hgap0 : 0 <
      (19 / 100 : ℝ) * kLowDet - lowAlternatingAdjugate := by
    linarith
  have hproduct :
      (1 / 1000 : ℝ) * (33 / 10000 : ℝ) <
        kDet * ((19 / 100 : ℝ) * kLowDet -
          lowAlternatingAdjugate) := by
    calc
      _ < kDet * (33 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_right kDet_gt (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hgap hdet0
  have hreserve : R ^ 2 <
      kDet * ((19 / 100 : ℝ) * kLowDet -
        lowAlternatingAdjugate) := by
    have hrat : (3 / 2000 : ℝ) ^ 2 <
        (1 / 1000 : ℝ) * (33 / 10000 : ℝ) := by norm_num
    linarith
  have hadjIdentity :
      kLowDet *
          adjugateQuadratic k00 k02 k04 k22 k24 k44
            factorTwoIntrinsicAlternating01
            factorTwoIntrinsicAlternating21
            factorTwoIntrinsicFourP45Cross41 =
        kDet * lowAlternatingAdjugate + R ^ 2 := by
    dsimp only [R, kLowDet, kDet, lowAlternatingAdjugate,
      p4AlternatingPolar]
    unfold adjugateQuadratic symmetricDeterminant
    ring
  have hscaled : 0 < kLowDet *
      ((19 / 100 : ℝ) * kDet -
        adjugateQuadratic k00 k02 k04 k22 k24 k44
          factorTwoIntrinsicAlternating01
          factorTwoIntrinsicAlternating21
          factorTwoIntrinsicFourP45Cross41) := by
    rw [mul_sub, hadjIdentity]
    nlinarith [hreserve]
  have hstrict :
      adjugateQuadratic k00 k02 k04 k22 k24 k44
          factorTwoIntrinsicAlternating01
          factorTwoIntrinsicAlternating21
          factorTwoIntrinsicFourP45Cross41 <
        (19 / 100 : ℝ) * kDet := by
    have := (mul_pos_iff.mp hscaled)
    rcases this with h | h
    · exact sub_pos.mp h.2
    · exact False.elim (by linarith [kLowDet_pos, h.1])
  exact hstrict.le

private theorem k_alternating_cauchy (z0 z2 z4 : ℝ) :
    (factorTwoIntrinsicAlternating01 * z0 +
        factorTwoIntrinsicAlternating21 * z2 +
        factorTwoIntrinsicFourP45Cross41 * z4) ^ 2 ≤
      (19 / 100 : ℝ) *
        symmetricQuadratic k00 k02 k04 k22 k24 k44 z0 z2 z4 := by
  have hgates := k_principal_gates
  have hQ := symmetricQuadratic_nonneg
    k00 k02 k04 k22 k24 k44 hgates.1 hgates.2.1 hgates.2.2
    z0 z2 z4
  have hcauchy := adjugate_cauchy
    k00 k02 k04 k22 k24 k44 hgates.1 hgates.2.1 hgates.2.2
    factorTwoIntrinsicAlternating01
    factorTwoIntrinsicAlternating21
    factorTwoIntrinsicFourP45Cross41 z0 z2 z4
  have hadj := k_adjugate_alternating_le
  have hupper := mul_le_mul_of_nonneg_left hadj hQ
  have hdet0 : 0 < kDet := by linarith [kDet_gt]
  have hscaled : kDet *
        (factorTwoIntrinsicAlternating01 * z0 +
          factorTwoIntrinsicAlternating21 * z2 +
          factorTwoIntrinsicFourP45Cross41 * z4) ^ 2 ≤
      kDet * ((19 / 100 : ℝ) *
        symmetricQuadratic k00 k02 k04 k22 k24 k44 z0 z2 z4) := by
    calc
      kDet *
          (factorTwoIntrinsicAlternating01 * z0 +
            factorTwoIntrinsicAlternating21 * z2 +
            factorTwoIntrinsicFourP45Cross41 * z4) ^ 2 ≤
        symmetricQuadratic k00 k02 k04 k22 k24 k44 z0 z2 z4 *
          adjugateQuadratic k00 k02 k04 k22 k24 k44
            factorTwoIntrinsicAlternating01
            factorTwoIntrinsicAlternating21
            factorTwoIntrinsicFourP45Cross41 := by
          simpa only [kDet] using hcauchy
      _ ≤ symmetricQuadratic k00 k02 k04 k22 k24 k44 z0 z2 z4 *
          ((19 / 100 : ℝ) * kDet) := hupper
      _ = kDet * ((19 / 100 : ℝ) *
          symmetricQuadratic k00 k02 k04 k22 k24 k44 z0 z2 z4) := by
        ring
  nlinarith

private def endpointBudget (z0 z2 z4 : ℝ) : ℝ :=
  symmetricQuadratic
    (factorTwoStructuralPhaseLow00 (-1) +
      3 * factorTwoStructuralPhaseLow00 1)
    (factorTwoStructuralPhaseLow02 (-1) +
      3 * factorTwoStructuralPhaseLow02 1)
    (factorTwoIntrinsicFourP45Cross04 (-1) +
      3 * factorTwoIntrinsicFourP45Cross04 1)
    (factorTwoStructuralPhaseLow22 (-1) +
      3 * factorTwoStructuralPhaseLow22 1)
    (factorTwoIntrinsicFourP45Cross24 (-1) +
      3 * factorTwoIntrinsicFourP45Cross24 1)
    (factorTwoIntrinsicSixP4Diagonal (-1) +
      3 * factorTwoIntrinsicSixP4Diagonal 1)
    z0 z2 z4

private theorem p4PlusDiagonal_gt :
    (137 / 1000 : ℝ) < factorTwoIntrinsicSixP4Diagonal 1 := by
  have hclean :=
    one_thousand_five_hundred_seventy_one_five_thousandths_lt_clean_p4
  have hpert := factorTwoCenteredSymmetricPerturbation_p4_lower
  change (137 / 1000 : ℝ) < factorTwoIntrinsicP4PhaseDiagonal 1
  unfold factorTwoIntrinsicP4PhaseDiagonal
  norm_num only [one_mul]
  nlinarith

private theorem combinedP4Diagonal_gt :
    k44 < factorTwoIntrinsicSixP4Diagonal (-1) +
      3 * factorTwoIntrinsicSixP4Diagonal 1 := by
  have hm := factorTwoIntrinsicP4MinusDiagonalLower_lt_phaseDiagonal
  have hp := p4PlusDiagonal_gt
  change (137 / 1000 : ℝ) < factorTwoIntrinsicP4PhaseDiagonal 1 at hp
  change k44 < factorTwoIntrinsicP4PhaseDiagonal (-1) +
    3 * factorTwoIntrinsicP4PhaseDiagonal 1
  norm_num [k44, factorTwoIntrinsicP4MinusDiagonalLower] at hm ⊢
  nlinarith

private theorem k_quadratic_le_endpointBudget (z0 z2 z4 : ℝ) :
    symmetricQuadratic k00 k02 k04 k22 k24 k44 z0 z2 z4 ≤
      endpointBudget z0 z2 z4 := by
  have hm := intrinsicStaticMinusEvenLower_le z0 z2
  have hp := evenPositiveEndpointUltraSharp_quadratic_le z0 z2
  have hlow :
      k00 * z0 ^ 2 + 2 * k02 * z0 * z2 + k22 * z2 ^ 2 ≤
        factorTwoIntrinsicStaticEvenQuadratic (-1) z0 z2 +
          3 * factorTwoIntrinsicStaticEvenQuadratic 1 z0 z2 := by
    calc
      k00 * z0 ^ 2 + 2 * k02 * z0 * z2 + k22 * z2 ^ 2 =
          intrinsicStaticMinusEvenLower z0 z2 +
            3 * (evenPositiveEndpointUltraSharp00 * z0 ^ 2 +
              2 * evenPositiveEndpointUltraSharp02 * z0 * z2 +
              evenPositiveEndpointUltraSharp22 * z2 ^ 2) := by
        unfold intrinsicStaticMinusEvenLower
          intrinsicStaticMinusEvenLower00 intrinsicStaticMinusEvenLower02
          intrinsicStaticMinusEvenLower22
          evenPositiveEndpointUltraSharp00 evenPositiveEndpointUltraSharp02
          evenPositiveEndpointUltraSharp22 k00 k02 k22
        ring
      _ ≤ factorTwoIntrinsicStaticEvenQuadratic (-1) z0 z2 +
          3 * factorTwoIntrinsicStaticEvenQuadratic 1 z0 z2 := by
        exact add_le_add hm (mul_le_mul_of_nonneg_left hp (by norm_num))
  have hdiag := mul_le_mul_of_nonneg_right combinedP4Diagonal_gt.le
    (sq_nonneg z4)
  unfold endpointBudget symmetricQuadratic
  unfold factorTwoIntrinsicStaticEvenQuadratic at hlow
  dsimp only [k04, k24]
  nlinarith

private theorem oddPlus_gt :
    (19 / 100 : ℝ) < factorTwoIntrinsicOddPhaseLow11 1 := by
  have hclean := yoshidaEndpointOddLowGram11_gt_1778_div_10000
  have hpert := oddStructuralLow_perturbation_sharp_bounds.1.1
  unfold factorTwoIntrinsicOddPhaseLow11
  norm_num only [one_mul]
  nlinarith

private theorem alternating_cauchy_endpointBudget (z0 z2 z4 : ℝ) :
    (factorTwoIntrinsicAlternating01 * z0 +
        factorTwoIntrinsicAlternating21 * z2 +
        factorTwoIntrinsicFourP45Cross41 * z4) ^ 2 ≤
      factorTwoIntrinsicOddPhaseLow11 1 * endpointBudget z0 z2 z4 := by
  have hgates := k_principal_gates
  have hKnonneg := symmetricQuadratic_nonneg
    k00 k02 k04 k22 k24 k44 hgates.1 hgates.2.1 hgates.2.2
    z0 z2 z4
  have htransport := k_quadratic_le_endpointBudget z0 z2 z4
  have hbudget0 : 0 ≤ endpointBudget z0 z2 z4 := hKnonneg.trans htransport
  calc
    (factorTwoIntrinsicAlternating01 * z0 +
        factorTwoIntrinsicAlternating21 * z2 +
        factorTwoIntrinsicFourP45Cross41 * z4) ^ 2 ≤
      (19 / 100 : ℝ) *
        symmetricQuadratic k00 k02 k04 k22 k24 k44 z0 z2 z4 :=
      k_alternating_cauchy z0 z2 z4
    _ ≤ (19 / 100 : ℝ) * endpointBudget z0 z2 z4 :=
      mul_le_mul_of_nonneg_left htransport (by norm_num)
    _ ≤ factorTwoIntrinsicOddPhaseLow11 1 * endpointBudget z0 z2 z4 :=
      mul_le_mul_of_nonneg_right oddPlus_gt.le hbudget0

/-! ## Exact contact with the raw coefficient -/

private def evenEndpointDet (sigma : ℝ) : ℝ :=
  symmetricDeterminant
    (factorTwoStructuralPhaseLow00 sigma)
    (factorTwoStructuralPhaseLow02 sigma)
    (factorTwoIntrinsicFourP45Cross04 sigma)
    (factorTwoStructuralPhaseLow22 sigma)
    (factorTwoIntrinsicFourP45Cross24 sigma)
    (factorTwoIntrinsicSixP4Diagonal sigma)

private def evenMixedOne : ℝ :=
  mixedDeterminantOne
    (factorTwoStructuralPhaseLow00 1)
    (factorTwoStructuralPhaseLow02 1)
    (factorTwoIntrinsicFourP45Cross04 1)
    (factorTwoStructuralPhaseLow22 1)
    (factorTwoIntrinsicFourP45Cross24 1)
    (factorTwoIntrinsicSixP4Diagonal 1)
    (factorTwoStructuralPhaseLow00 (-1))
    (factorTwoStructuralPhaseLow02 (-1))
    (factorTwoIntrinsicFourP45Cross04 (-1))
    (factorTwoStructuralPhaseLow22 (-1))
    (factorTwoIntrinsicFourP45Cross24 (-1))
    (factorTwoIntrinsicSixP4Diagonal (-1))

private def alternatingPlusAdjugate : ℝ :=
  adjugateQuadratic
    (factorTwoStructuralPhaseLow00 1)
    (factorTwoStructuralPhaseLow02 1)
    (factorTwoIntrinsicFourP45Cross04 1)
    (factorTwoStructuralPhaseLow22 1)
    (factorTwoIntrinsicFourP45Cross24 1)
    (factorTwoIntrinsicSixP4Diagonal 1)
    factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
    factorTwoIntrinsicFourP45Cross41

private theorem p4PivotPolynomial_expansion :
    factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial =
      C (evenEndpointDet 1) + C evenMixedOne * X +
        C (mixedDeterminantOne
          (factorTwoStructuralPhaseLow00 (-1))
          (factorTwoStructuralPhaseLow02 (-1))
          (factorTwoIntrinsicFourP45Cross04 (-1))
          (factorTwoStructuralPhaseLow22 (-1))
          (factorTwoIntrinsicFourP45Cross24 (-1))
          (factorTwoIntrinsicSixP4Diagonal (-1))
          (factorTwoStructuralPhaseLow00 1)
          (factorTwoStructuralPhaseLow02 1)
          (factorTwoIntrinsicFourP45Cross04 1)
          (factorTwoStructuralPhaseLow22 1)
          (factorTwoIntrinsicFourP45Cross24 1)
          (factorTwoIntrinsicSixP4Diagonal 1)) * X ^ 2 +
        C (evenEndpointDet (-1)) * X ^ 3 := by
  unfold factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial
    coefficientAdjugateTwoPolynomial coefficientLowDetPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    endpointAffinePolynomial evenEndpointDet evenMixedOne
    mixedDeterminantOne symmetricDeterminant
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

private theorem pivotCoeff_zero_eq_evenEndpointDet :
    pivotCoeff 0 = evenEndpointDet 1 := by
  change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 0 = _
  rw [p4PivotPolynomial_expansion]
  simp

private theorem pivotCoeff_one_eq_evenMixedOne :
    pivotCoeff 1 = evenMixedOne := by
  change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 1 = _
  rw [p4PivotPolynomial_expansion]
  simp

private theorem p1AlternatingAdjugateCoeff_zero_eq :
    p1AlternatingAdjugateCoeff 0 = alternatingPlusAdjugate := by
  change coefficientP1AlternatingAdjugatePolynomial.coeff 0 = _
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [coefficientP1AlternatingAdjugatePolynomial,
    coefficientLowDetPolynomial, coefficientLow00Polynomial,
    coefficientLow02Polynomial, coefficientLow22Polynomial,
    coefficientCross04Polynomial, coefficientCross24Polynomial,
    coefficientP4DiagonalPolynomial, endpointAffinePolynomial,
    alternatingPlusAdjugate, adjugateQuadratic]
  ring

private theorem coefficient_one_eq_explicit :
    factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 1 =
      evenEndpointDet 1 * factorTwoIntrinsicOddPhaseLow11 (-1) +
        evenMixedOne * factorTwoIntrinsicOddPhaseLow11 1 -
        alternatingPlusAdjugate := by
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]
  rw [pivotCoeff_zero_eq_evenEndpointDet, pivotCoeff_one_eq_evenMixedOne,
    p1AlternatingAdjugateCoeff_zero_eq]
  simp [coefficientOdd11Polynomial, endpointAffinePolynomial]

private def lowDetPlus : ℝ :=
  factorTwoStructuralPhaseLow00 1 * factorTwoStructuralPhaseLow22 1 -
    factorTwoStructuralPhaseLow02 1 ^ 2

private def lowMixedOne : ℝ :=
  factorTwoStructuralPhaseLow00 (-1) * factorTwoStructuralPhaseLow22 1 +
    factorTwoStructuralPhaseLow00 1 * factorTwoStructuralPhaseLow22 (-1) -
    2 * factorTwoStructuralPhaseLow02 1 *
      factorTwoStructuralPhaseLow02 (-1)

private def lowAlternatingPlusAdjugate : ℝ :=
  factorTwoStructuralPhaseLow22 1 * factorTwoIntrinsicAlternating01 ^ 2 -
    2 * factorTwoStructuralPhaseLow02 1 *
      factorTwoIntrinsicAlternating01 * factorTwoIntrinsicAlternating21 +
    factorTwoStructuralPhaseLow00 1 * factorTwoIntrinsicAlternating21 ^ 2

private def lowCoefficientOne : ℝ :=
  lowDetPlus * factorTwoIntrinsicOddPhaseLow11 (-1) +
    lowMixedOne * factorTwoIntrinsicOddPhaseLow11 1 -
    lowAlternatingPlusAdjugate

private theorem lowDetPlus_mul_oddPlus_eq_control0 :
    lowDetPlus * factorTwoIntrinsicOddPhaseLow11 1 =
      factorTwoIntrinsicBoundaryControl0 1 0 := by
  unfold lowDetPlus factorTwoIntrinsicBoundaryControl0
    factorTwoIntrinsicBoundaryPower0 factorTwoIntrinsicEvenDetCoefficient0
    factorTwoIntrinsicEvenPhaseDet factorTwoIntrinsicOddPhaseQuadratic
  ring

private theorem lowCoefficientOne_eq_three_control1 :
    lowCoefficientOne = 3 * factorTwoIntrinsicBoundaryControl1 1 0 := by
  unfold lowCoefficientOne lowDetPlus lowMixedOne
    lowAlternatingPlusAdjugate
    factorTwoIntrinsicBoundaryControl1 factorTwoIntrinsicBoundaryPower0
    factorTwoIntrinsicBoundaryPower1 factorTwoIntrinsicEvenDetCoefficient0
    factorTwoIntrinsicEvenDetCoefficient1
    factorTwoIntrinsicAdjugateCoefficient0
    factorTwoIntrinsicEvenPhaseDet factorTwoIntrinsicEvenAdjugateCoupling
    factorTwoIntrinsicOddPhaseQuadratic factorTwoIntrinsicOddDirectionQuadratic
    factorTwoIntrinsicAlternatingRow0 factorTwoIntrinsicAlternatingRow2
    factorTwoIntrinsicEvenDirection00 factorTwoIntrinsicEvenDirection02
    factorTwoIntrinsicEvenDirection22
    factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22 factorTwoIntrinsicOddPhaseLow11
  norm_num
  ring

private theorem lowCoefficientOne_lower :
    3 * lowDetPlus * factorTwoIntrinsicOddPhaseLow11 1 ≤
      lowCoefficientOne := by
  have hstep :=
    factorTwoIntrinsicBoundaryControlStep01_nonneg_of_slope23Fifths
      factorTwoIntrinsicStep01Slope_twentyThree_fifths_le 1 0
  unfold YoshidaFactorTwoPhaseIntrinsicLowControlsPositive.factorTwoIntrinsicBoundaryControlStep01
    at hstep
  have h0 := lowDetPlus_mul_oddPlus_eq_control0
  rw [lowCoefficientOne_eq_three_control1]
  nlinarith

private def evenEndpointQuadratic (sigma z0 z2 z4 : ℝ) : ℝ :=
  symmetricQuadratic
    (factorTwoStructuralPhaseLow00 sigma)
    (factorTwoStructuralPhaseLow02 sigma)
    (factorTwoIntrinsicFourP45Cross04 sigma)
    (factorTwoStructuralPhaseLow22 sigma)
    (factorTwoIntrinsicFourP45Cross24 sigma)
    (factorTwoIntrinsicSixP4Diagonal sigma)
    z0 z2 z4

private def schurVector0 : ℝ :=
  -(factorTwoStructuralPhaseLow22 1 *
      factorTwoIntrinsicFourP45Cross04 1 -
    factorTwoStructuralPhaseLow02 1 *
      factorTwoIntrinsicFourP45Cross24 1)

private def schurVector2 : ℝ :=
  -(-factorTwoStructuralPhaseLow02 1 *
      factorTwoIntrinsicFourP45Cross04 1 +
    factorTwoStructuralPhaseLow00 1 *
      factorTwoIntrinsicFourP45Cross24 1)

private def schurVector4 : ℝ := lowDetPlus

private theorem endpointBudget_eq_endpointQuadratics (z0 z2 z4 : ℝ) :
    endpointBudget z0 z2 z4 =
      evenEndpointQuadratic (-1) z0 z2 z4 +
        3 * evenEndpointQuadratic 1 z0 z2 z4 := by
  unfold endpointBudget evenEndpointQuadratic symmetricQuadratic
  ring

private theorem plusQuadratic_schurVector :
    evenEndpointQuadratic 1 schurVector0 schurVector2 schurVector4 =
      lowDetPlus * evenEndpointDet 1 := by
  unfold evenEndpointQuadratic schurVector0 schurVector2 schurVector4
    lowDetPlus evenEndpointDet symmetricQuadratic symmetricDeterminant
  ring

private theorem coefficient_block_identity :
    lowDetPlus *
        (evenEndpointDet 1 * factorTwoIntrinsicOddPhaseLow11 (-1) +
          evenMixedOne * factorTwoIntrinsicOddPhaseLow11 1 -
          alternatingPlusAdjugate) =
      evenEndpointDet 1 * lowCoefficientOne +
        factorTwoIntrinsicOddPhaseLow11 1 *
          evenEndpointQuadratic (-1)
            schurVector0 schurVector2 schurVector4 -
        (factorTwoIntrinsicAlternating01 * schurVector0 +
          factorTwoIntrinsicAlternating21 * schurVector2 +
          factorTwoIntrinsicFourP45Cross41 * schurVector4) ^ 2 := by
  unfold evenEndpointDet evenMixedOne alternatingPlusAdjugate
    lowCoefficientOne lowMixedOne lowAlternatingPlusAdjugate
    evenEndpointQuadratic schurVector0 schurVector2 schurVector4
    lowDetPlus
    mixedDeterminantOne symmetricDeterminant symmetricQuadratic
    adjugateQuadratic
  ring

private theorem lowDetPlus_pos : 0 < lowDetPlus := by
  have h := factorTwoIntrinsicEven_plus_endpoint_structural_gates.2
  simpa only [lowDetPlus, factorTwoIntrinsicEvenPhaseDet] using h

private theorem evenEndpointDet_plus_pos : 0 < evenEndpointDet 1 := by
  have h := factorTwoIntrinsicSixP4SchurLeading_plus_pos
  rw [factorTwoIntrinsicSixP4SchurLeading_eq_P024Determinant] at h
  simpa only [evenEndpointDet, factorTwoIntrinsicP024Determinant] using h

/-- The first mixed coefficient of the raw `P0/P2/P4/P1` determinant is
nonnegative.  The proof uses the exact first Bernstein step on `P0/P2/P1`
and a single three-dimensional adjugate Cauchy inequality for the `P4`
extension. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_one_nonneg :
    0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 1 := by
  rw [coefficient_one_eq_explicit]
  let L : ℝ :=
    factorTwoIntrinsicAlternating01 * schurVector0 +
      factorTwoIntrinsicAlternating21 * schurVector2 +
      factorTwoIntrinsicFourP45Cross41 * schurVector4
  have hCauchy := alternating_cauchy_endpointBudget
    schurVector0 schurVector2 schurVector4
  have hbudget := endpointBudget_eq_endpointQuadratics
    schurVector0 schurVector2 schurVector4
  have hplus := plusQuadratic_schurVector
  have hlow := lowCoefficientOne_lower
  have hlowScaled := mul_le_mul_of_nonneg_left hlow
    evenEndpointDet_plus_pos.le
  have hCauchy' :
      L ^ 2 ≤
        factorTwoIntrinsicOddPhaseLow11 1 *
          (evenEndpointQuadratic (-1)
              schurVector0 schurVector2 schurVector4 +
            3 * (lowDetPlus * evenEndpointDet 1)) := by
    dsimp only [L]
    rw [hbudget, hplus] at hCauchy
    exact hCauchy
  have hcore : 0 ≤
      evenEndpointDet 1 * lowCoefficientOne +
        factorTwoIntrinsicOddPhaseLow11 1 *
          evenEndpointQuadratic (-1)
            schurVector0 schurVector2 schurVector4 - L ^ 2 := by
    have hchain : L ^ 2 ≤
        factorTwoIntrinsicOddPhaseLow11 1 *
            evenEndpointQuadratic (-1)
              schurVector0 schurVector2 schurVector4 +
          evenEndpointDet 1 * lowCoefficientOne := by
      calc
        L ^ 2 ≤
            factorTwoIntrinsicOddPhaseLow11 1 *
              (evenEndpointQuadratic (-1)
                  schurVector0 schurVector2 schurVector4 +
                3 * (lowDetPlus * evenEndpointDet 1)) := hCauchy'
        _ = factorTwoIntrinsicOddPhaseLow11 1 *
              evenEndpointQuadratic (-1)
                schurVector0 schurVector2 schurVector4 +
            evenEndpointDet 1 *
              (3 * lowDetPlus * factorTwoIntrinsicOddPhaseLow11 1) := by
          ring
        _ ≤ factorTwoIntrinsicOddPhaseLow11 1 *
              evenEndpointQuadratic (-1)
                schurVector0 schurVector2 schurVector4 +
            evenEndpointDet 1 * lowCoefficientOne :=
          add_le_add_right hlowScaled
            (factorTwoIntrinsicOddPhaseLow11 1 *
              evenEndpointQuadratic (-1)
                schurVector0 schurVector2 schurVector4)
    dsimp only [L] at hchain ⊢
    linarith
  have hidentity := coefficient_block_identity
  dsimp only [L] at hcore
  have hscaled : 0 ≤ lowDetPlus *
      (evenEndpointDet 1 * factorTwoIntrinsicOddPhaseLow11 (-1) +
        evenMixedOne * factorTwoIntrinsicOddPhaseLow11 1 -
        alternatingPlusAdjugate) := by
    rw [hidentity]
    exact hcore
  have hscaled' : 0 ≤
      (evenEndpointDet 1 * factorTwoIntrinsicOddPhaseLow11 (-1) +
        evenMixedOne * factorTwoIntrinsicOddPhaseLow11 1 -
        alternatingPlusAdjugate) * lowDetPlus := by
    simpa only [mul_comm] using hscaled
  exact nonneg_of_mul_nonneg_left hscaled' lowDetPlus_pos

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC1Structural
