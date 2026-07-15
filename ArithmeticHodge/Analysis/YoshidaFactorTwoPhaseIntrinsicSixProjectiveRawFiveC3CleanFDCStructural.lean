import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC3Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3PerturbationStructural

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3Structural

noncomputable section

open Polynomial
open CenteredOddOneThreeEnergy
open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur
open YoshidaEndpointOddFullPolarization
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural positivity of the third raw five-mode coefficient

This coefficient is the endpoint reversal of the second convolution layer.
The proof keeps that reversal at the level of the even adjugate pencil and
the odd endpoint pencil; it does not enumerate values of the projective
parameter.
-/

/-! ### Restoring the clean aligned coordinates

At this point every perturbation and alternating coordinate is back at its
correlated value.  The remaining five moves follow the aligned coordinates
themselves.  Each move uses one exact quadratic secant, so no projective
coefficient list is expanded or checked pointwise. -/

def correlatedDeterminantBlock
    (A X R C D F a x r c d f q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  let Ap := A - a
  let Xp := X - x
  let Rp := R - r
  let Cp := C - c
  let Dp := D - d
  let Fp := F - f
  let Am := A + a
  let Xm := X + x
  let Rm := R + r
  let Cm := C + c
  let Dm := D + d
  let Fm := F + f
  let o11p := q11 + h11
  let o13p := q13 + h13
  let o33p := q33 + h33
  let o11m := q11 - h11
  let o13m := q13 - h13
  let o33m := q33 - h33
  let oddPlus := o11p * o33p - o13p ^ 2
  let oddMixed := o11p * o33m + o11m * o33p - 2 * o13p * o13m
  let oddMinus := o11m * o33m - o13m ^ 2
  alignedMixedDeterminant Ap Xp Rp Cp Dp Fp Am Xm Rm Cm Dm Fm * oddMinus +
    alignedMixedDeterminant Am Xm Rm Cm Dm Fm Ap Xp Rp Cp Dp Fp * oddMixed +
    alignedDeterminant Am Xm Rm Cm Dm Fm * oddPlus

def correlatedCouplingBlock
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  let Ap := A - a
  let Xp := X - x
  let Rp := R - r
  let Cp := C - c
  let Dp := D - d
  let Fp := F - f
  let Am := A + a
  let Xm := X + x
  let Rm := R + r
  let Cm := C + c
  let Dm := D + d
  let Fm := F + f
  let o11p := q11 + h11
  let o13p := q13 + h13
  let o33p := q33 + h33
  let o11m := q11 - h11
  let o13m := q13 - h13
  let o33m := q33 - h33
  let minusCoupling :=
    o33p * alignedAdjugatePair Am Xm Rm Cm Dm Fm su du u4 su du u4 -
      2 * o13p * alignedAdjugatePair Am Xm Rm Cm Dm Fm su du u4 sv dv v4 +
      o11p * alignedAdjugatePair Am Xm Rm Cm Dm Fm sv dv v4 sv dv v4
  let mixedCoupling :=
    o33m * alignedMixedAdjugatePair Ap Xp Rp Cp Dp Fp
        Am Xm Rm Cm Dm Fm su du u4 su du u4 -
      2 * o13m * alignedMixedAdjugatePair Ap Xp Rp Cp Dp Fp
        Am Xm Rm Cm Dm Fm su du u4 sv dv v4 +
      o11m * alignedMixedAdjugatePair Ap Xp Rp Cp Dp Fp
        Am Xm Rm Cm Dm Fm sv dv v4 sv dv v4
  (-minusCoupling) - mixedCoupling

def correlatedCrossBlock
    (A X R C D F f su du u4 sv dv v4 : ℝ) : ℝ :=
  alignedCrossEnergy A X R C D (F + f) su du u4 sv dv v4

theorem correlatedCoefficientThree_eq_blocks
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    correlatedCoefficientThree A X R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 =
      correlatedDeterminantBlock A X R C D F a x r c d f
          q11 q13 q33 h11 h13 h33 +
        correlatedCouplingBlock A X R C D F a x r c d f
          su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 +
        correlatedCrossBlock (A + a) (X + x) (R + r) (C + c) (D + d)
          F f su du u4 sv dv v4 := by
  unfold correlatedCoefficientThree correlatedDeterminantBlock
    correlatedCouplingBlock correlatedCrossBlock
  dsimp only
  ring

private def alignedTopPair
    (A X C sx dx sy dy : ℝ) : ℝ :=
  C * sx * sy - X * (sx * dy + dx * sy) + A * dx * dy

private theorem alignedTopPair_bounds
    (A X C sx dx sy dy
      AL AU XL XU CL CU sxL sxU dxL dxU syL syU dyL dyU : ℝ)
    (hAL : AL ≤ A) (hAU : A ≤ AU)
    (hXL : XL ≤ X) (hXU : X ≤ XU)
    (hCL : CL ≤ C) (hCU : C ≤ CU)
    (hsxL : sxL ≤ sx) (hsxU : sx ≤ sxU)
    (hdxL : dxL ≤ dx) (hdxU : dx ≤ dxU)
    (hsyL : syL ≤ sy) (hsyU : sy ≤ syU)
    (hdyL : dyL ≤ dy) (hdyU : dy ≤ dyU)
    (hAL0 : 0 ≤ AL) (hXL0 : 0 ≤ XL) (hCL0 : 0 ≤ CL)
    (hsxL0 : 0 ≤ sxL) (hdxL0 : 0 ≤ dxL)
    (hsyL0 : 0 ≤ syL) (hdyL0 : 0 ≤ dyL) :
    CL * sxL * syL - XU * (sxU * dyU + dxU * syU) +
        AL * dxL * dyL ≤ alignedTopPair A X C sx dx sy dy ∧
      alignedTopPair A X C sx dx sy dy ≤
        CU * sxU * syU - XL * (sxL * dyL + dxL * syL) +
          AU * dxU * dyU := by
  have hA0 : 0 ≤ A := le_trans hAL0 hAL
  have hX0 : 0 ≤ X := le_trans hXL0 hXL
  have hC0 : 0 ≤ C := le_trans hCL0 hCL
  have hsx0 : 0 ≤ sx := le_trans hsxL0 hsxL
  have hdx0 : 0 ≤ dx := le_trans hdxL0 hdxL
  have hsy0 : 0 ≤ sy := le_trans hsyL0 hsyL
  have hdy0 : 0 ≤ dy := le_trans hdyL0 hdyL
  have hAU0 : 0 ≤ AU := le_trans hA0 hAU
  have hXU0 : 0 ≤ XU := le_trans hX0 hXU
  have hCU0 : 0 ≤ CU := le_trans hC0 hCU
  have hsxU0 : 0 ≤ sxU := le_trans hsx0 hsxU
  have hdxU0 : 0 ≤ dxU := le_trans hdx0 hdxU
  have hsyU0 : 0 ≤ syU := le_trans hsy0 hsyU
  have hdyU0 : 0 ≤ dyU := le_trans hdy0 hdyU
  have hCLower := nonnegative_triple_lower
    C sx sy CL sxL syL hCL hsxL hsyL hCL0 hsxL0 hsx0 hsy0
  have hCUpper := nonnegative_triple_upper
    C sx sy CU sxU syU hCU hsxU hsyU hCU0 hsxU0 hsx0 hsy0
  have hXsxdyLower := nonnegative_triple_lower
    X sx dy XL sxL dyL hXL hsxL hdyL hXL0 hsxL0 hsx0 hdy0
  have hXsxdyUpper := nonnegative_triple_upper
    X sx dy XU sxU dyU hXU hsxU hdyU hXU0 hsxU0 hsx0 hdy0
  have hXdxsyLower := nonnegative_triple_lower
    X dx sy XL dxL syL hXL hdxL hsyL hXL0 hdxL0 hdx0 hsy0
  have hXdxsyUpper := nonnegative_triple_upper
    X dx sy XU dxU syU hXU hdxU hsyU hXU0 hdxU0 hdx0 hsy0
  have hALower := nonnegative_triple_lower
    A dx dy AL dxL dyL hAL hdxL hdyL hAL0 hdxL0 hdx0 hdy0
  have hAUpper := nonnegative_triple_upper
    A dx dy AU dxU dyU hAU hdxU hdyU hAU0 hdxU0 hdx0 hdy0
  constructor <;> unfold alignedTopPair <;>
    nlinarith only [hCLower, hCUpper, hXsxdyLower, hXsxdyUpper,
      hXdxsyLower, hXdxsyUpper, hALower, hAUpper]

private def cleanFSecant
    (a x c su du sv dv q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  let Ap := cornerA - a
  let Xp := cornerX - x
  let Cp := cornerC - c
  let Am := cornerA + a
  let Xm := cornerX + x
  let Cm := cornerC + c
  let topMinus := Ap * Cp - Xp ^ 2
  let topMixed := Ap * Cm + Am * Cp - 2 * Xp * Xm
  let topPlus := Am * Cm - Xm ^ 2
  let o11p := q11 + h11
  let o13p := q13 + h13
  let o33p := q33 + h33
  let o11m := q11 - h11
  let o13m := q13 - h13
  let o33m := q33 - h33
  let oddPlus := o11p * o33p - o13p ^ 2
  let oddMixed := o11p * o33m + o11m * o33p - 2 * o13p * o13m
  let oddMinus := o11m * o33m - o13m ^ 2
  let plusCoupling :=
    (o33p * alignedTopPair Am Xm Cm su du su du -
      2 * o13p * alignedTopPair Am Xm Cm su du sv dv +
      o11p * alignedTopPair Am Xm Cm sv dv sv dv) / 4
  let minusCoupling :=
    (o33m * alignedTopPair cornerA cornerX cornerC su du su du -
      2 * o13m * alignedTopPair cornerA cornerX cornerC su du sv dv +
      o11m * alignedTopPair cornerA cornerX cornerC sv dv sv dv) / 2
  (topMinus + topMixed) * oddMinus / 4 +
    (topPlus + topMixed) * oddMixed / 4 + topPlus * oddPlus / 4 -
    plusCoupling - minusCoupling + (du * sv - su * dv) ^ 2 / 4

private theorem clean_f_secant_eq
    (F a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    quadraticSecant
        (fun z ↦ correlatedCoefficientThree
          cornerA cornerX cornerR cornerC cornerD z
          a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33)
        F cornerF =
      cleanFSecant a x c su du sv dv q11 q13 q33 h11 h13 h33 := by
  unfold quadraticSecant correlatedCoefficientThree cleanFSecant alignedTopPair
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00 alignedEntry02
    alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

set_option maxHeartbeats 3000000 in
private theorem cleanFSecant_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (1 / 1000000 : ℝ) ≤
      cleanFSecant a x c su du sv dv q11 q13 q33 h11 h13 h33 := by
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at haL haU hxL hxU hcL hcU hsuL hsuU hduL hduU hsvL hsvU hdvL hdvU hq11L hq11U hq13L hq13U hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
  rcases oddASlope_bounds A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox with
    ⟨hOddMinus, hOddMixed, hOddPlus⟩
  have ha0 : 0 ≤ a := by linarith only [haL]
  have hx0 : 0 ≤ x := by linarith only [hxL]
  have hc0 : 0 ≤ c := by linarith only [hcL]
  have hacL := nonnegative_product_lower
    a c (824479 / 1000000) (5179 / 1000000)
    haL hcL (by norm_num) hc0
  have hacU := nonnegative_product_upper
    a c (165293 / 200000) (1433 / 200000)
    haU hcU (by norm_num) hc0
  have hxxL := nonnegative_product_lower
    x x (37851 / 1000000) (37851 / 1000000)
    hxL hxL (by norm_num) hx0
  have hxxU := nonnegative_product_upper
    x x (39761 / 1000000) (39761 / 1000000)
    hxU hxU (by norm_num) hx0
  have hTopMinusMixed : (257 / 10000 : ℝ) ≤
      ((cornerA - a) * (cornerC - c) - (cornerX - x) ^ 2) +
        ((cornerA - a) * (cornerC + c) +
          (cornerA + a) * (cornerC - c) -
            2 * (cornerX - x) * (cornerX + x)) := by
    norm_num [cornerA, cornerX, cornerC] at ⊢
    ring_nf
    nlinarith only [haU, hxL, hcU, hacU, hxxL]
  have hTopPlusMixed : (583 / 10000 : ℝ) ≤
      ((cornerA + a) * (cornerC + c) - (cornerX + x) ^ 2) +
        ((cornerA - a) * (cornerC + c) +
          (cornerA + a) * (cornerC - c) -
            2 * (cornerX - x) * (cornerX + x)) := by
    norm_num [cornerA, cornerX, cornerC] at ⊢
    ring_nf
    nlinarith only [haL, hxU, hcL, hacU, hxxL]
  have hTopPlus : (341 / 10000 : ℝ) ≤
      (cornerA + a) * (cornerC + c) - (cornerX + x) ^ 2 := by
    norm_num [cornerA, cornerX, cornerC] at ⊢
    ring_nf
    nlinarith only [haL, hxU, hcL, hacL, hxxU]
  have hDetOne := nonnegative_product_lower
    (((cornerA - a) * (cornerC - c) - (cornerX - x) ^ 2) +
      ((cornerA - a) * (cornerC + c) +
        (cornerA + a) * (cornerC - c) -
          2 * (cornerX - x) * (cornerX + x)))
    ((q11 - h11) * (q33 - h33) - (q13 - h13) ^ 2)
    (257 / 10000) (26 / 1000) hTopMinusMixed hOddMinus
    (by norm_num) (by linarith only [hOddMinus])
  have hDetTwo := nonnegative_product_lower
    (((cornerA + a) * (cornerC + c) - (cornerX + x) ^ 2) +
      ((cornerA - a) * (cornerC + c) +
        (cornerA + a) * (cornerC - c) -
          2 * (cornerX - x) * (cornerX + x)))
    ((q11 + h11) * (q33 - h33) +
      (q11 - h11) * (q33 + h33) -
        2 * (q13 + h13) * (q13 - h13))
    (583 / 10000) (41 / 1000) hTopPlusMixed hOddMixed
    (by norm_num) (by linarith only [hOddMixed])
  have hDetThree := nonnegative_product_lower
    ((cornerA + a) * (cornerC + c) - (cornerX + x) ^ 2)
    ((q11 + h11) * (q33 + h33) - (q13 + h13) ^ 2)
    (341 / 10000) (4 / 1000) hTopPlus hOddPlus
    (by norm_num) (by linarith only [hOddPlus])
  have hDet : (31949 / 40000000 : ℝ) ≤
      (((cornerA - a) * (cornerC - c) - (cornerX - x) ^ 2 +
          ((cornerA - a) * (cornerC + c) +
            (cornerA + a) * (cornerC - c) -
              2 * (cornerX - x) * (cornerX + x))) *
        ((q11 - h11) * (q33 - h33) - (q13 - h13) ^ 2) +
      ((cornerA + a) * (cornerC + c) - (cornerX + x) ^ 2 +
          ((cornerA - a) * (cornerC + c) +
            (cornerA + a) * (cornerC - c) -
              2 * (cornerX - x) * (cornerX + x))) *
        ((q11 + h11) * (q33 - h33) +
          (q11 - h11) * (q33 + h33) -
            2 * (q13 + h13) * (q13 - h13)) +
      ((cornerA + a) * (cornerC + c) - (cornerX + x) ^ 2) *
        ((q11 + h11) * (q33 + h33) - (q13 + h13) ^ 2)) / 4 := by
    nlinarith only [hDetOne, hDetTwo, hDetThree]
  have hApL : (2198709 / 1000000 : ℝ) ≤ cornerA + a := by
    norm_num [cornerA] at ⊢
    linarith only [haL]
  have hApU : cornerA + a ≤ (2200695 / 1000000 : ℝ) := by
    norm_num [cornerA] at ⊢
    linarith only [haU]
  have hXpL : (77621 / 1000000 : ℝ) ≤ cornerX + x := by
    norm_num [cornerX] at ⊢
    linarith only [hxL]
  have hXpU : cornerX + x ≤ (79531 / 1000000 : ℝ) := by
    norm_num [cornerX] at ⊢
    linarith only [hxU]
  have hCpL : (18409 / 1000000 : ℝ) ≤ cornerC + c := by
    norm_num [cornerC] at ⊢
    linarith only [hcL]
  have hCpU : cornerC + c ≤ (20395 / 1000000 : ℝ) := by
    norm_num [cornerC] at ⊢
    linarith only [hcU]
  have hPuuBounds := alignedTopPair_bounds
    (cornerA + a) (cornerX + x) (cornerC + c) su du su du
    (2198709 / 1000000) (2200695 / 1000000)
    (77621 / 1000000) (79531 / 1000000)
    (18409 / 1000000) (20395 / 1000000)
    (7021 / 12500) (56173 / 100000)
    (1687 / 100000) (423 / 25000)
    (7021 / 12500) (56173 / 100000)
    (1687 / 100000) (423 / 25000)
    hApL hApU hXpL hXpU hCpL hCpU
    hsuL hsuU hduL hduU hsuL hsuU hduL hduU
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hPuvBounds := alignedTopPair_bounds
    (cornerA + a) (cornerX + x) (cornerC + c) su du sv dv
    (2198709 / 1000000) (2200695 / 1000000)
    (77621 / 1000000) (79531 / 1000000)
    (18409 / 1000000) (20395 / 1000000)
    (7021 / 12500) (56173 / 100000)
    (1687 / 100000) (423 / 25000)
    (10763 / 20000) (13459 / 25000)
    (111 / 2000) (279 / 5000)
    hApL hApU hXpL hXpU hCpL hCpU
    hsuL hsuU hduL hduU hsvL hsvU hdvL hdvU
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hPvvBounds := alignedTopPair_bounds
    (cornerA + a) (cornerX + x) (cornerC + c) sv dv sv dv
    (2198709 / 1000000) (2200695 / 1000000)
    (77621 / 1000000) (79531 / 1000000)
    (18409 / 1000000) (20395 / 1000000)
    (10763 / 20000) (13459 / 25000)
    (111 / 2000) (279 / 5000)
    (10763 / 20000) (13459 / 25000)
    (111 / 2000) (279 / 5000)
    hApL hApU hXpL hXpU hCpL hCpU
    hsvL hsvU hdvL hdvU hsvL hsvU hdvL hdvU
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hMuuBounds := alignedTopPair_bounds
    cornerA cornerX cornerC su du su du
    cornerA cornerA cornerX cornerX cornerC cornerC
    (7021 / 12500) (56173 / 100000)
    (1687 / 100000) (423 / 25000)
    (7021 / 12500) (56173 / 100000)
    (1687 / 100000) (423 / 25000)
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    hsuL hsuU hduL hduU hsuL hsuU hduL hduU
    (by norm_num [cornerA]) (by norm_num [cornerX])
    (by norm_num [cornerC]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hMuvBounds := alignedTopPair_bounds
    cornerA cornerX cornerC su du sv dv
    cornerA cornerA cornerX cornerX cornerC cornerC
    (7021 / 12500) (56173 / 100000)
    (1687 / 100000) (423 / 25000)
    (10763 / 20000) (13459 / 25000)
    (111 / 2000) (279 / 5000)
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    hsuL hsuU hduL hduU hsvL hsvU hdvL hdvU
    (by norm_num [cornerA]) (by norm_num [cornerX])
    (by norm_num [cornerC]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hMvvBounds := alignedTopPair_bounds
    cornerA cornerX cornerC sv dv sv dv
    cornerA cornerA cornerX cornerX cornerC cornerC
    (10763 / 20000) (13459 / 25000)
    (111 / 2000) (279 / 5000)
    (10763 / 20000) (13459 / 25000)
    (111 / 2000) (279 / 5000)
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    hsvL hsvU hdvL hdvU hsvL hsvU hdvL hdvU
    (by norm_num [cornerA]) (by norm_num [cornerX])
    (by norm_num [cornerC]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hPuuL : (49 / 10000 : ℝ) ≤ alignedTopPair
      (cornerA + a) (cornerX + x) (cornerC + c) su du su du :=
    le_trans (by norm_num) hPuuBounds.1
  have hPuuU : alignedTopPair
      (cornerA + a) (cornerX + x) (cornerC + c) su du su du ≤
        (56 / 10000 : ℝ) := le_trans hPuuBounds.2 (by norm_num)
  have hPuvL : (44 / 10000 : ℝ) ≤ alignedTopPair
      (cornerA + a) (cornerX + x) (cornerC + c) su du sv dv :=
    le_trans (by norm_num) hPuvBounds.1
  have hPvvL : (73 / 10000 : ℝ) ≤ alignedTopPair
      (cornerA + a) (cornerX + x) (cornerC + c) sv dv sv dv :=
    le_trans (by norm_num) hPvvBounds.1
  have hPvvU : alignedTopPair
      (cornerA + a) (cornerX + x) (cornerC + c) sv dv sv dv ≤
        (82 / 10000 : ℝ) := le_trans hPvvBounds.2 (by norm_num)
  have hMuuL : (38 / 10000 : ℝ) ≤
      alignedTopPair cornerA cornerX cornerC su du su du :=
    le_trans (by norm_num [cornerA, cornerX, cornerC]) hMuuBounds.1
  have hMuuU : alignedTopPair cornerA cornerX cornerC su du su du ≤
      (382 / 100000 : ℝ) :=
    le_trans hMuuBounds.2 (by norm_num [cornerA, cornerX, cornerC])
  have hMuvL : (367 / 100000 : ℝ) ≤
      alignedTopPair cornerA cornerX cornerC su du sv dv :=
    le_trans (by norm_num [cornerA, cornerX, cornerC]) hMuvBounds.1
  have hMvvL : (56 / 10000 : ℝ) ≤
      alignedTopPair cornerA cornerX cornerC sv dv sv dv :=
    le_trans (by norm_num [cornerA, cornerX, cornerC]) hMvvBounds.1
  have hMvvU : alignedTopPair cornerA cornerX cornerC sv dv sv dv ≤
      (574 / 100000 : ℝ) :=
    le_trans hMvvBounds.2 (by norm_num [cornerA, cornerX, cornerC])
  have hp1 : (q33 + h33) * alignedTopPair
      (cornerA + a) (cornerX + x) (cornerC + c) su du su du / 4 ≤
        (3235 / 10000000 : ℝ) := by
    have hq : q33 + h33 ≤ (216 / 1000 : ℝ) := by
      linarith only [hq33U, hh33U]
    have hpairL : (49 / 10000 : ℝ) ≤ alignedTopPair
        (cornerA + a) (cornerX + x) (cornerC + c) su du su du := hPuuL
    have hpairU : alignedTopPair
        (cornerA + a) (cornerX + x) (cornerC + c) su du su du ≤
          (56 / 10000 : ℝ) := hPuuU
    have hprod := nonnegative_product_upper
      (q33 + h33)
      (alignedTopPair (cornerA + a) (cornerX + x) (cornerC + c)
        su du su du)
      (216 / 1000) (56 / 10000) hq hpairU
      (by norm_num) (by linarith only [hpairL])
    nlinarith only [hprod]
  have hp2 : -2 * (q13 + h13) * alignedTopPair
      (cornerA + a) (cornerX + x) (cornerC + c) su du sv dv / 4 ≤
        (-4089 / 10000000 : ℝ) := by
    have hq : (189 / 1000 : ℝ) ≤ q13 + h13 := by
      linarith only [hq13L, hh13L]
    have hpair : (44 / 10000 : ℝ) ≤ alignedTopPair
        (cornerA + a) (cornerX + x) (cornerC + c) su du sv dv := hPuvL
    have hprod := nonnegative_product_lower
      (q13 + h13)
      (alignedTopPair (cornerA + a) (cornerX + x) (cornerC + c)
        su du sv dv)
      (189 / 1000) (44 / 10000) hq hpair
      (by norm_num) (by linarith only [hpair])
    nlinarith only [hprod]
  have hp3 : (q11 + h11) * alignedTopPair
      (cornerA + a) (cornerX + x) (cornerC + c) sv dv sv dv / 4 ≤
        (4127 / 10000000 : ℝ) := by
    have hq : q11 + h11 ≤ (199 / 1000 : ℝ) := by
      linarith only [hq11U, hh11U]
    have hpairL : (73 / 10000 : ℝ) ≤ alignedTopPair
        (cornerA + a) (cornerX + x) (cornerC + c) sv dv sv dv := hPvvL
    have hpairU : alignedTopPair
        (cornerA + a) (cornerX + x) (cornerC + c) sv dv sv dv ≤
          (82 / 10000 : ℝ) := hPvvU
    have hprod := nonnegative_product_upper
      (q11 + h11)
      (alignedTopPair (cornerA + a) (cornerX + x) (cornerC + c)
        sv dv sv dv)
      (199 / 1000) (82 / 10000) hq hpairU
      (by norm_num) (by linarith only [hpairL])
    nlinarith only [hprod]
  have hPlusCoupling :
      ((q33 + h33) * alignedTopPair
          (cornerA + a) (cornerX + x) (cornerC + c) su du su du -
        2 * (q13 + h13) * alignedTopPair
          (cornerA + a) (cornerX + x) (cornerC + c) su du sv dv +
        (q11 + h11) * alignedTopPair
          (cornerA + a) (cornerX + x) (cornerC + c) sv dv sv dv) / 4 ≤
        (328 / 1000000 : ℝ) := by
    nlinarith only [hp1, hp2, hp3]
  have hm1 : (q33 - h33) * alignedTopPair
      cornerA cornerX cornerC su du su du / 2 ≤ (866 / 1000000 : ℝ) := by
    have hq : q33 - h33 ≤ (453 / 1000 : ℝ) := by
      linarith only [hq33U, hh33L]
    have hpairL : (38 / 10000 : ℝ) ≤
        alignedTopPair cornerA cornerX cornerC su du su du := hMuuL
    have hpairU : alignedTopPair cornerA cornerX cornerC su du su du ≤
        (382 / 100000 : ℝ) := hMuuU
    have hprod := nonnegative_product_upper
      (q33 - h33) (alignedTopPair cornerA cornerX cornerC su du su du)
      (453 / 1000) (382 / 100000) hq hpairU
      (by norm_num) (by linarith only [hpairL])
    nlinarith only [hprod]
  have hm2 : -2 * (q13 - h13) * alignedTopPair
      cornerA cornerX cornerC su du sv dv / 2 ≤
        (-7649 / 10000000 : ℝ) := by
    have hq : (209 / 1000 : ℝ) ≤ q13 - h13 := by
      linarith only [hq13L, hh13U]
    have hpair : (367 / 100000 : ℝ) ≤
        alignedTopPair cornerA cornerX cornerC su du sv dv := hMuvL
    have hprod := nonnegative_product_lower
      (q13 - h13) (alignedTopPair cornerA cornerX cornerC su du sv dv)
      (209 / 1000) (367 / 100000) hq hpair
      (by norm_num) (by linarith only [hpair])
    nlinarith only [hprod]
  have hm3 : (q11 - h11) * alignedTopPair
      cornerA cornerX cornerC sv dv sv dv / 2 ≤
        (4824 / 10000000 : ℝ) := by
    have hq : q11 - h11 ≤ (165 / 1000 : ℝ) := by
      linarith only [hq11U, hh11L]
    have hpairL : (56 / 10000 : ℝ) ≤
        alignedTopPair cornerA cornerX cornerC sv dv sv dv := hMvvL
    have hpairU : alignedTopPair cornerA cornerX cornerC sv dv sv dv ≤
        (574 / 100000 : ℝ) := hMvvU
    have hprod := nonnegative_product_upper
      (q11 - h11) (alignedTopPair cornerA cornerX cornerC sv dv sv dv)
      (165 / 1000) (574 / 100000) hq hpairU
      (by norm_num) (by linarith only [hpairL])
    nlinarith only [hprod]
  have hMinusCoupling :
      ((q33 - h33) * alignedTopPair cornerA cornerX cornerC su du su du -
        2 * (q13 - h13) * alignedTopPair
          cornerA cornerX cornerC su du sv dv +
        (q11 - h11) * alignedTopPair
          cornerA cornerX cornerC sv dv sv dv) / 2 ≤
        (584 / 1000000 : ℝ) := by
    nlinarith only [hm1, hm2, hm3]
  have hsuDv : (56168 / 100000 : ℝ) * (555 / 10000) ≤ su * dv := by
    bound
  have hduSv : du * sv ≤ (1692 / 100000 : ℝ) * (53836 / 100000) := by
    bound
  have hgap : (22 / 1000 : ℝ) ≤ su * dv - du * sv := by
    nlinarith only [hsuDv, hduSv]
  have hsq : (22 / 1000 : ℝ) ^ 2 ≤ (su * dv - du * sv) ^ 2 := by
    have hprod := mul_nonneg
      (by linarith only [hgap] : 0 ≤ su * dv - du * sv - 22 / 1000)
      (by linarith only [hgap] : 0 ≤ su * dv - du * sv + 22 / 1000)
    nlinarith only [hprod]
  have hCross : (12 / 100000 : ℝ) ≤ (du * sv - su * dv) ^ 2 / 4 := by
    nlinarith only [hsq]
  unfold cleanFSecant
  dsimp only
  nlinarith only [hDet, hPlusCoupling, hMinusCoupling, hCross]

set_option maxHeartbeats 3000000 in
theorem correlated_clean_unfix_F
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 ≤
      correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD F
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := by
  let g : ℝ → ℝ := fun z ↦ correlatedCoefficientThree
    cornerA cornerX cornerR cornerC cornerD z
    a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33
  have hslope := cleanFSecant_lower A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hsecFloor : (1 / 1000000 : ℝ) ≤ quadraticSecant g F cornerF := by
    rw [show quadraticSecant g F cornerF =
        cleanFSecant a x c su du sv dv q11 q13 q33 h11 h13 h33 by
      simpa only [g] using clean_f_secant_eq F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33]
    exact hslope
  have hsec : (0 : ℝ) ≤ quadraticSecant g F cornerF :=
    le_trans (by norm_num) hsecFloor
  have hid : g F - g cornerF =
      (F - cornerF) * quadraticSecant g F cornerF := by
    unfold g quadraticSecant correlatedCoefficientThree alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  exact quadraticSecant_lower_endpoint g F cornerF
    (by simpa only [cornerF] using hbox.F_mem.1) hsec hid

private theorem correlated_cross_gap_bounds
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (77 / 1000 : ℝ) ≤ u4 * sv - v4 * su ∧
      (22 / 1000 : ℝ) ≤ su * dv - du * sv := by
  rcases hbox.su_mem with ⟨hsuL, _⟩
  rcases hbox.du_mem with ⟨_, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, _⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, _⟩
  rcases hbox.v4_mem with ⟨_, hv4U⟩
  have hsu0 : 0 ≤ su := by linarith only [hsuL]
  have hsv0 : 0 ≤ sv := by linarith only [hsvL]
  have hdv0 : 0 ≤ dv := by linarith only [hdvL]
  have hnv4L : (1 / 500 : ℝ) ≤ -v4 := by linarith only [hv4U]
  have hu4svL := nonnegative_product_lower
    u4 sv (141 / 1000) (53815 / 100000)
    hu4L hsvL (by norm_num) hsv0
  have hnv4suL := nonnegative_product_lower
    (-v4) su (1 / 500) (56168 / 100000)
    hnv4L hsuL (by norm_num) hsu0
  have hsudvL := nonnegative_product_lower
    su dv (56168 / 100000) (555 / 10000)
    hsuL hdvL (by norm_num) hdv0
  have hdusvU := nonnegative_product_upper
    du sv (1692 / 100000) (53836 / 100000)
    hduU hsvU (by norm_num) hsv0
  constructor <;>
    nlinarith only [hu4svL, hnv4suL, hsudvL, hdusvU]

private theorem oddCouplingCross_negative_four_bounds
    (u z v w o11 o13 o33
      uL uU zL zU vL vU tL tU
      o11L o11U o13L o13U o33L o33U : ℝ)
    (huL : uL ≤ u) (huU : u ≤ uU)
    (hzL : zL ≤ z) (hzU : z ≤ zU)
    (hvL : vL ≤ v) (hvU : v ≤ vU)
    (htL : tL ≤ -w) (htU : -w ≤ tU)
    (ho11L : o11L ≤ o11) (ho11U : o11 ≤ o11U)
    (ho13L : o13L ≤ o13) (ho13U : o13 ≤ o13U)
    (ho33L : o33L ≤ o33) (ho33U : o33 ≤ o33U)
    (huL0 : 0 ≤ uL) (hzL0 : 0 ≤ zL) (hvL0 : 0 ≤ vL)
    (htL0 : 0 ≤ tL) (ho11L0 : 0 ≤ o11L)
    (ho13L0 : 0 ≤ o13L) (ho33L0 : 0 ≤ o33L) :
    o33L * uL * zL + o13L * uL * tL - o13U * zU * vU -
        o11U * vU * tU ≤
      oddCouplingCross u z v w o11 o13 o33 ∧
    oddCouplingCross u z v w o11 o13 o33 ≤
      o33U * uU * zU + o13U * uU * tU - o13L * zL * vL -
        o11L * vL * tL := by
  have hu0 : 0 ≤ u := le_trans huL0 huL
  have hz0 : 0 ≤ z := le_trans hzL0 hzL
  have hv0 : 0 ≤ v := le_trans hvL0 hvL
  have ht0 : 0 ≤ -w := le_trans htL0 htL
  have ho110 : 0 ≤ o11 := le_trans ho11L0 ho11L
  have ho130 : 0 ≤ o13 := le_trans ho13L0 ho13L
  have ho330 : 0 ≤ o33 := le_trans ho33L0 ho33L
  have huU0 : 0 ≤ uU := le_trans hu0 huU
  have hzU0 : 0 ≤ zU := le_trans hz0 hzU
  have hvU0 : 0 ≤ vU := le_trans hv0 hvU
  have htU0 : 0 ≤ tU := le_trans ht0 htU
  have ho11U0 : 0 ≤ o11U := le_trans ho110 ho11U
  have ho13U0 : 0 ≤ o13U := le_trans ho130 ho13U
  have ho33U0 : 0 ≤ o33U := le_trans ho330 ho33U
  have h33L := nonnegative_triple_lower
    o33 u z o33L uL zL ho33L huL hzL ho33L0 huL0 hu0 hz0
  have h33U := nonnegative_triple_upper
    o33 u z o33U uU zU ho33U huU hzU ho33U0 huU0 hu0 hz0
  have h13utL := nonnegative_triple_lower
    o13 u (-w) o13L uL tL ho13L huL htL ho13L0 huL0 hu0 ht0
  have h13utU := nonnegative_triple_upper
    o13 u (-w) o13U uU tU ho13U huU htU ho13U0 huU0 hu0 ht0
  have h13zvL := nonnegative_triple_lower
    o13 z v o13L zL vL ho13L hzL hvL ho13L0 hzL0 hz0 hv0
  have h13zvU := nonnegative_triple_upper
    o13 z v o13U zU vU ho13U hzU hvU ho13U0 hzU0 hz0 hv0
  have h11vtL := nonnegative_triple_lower
    o11 v (-w) o11L vL tL ho11L hvL htL ho11L0 hvL0 hv0 ht0
  have h11vtU := nonnegative_triple_upper
    o11 v (-w) o11U vU tU ho11U hvU htU ho11U0 hvU0 hv0 ht0
  constructor <;> unfold oddCouplingCross <;>
    nlinarith only [h33L, h33U, h13utL, h13utU, h13zvL, h13zvU,
      h11vtL, h11vtU]

private theorem oddCouplingFour_negative_upper
    (z w o11 o13 o33 zU tU o11U o13U o33U : ℝ)
    (hzU : z ≤ zU) (htU : -w ≤ tU)
    (ho11U : o11 ≤ o11U) (ho13U : o13 ≤ o13U)
    (ho33U : o33 ≤ o33U)
    (hz0 : 0 ≤ z) (ht0 : 0 ≤ -w)
    (ho110 : 0 ≤ o11) (ho130 : 0 ≤ o13) (ho330 : 0 ≤ o33) :
    oddCouplingFour z w o11 o13 o33 ≤
      o33U * zU * zU + 2 * o13U * zU * tU + o11U * tU * tU := by
  have hzU0 : 0 ≤ zU := le_trans hz0 hzU
  have htU0 : 0 ≤ tU := le_trans ht0 htU
  have ho11U0 : 0 ≤ o11U := le_trans ho110 ho11U
  have ho13U0 : 0 ≤ o13U := le_trans ho130 ho13U
  have ho33U0 : 0 ≤ o33U := le_trans ho330 ho33U
  have h33 := nonnegative_triple_upper
    o33 z z o33U zU zU ho33U hzU hzU ho33U0 hzU0 hz0 hz0
  have h13 := nonnegative_triple_upper
    o13 z (-w) o13U zU tU ho13U hzU htU ho13U0 hzU0 hz0 ht0
  have h11 := nonnegative_triple_upper
    o11 (-w) (-w) o11U tU tU ho11U htU htU
      ho11U0 htU0 ht0 ht0
  unfold oddCouplingFour
  nlinarith only [h33, h13, h11]

private theorem product_upper_of_nonnegative_left
    (a b aU bU : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ aU)
    (hb : b ≤ bU) (hbU0 : 0 ≤ bU) :
    a * b ≤ aU * bU := by
  have hfirst := mul_nonneg (sub_nonneg.mpr ha) hbU0
  have hsecond := mul_nonneg ha0 (sub_nonneg.mpr hb)
  nlinarith only [hfirst, hsecond]

set_option maxHeartbeats 3000000 in
theorem correlated_clean_unfix_D
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD F
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 ≤
      correlatedCoefficientThree
        cornerA cornerX cornerR cornerC D F
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := by
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at hDL hDU hFL hFU haL haU hxL hxU hrL hrU hcL hcU hdL hdU hfL hfU hsuL hsuU hduL hduU hu4L hu4U hsvL hsvU hdvL hdvU hv4L hv4U hq11L hq11U hq13L hq13U hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
  let g : ℝ → ℝ := fun z ↦ correlatedCoefficientThree
    cornerA cornerX cornerR cornerC z F
    a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33
  have hsec : quadraticSecant g D cornerD ≤ (0 : ℝ) := by
    let gdet : ℝ → ℝ := fun z ↦ correlatedDeterminantBlock
      cornerA cornerX cornerR cornerC z F a x r c d f
        q11 q13 q33 h11 h13 h33
    let gcoupling : ℝ → ℝ := fun z ↦ correlatedCouplingBlock
      cornerA cornerX cornerR cornerC z F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33
    let gcross : ℝ → ℝ := fun z ↦ correlatedCrossBlock
      (cornerA + a) (cornerX + x) (cornerR + r) (cornerC + c) (z + d)
        F f su du u4 sv dv v4
    have hdet : quadraticSecant gdet D cornerD ≤ (-638 / 100000 : ℝ) := by
      rcases oddASlope_bounds A X R C D F a x r c d f
          su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox with
        ⟨hOddMinus, hOddMixed, hOddPlus⟩
      let om : ℝ :=
        (q11 - h11) * (q33 - h33) - (q13 - h13) ^ 2
      let ox : ℝ :=
        (q11 + h11) * (q33 - h33) +
          (q11 - h11) * (q33 + h33) -
            2 * (q13 + h13) * (q13 - h13)
      let op : ℝ :=
        (q11 + h11) * (q33 + h33) - (q13 + h13) ^ 2
      have hom : (26 / 1000 : ℝ) ≤ om := by
        simpa only [om] using hOddMinus
      have hox : (41 / 1000 : ℝ) ≤ ox := by
        simpa only [ox] using hOddMixed
      have hop : (4 / 1000 : ℝ) ≤ op := by
        simpa only [op] using hOddPlus
      have hD0 : 0 ≤ D := by linarith only [hDL]
      have ha0 : 0 ≤ a := by linarith only [haL]
      have hd0 : 0 ≤ d := by linarith only [hdL]
      have hr0 : 0 ≤ r := by linarith only [hrL]
      have hx0 : 0 ≤ x := by linarith only [hxL]
      have hDaL := nonnegative_product_lower
        D a (42817 / 1000000) (824479 / 1000000)
        hDL haL (by norm_num) ha0
      have hDaU := nonnegative_product_upper
        D a (21449 / 500000) (165293 / 200000)
        hDU haU (by norm_num) ha0
      have hAdL := nonnegative_product_lower
        a d (824479 / 1000000) (23317 / 1000000)
        haL hdL (by norm_num) hd0
      have hAdU := nonnegative_product_upper
        a d (165293 / 200000) (27183 / 1000000)
        haU hdU (by norm_num) hd0
      have hRxL := nonnegative_product_lower
        r x (49817 / 1000000) (37851 / 1000000)
        hrL hxL (by norm_num) hx0
      have hRxU := nonnegative_product_upper
        r x (57183 / 1000000) (39761 / 1000000)
        hrU hxU (by norm_num) hx0
      let gm : ℝ :=
        D * a / 4 - 412269 / 400000 * D + a * d / 2 +
          21449 / 2000000 * a + 137423 / 200000 * d + r * x / 2 +
            3977 / 200000 * r + 121449 / 1000000 * x -
              11740773819 / 200000000000
      let gx : ℝ :=
        -D * a / 4 - 412269 / 400000 * D + a * d / 2 -
          21449 / 2000000 * a - 137423 / 200000 * d + r * x / 2 -
            3977 / 200000 * r - 121449 / 1000000 * x -
              11740773819 / 200000000000
      let gp : ℝ :=
        -(D * a / 4 + 137423 / 400000 * D + a * d / 2 +
          21449 / 2000000 * a + 137423 / 200000 * d + r * x / 2 +
            3977 / 200000 * r + 121449 / 1000000 * x +
              3913591273 / 200000000000)
      have hgm : gm ≤ (-48 / 1000 : ℝ) := by
        dsimp only [gm]
        nlinarith only [hDL, haU, hdU, hrU, hxU, hDaU, hAdU, hRxU]
      have hgx : gx ≤ (-129 / 1000 : ℝ) := by
        dsimp only [gx]
        nlinarith only [hDL, haL, hdL, hrL, hxL, hDaL, hAdU, hRxU]
      have hgp : gp ≤ (-84 / 1000 : ℝ) := by
        dsimp only [gp]
        nlinarith only [hDL, haL, hdL, hrL, hxL, hDaL, hAdL, hRxL]
      have hsecEq : quadraticSecant gdet D cornerD =
          gm * om + gx * ox + gp * op := by
        unfold gdet quadraticSecant correlatedDeterminantBlock
          alignedDeterminant alignedMixedDeterminant alignedEntry00 alignedEntry02
          alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
        dsimp only [gm, gx, gp, om, ox, op]
        simp only [cornerA, cornerX, cornerR, cornerC, cornerD]
        ring
      have hmProd := positive_negative_product_upper
        om gm (26 / 1000) (-48 / 1000) hom
        (by linarith only [hgm]) (by norm_num) hgm
      have hxProd := positive_negative_product_upper
        ox gx (41 / 1000) (-129 / 1000) hox
        (by linarith only [hgx]) (by norm_num) hgx
      have hpProd := positive_negative_product_upper
        op gp (4 / 1000) (-84 / 1000) hop
        (by linarith only [hgp]) (by norm_num) hgp
      rw [hsecEq]
      nlinarith only [hmProd, hxProd, hpProd]
    have hcoupling : quadraticSecant gcoupling D cornerD ≤
        (674 / 100000 : ℝ) := by
      let p11 : ℝ := q11 + h11
      let p13 : ℝ := q13 + h13
      let p33 : ℝ := q33 + h33
      let m11 : ℝ := q11 - h11
      let m13 : ℝ := q13 - h13
      let m33 : ℝ := q33 - h33
      have hp11L : (1918 / 10000 : ℝ) ≤ p11 := by
        dsimp only [p11]; linarith only [hq11L, hh11L]
      have hp11U : p11 ≤ (199 / 1000 : ℝ) := by
        dsimp only [p11]; linarith only [hq11U, hh11U]
      have hp13L : (189 / 1000 : ℝ) ≤ p13 := by
        dsimp only [p13]; linarith only [hq13L, hh13L]
      have hp13U : p13 ≤ (1912 / 10000 : ℝ) := by
        dsimp only [p13]; linarith only [hq13U, hh13U]
      have hp33L : (2115 / 10000 : ℝ) ≤ p33 := by
        dsimp only [p33]; linarith only [hq33L, hh33L]
      have hp33U : p33 ≤ (216 / 1000 : ℝ) := by
        dsimp only [p33]; linarith only [hq33U, hh33U]
      have hm11L : (1578 / 10000 : ℝ) ≤ m11 := by
        dsimp only [m11]; linarith only [hq11L, hh11U]
      have hm11U : m11 ≤ (165 / 1000 : ℝ) := by
        dsimp only [m11]; linarith only [hq11U, hh11L]
      have hm13L : (209 / 1000 : ℝ) ≤ m13 := by
        dsimp only [m13]; linarith only [hq13L, hh13U]
      have hm13U : m13 ≤ (2112 / 10000 : ℝ) := by
        dsimp only [m13]; linarith only [hq13U, hh13L]
      have hm33L : (4485 / 10000 : ℝ) ≤ m33 := by
        dsimp only [m33]; linarith only [hq33L, hh33U]
      have hm33U : m33 ≤ (453 / 1000 : ℝ) := by
        dsimp only [m33]; linarith only [hq33U, hh33L]
      have htL : (1 / 500 : ℝ) ≤ -v4 := by linarith only [hv4U]
      have htU : -v4 ≤ (1 / 250 : ℝ) := by linarith only [hv4L]
      have hSpBounds := alignedTopPair_bounds
        p11 p13 p33 su sv su sv
        (1918 / 10000) (199 / 1000) (189 / 1000) (1912 / 10000)
        (2115 / 10000) (216 / 1000)
        (7021 / 12500) (56173 / 100000)
        (10763 / 20000) (13459 / 25000)
        (7021 / 12500) (56173 / 100000)
        (10763 / 20000) (13459 / 25000)
        hp11L hp11U hp13L hp13U hp33L hp33U
        hsuL hsuU hsvL hsvU hsuL hsuU hsvL hsvU
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
      have hSDpBounds := alignedTopPair_bounds
        p11 p13 p33 su sv du dv
        (1918 / 10000) (199 / 1000) (189 / 1000) (1912 / 10000)
        (2115 / 10000) (216 / 1000)
        (7021 / 12500) (56173 / 100000)
        (10763 / 20000) (13459 / 25000)
        (1687 / 100000) (423 / 25000)
        (111 / 2000) (279 / 5000)
        hp11L hp11U hp13L hp13U hp33L hp33U
        hsuL hsuU hsvL hsvU hduL hduU hdvL hdvU
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
      have hSmBounds := alignedTopPair_bounds
        m11 m13 m33 su sv su sv
        (1578 / 10000) (165 / 1000) (209 / 1000) (2112 / 10000)
        (4485 / 10000) (453 / 1000)
        (7021 / 12500) (56173 / 100000)
        (10763 / 20000) (13459 / 25000)
        (7021 / 12500) (56173 / 100000)
        (10763 / 20000) (13459 / 25000)
        hm11L hm11U hm13L hm13U hm33L hm33U
        hsuL hsuU hsvL hsvU hsuL hsuU hsvL hsvU
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
      have hSDmBounds := alignedTopPair_bounds
        m11 m13 m33 su sv du dv
        (1578 / 10000) (165 / 1000) (209 / 1000) (2112 / 10000)
        (4485 / 10000) (453 / 1000)
        (7021 / 12500) (56173 / 100000)
        (10763 / 20000) (13459 / 25000)
        (1687 / 100000) (423 / 25000)
        (111 / 2000) (279 / 5000)
        hm11L hm11U hm13L hm13U hm33L hm33U
        hsuL hsuU hsvL hsvU hduL hduU hdvL hdvU
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
      have hS4pBounds := oddCouplingCross_negative_four_bounds
        su u4 sv v4 p11 p13 p33
        (7021 / 12500) (56173 / 100000) (141 / 1000) (18 / 125)
        (10763 / 20000) (13459 / 25000) (1 / 500) (1 / 250)
        (1918 / 10000) (199 / 1000) (189 / 1000) (1912 / 10000)
        (2115 / 10000) (216 / 1000)
        hsuL hsuU hu4L hu4U hsvL hsvU htL htU
        hp11L hp11U hp13L hp13U hp33L hp33U
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
      have hD4pBounds := oddCouplingCross_negative_four_bounds
        du u4 dv v4 p11 p13 p33
        (1687 / 100000) (423 / 25000) (141 / 1000) (18 / 125)
        (111 / 2000) (279 / 5000) (1 / 500) (1 / 250)
        (1918 / 10000) (199 / 1000) (189 / 1000) (1912 / 10000)
        (2115 / 10000) (216 / 1000)
        hduL hduU hu4L hu4U hdvL hdvU htL htU
        hp11L hp11U hp13L hp13U hp33L hp33U
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
      have hS4mBounds := oddCouplingCross_negative_four_bounds
        su u4 sv v4 m11 m13 m33
        (7021 / 12500) (56173 / 100000) (141 / 1000) (18 / 125)
        (10763 / 20000) (13459 / 25000) (1 / 500) (1 / 250)
        (1578 / 10000) (165 / 1000) (209 / 1000) (2112 / 10000)
        (4485 / 10000) (453 / 1000)
        hsuL hsuU hu4L hu4U hsvL hsvU htL htU
        hm11L hm11U hm13L hm13U hm33L hm33U
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
      have hD4mBounds := oddCouplingCross_negative_four_bounds
        du u4 dv v4 m11 m13 m33
        (1687 / 100000) (423 / 25000) (141 / 1000) (18 / 125)
        (111 / 2000) (279 / 5000) (1 / 500) (1 / 250)
        (1578 / 10000) (165 / 1000) (209 / 1000) (2112 / 10000)
        (4485 / 10000) (453 / 1000)
        hduL hduU hu4L hu4U hdvL hdvU htL htU
        hm11L hm11U hm13L hm13U hm33L hm33U
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
      let Sp := alignedTopPair p11 p13 p33 su sv su sv
      let SDp := alignedTopPair p11 p13 p33 su sv du dv
      let S4p := oddCouplingCross su u4 sv v4 p11 p13 p33
      let D4p := oddCouplingCross du u4 dv v4 p11 p13 p33
      let Sm := alignedTopPair m11 m13 m33 su sv su sv
      let SDm := alignedTopPair m11 m13 m33 su sv du dv
      let S4m := oddCouplingCross su u4 sv v4 m11 m13 m33
      let D4m := oddCouplingCross du u4 dv v4 m11 m13 m33
      have hSpU : Sp ≤ (116 / 10000 : ℝ) :=
        le_trans hSpBounds.2 (by norm_num [Sp])
      have hSDpU : SDp ≤ (43 / 100000 : ℝ) :=
        le_trans hSDpBounds.2 (by norm_num [SDp])
      have hS4pU : S4p ≤ (34 / 10000 : ℝ) :=
        le_trans hS4pBounds.2 (by norm_num [S4p])
      have hD4pL : (-108 / 100000 : ℝ) ≤ D4p :=
        le_trans (by norm_num [D4p]) hD4pBounds.1
      have hSmU : Sm ≤ (645 / 10000 : ℝ) :=
        le_trans hSmBounds.2 (by norm_num [Sm])
      have hSDmU : SDm ≤ (85 / 100000 : ℝ) :=
        le_trans hSDmBounds.2 (by norm_num [SDm])
      have hS4mU : S4m ≤ (212 / 10000 : ℝ) :=
        le_trans hS4mBounds.2 (by norm_num [S4m])
      have hD4mL : (-66 / 100000 : ℝ) ≤ D4m :=
        le_trans (by norm_num [D4m]) hD4mBounds.1
      have hcSp0 : 0 ≤ D + cornerD + 2 * d := by
        norm_num [cornerD] at ⊢; linarith only [hDL, hdL]
      have hcSDp0 : 0 ≤ 2 * (cornerR + r) := by
        norm_num [cornerR] at ⊢; linarith only [hrL]
      have hcS4p0 : 0 ≤ 2 * (cornerX + x) := by
        norm_num [cornerX] at ⊢; linarith only [hxL]
      have hcD4p0 : 0 ≤ 2 * (cornerA + a) := by
        norm_num [cornerA] at ⊢; linarith only [haL]
      have hcSm0 : 0 ≤ D + cornerD := by
        norm_num [cornerD] at ⊢; linarith only [hDL]
      have hSpProd := product_upper_of_nonnegative_left
        (D + cornerD + 2 * d) Sp (141 / 1000) (116 / 10000)
        hcSp0 (by norm_num [cornerD] at ⊢; linarith only [hDU, hdU])
        hSpU (by norm_num)
      have hSDpProd := product_upper_of_nonnegative_left
        (2 * (cornerR + r)) SDp (601 / 1000) (43 / 100000)
        hcSDp0 (by norm_num [cornerR] at ⊢; linarith only [hrU])
        hSDpU (by norm_num)
      have hS4pProd := product_upper_of_nonnegative_left
        (2 * (cornerX + x)) S4p (160 / 1000) (34 / 10000)
        hcS4p0 (by norm_num [cornerX] at ⊢; linarith only [hxU])
        hS4pU (by norm_num)
      have hD4pProd := product_upper_of_nonnegative_left
        (2 * (cornerA + a)) (-D4p) (4402 / 1000) (108 / 100000)
        hcD4p0 (by norm_num [cornerA] at ⊢; linarith only [haU])
        (by linarith only [hD4pL]) (by norm_num)
      have hSmProd := product_upper_of_nonnegative_left
        (D + cornerD) Sm (86 / 1000) (645 / 10000)
        hcSm0 (by norm_num [cornerD] at ⊢; linarith only [hDU])
        hSmU (by norm_num)
      have hSDmProd := product_upper_of_nonnegative_left
        (2 * cornerR) SDm (486 / 1000) (85 / 100000)
        (by norm_num [cornerR]) (by norm_num [cornerR]) hSDmU (by norm_num)
      have hS4mProd := product_upper_of_nonnegative_left
        (2 * cornerX) S4m (80 / 1000) (212 / 10000)
        (by norm_num [cornerX]) (by norm_num [cornerX]) hS4mU (by norm_num)
      have hD4mProd := product_upper_of_nonnegative_left
        (2 * cornerA) (-D4m) (2749 / 1000) (66 / 100000)
        (by norm_num [cornerA]) (by norm_num [cornerA])
        (by linarith only [hD4mL]) (by norm_num)
      have hsecEq : quadraticSecant gcoupling D cornerD =
          ((D + cornerD + 2 * d) * Sp + 2 * (cornerR + r) * SDp +
            2 * (cornerX + x) * S4p - 2 * (cornerA + a) * D4p) / 4 +
          ((D + cornerD) * Sm + 2 * cornerR * SDm +
            2 * cornerX * S4m - 2 * cornerA * D4m) / 2 := by
        unfold gcoupling quadraticSecant correlatedCouplingBlock
          alignedAdjugatePair alignedMixedAdjugatePair
        dsimp only [Sp, SDp, S4p, D4p, Sm, SDm, S4m, D4m,
          p11, p13, p33, m11, m13, m33]
        unfold alignedTopPair oddCouplingCross
        simp only [cornerA, cornerX, cornerR, cornerC, cornerD]
        ring
      rw [hsecEq]
      nlinarith only [hSpProd, hSDpProd, hS4pProd, hD4pProd,
        hSmProd, hSDmProd, hS4mProd, hD4mProd]
    have hcross : quadraticSecant gcross D cornerD ≤
        (-83 / 100000 : ℝ) := by
      obtain ⟨hP, hQ⟩ := correlated_cross_gap_bounds
        A X R C D F a x r c d f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33 hbox
      have hprod := nonnegative_product_lower
        (u4 * sv - v4 * su) (su * dv - du * sv)
        (77 / 1000) (22 / 1000) hP hQ
        (by norm_num) (by linarith only [hQ])
      unfold gcross quadraticSecant correlatedCrossBlock alignedCrossEnergy
      dsimp only
      simp only [cornerA, cornerX, cornerR, cornerC, cornerD]
      ring_nf
      nlinarith only [hprod]
    have hsplit : quadraticSecant g D cornerD =
        quadraticSecant gdet D cornerD +
          quadraticSecant gcoupling D cornerD +
            quadraticSecant gcross D cornerD := by
      unfold g gdet gcoupling gcross quadraticSecant
      simp only [correlatedCoefficientThree_eq_blocks]
      ring
    calc
      quadraticSecant g D cornerD =
          quadraticSecant gdet D cornerD +
            quadraticSecant gcoupling D cornerD +
              quadraticSecant gcross D cornerD := hsplit
      _ ≤ (-638 / 100000 : ℝ) + 674 / 100000 + (-83 / 100000 : ℝ) :=
        add_le_add (add_le_add hdet hcoupling) hcross
      _ ≤ 0 := by norm_num
  have hid : g D - g cornerD =
      (D - cornerD) * quadraticSecant g D cornerD := by
    unfold g quadraticSecant correlatedCoefficientThree alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  exact quadraticSecant_upper_endpoint g D cornerD
    (by simpa only [cornerD] using hbox.D_mem.2) hsec hid

set_option maxHeartbeats 3000000 in
theorem correlated_clean_unfix_C
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    correlatedCoefficientThree
        cornerA cornerX cornerR cornerC D F
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 ≤
      correlatedCoefficientThree
        cornerA cornerX cornerR C D F
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := by
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at hDL hDU hFL hFU haL haU hxL hxU hrL hrU hcL hcU hdL hdU hfL hfU hsuL hsuU hduL hduU hu4L hu4U hsvL hsvU hdvL hdvU hv4L hv4U hq11L hq11U hq13L hq13U hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
  let g : ℝ → ℝ := fun z ↦ correlatedCoefficientThree
    cornerA cornerX cornerR z D F
    a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33
  have hsec : (0 : ℝ) ≤ quadraticSecant g C cornerC := by
    let gdet : ℝ → ℝ := fun z ↦ correlatedDeterminantBlock
      cornerA cornerX cornerR z D F a x r c d f
        q11 q13 q33 h11 h13 h33
    let gcoupling : ℝ → ℝ := fun z ↦ correlatedCouplingBlock
      cornerA cornerX cornerR z D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33
    let gcross : ℝ → ℝ := fun z ↦ correlatedCrossBlock
      (cornerA + a) (cornerX + x) (cornerR + r) (z + c) (D + d)
        F f su du u4 sv dv v4
    have hdet : (1829 / 100000 : ℝ) ≤
        quadraticSecant gdet C cornerC := by
      rcases oddASlope_bounds A X R C D F a x r c d f
          su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox with
        ⟨hOddMinus, hOddMixed, hOddPlus⟩
      let om : ℝ :=
        (q11 - h11) * (q33 - h33) - (q13 - h13) ^ 2
      let ox : ℝ :=
        (q11 + h11) * (q33 - h33) +
          (q11 - h11) * (q33 + h33) -
            2 * (q13 + h13) * (q13 - h13)
      let op : ℝ :=
        (q11 + h11) * (q33 + h33) - (q13 + h13) ^ 2
      have hom : (26 / 1000 : ℝ) ≤ om := by
        simpa only [om] using hOddMinus
      have hox : (41 / 1000 : ℝ) ≤ ox := by
        simpa only [ox] using hOddMixed
      have hop : (4 / 1000 : ℝ) ≤ op := by
        simpa only [op] using hOddPlus
      have hF0 : 0 ≤ F := by linarith only [hFL]
      have ha0 : 0 ≤ a := by linarith only [haL]
      have hf0 : 0 ≤ f := by linarith only [hfL]
      have hr0 : 0 ≤ r := by linarith only [hrL]
      have hFaL := nonnegative_product_lower
        F a (1571 / 5000) (824479 / 1000000)
        hFL haL (by norm_num) ha0
      have hFaU := nonnegative_product_upper
        F a (63 / 200) (165293 / 200000)
        hFU haU (by norm_num) ha0
      have hAfL := nonnegative_product_lower
        a f (824479 / 1000000) (4411 / 25000)
        haL hfL (by norm_num) hf0
      have hAfU := nonnegative_product_upper
        a f (165293 / 200000) (552 / 3125)
        haU hfU (by norm_num) hf0
      have hRrL := nonnegative_product_lower
        r r (49817 / 1000000) (49817 / 1000000)
        hrL hrL (by norm_num) hr0
      have hRrU := nonnegative_product_upper
        r r (57183 / 1000000) (57183 / 1000000)
        hrU hrU (by norm_num) hr0
      let gm : ℝ :=
        -F * a / 4 + 412269 / 400000 * F - a * f / 4 -
          137423 / 400000 * f + r ^ 2 / 4 +
            121449 / 1000000 * r - 44249578803 / 1000000000000
      let gx : ℝ :=
        F * a / 4 + 412269 / 400000 * F - a * f / 4 +
          137423 / 400000 * f + r ^ 2 / 4 -
            121449 / 1000000 * r - 44249578803 / 1000000000000
      let gp : ℝ :=
        F * a / 4 + 137423 / 400000 * F + a * f / 4 +
          137423 / 400000 * f - r ^ 2 / 4 -
            121449 / 1000000 * r - 14749859601 / 1000000000000
      have hgm : (123 / 1000 : ℝ) ≤ gm := by
        dsimp only [gm]
        nlinarith only [hFL, hfU, hrL, hFaU, hAfU, hRrL]
      have hgx : (362 / 1000 : ℝ) ≤ gx := by
        dsimp only [gx]
        nlinarith only [hFL, hfL, hrU, hFaL, hAfU, hRrL]
      have hgp : (247 / 1000 : ℝ) ≤ gp := by
        dsimp only [gp]
        nlinarith only [hFL, hfL, hrU, hFaL, hAfL, hRrU]
      have hsecEq : quadraticSecant gdet C cornerC =
          gm * om + gx * ox + gp * op := by
        unfold gdet quadraticSecant correlatedDeterminantBlock
          alignedDeterminant alignedMixedDeterminant alignedEntry00 alignedEntry02
          alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
        dsimp only [gm, gx, gp, om, ox, op]
        simp only [cornerA, cornerX, cornerR, cornerC]
        ring
      have hmProd := nonnegative_product_lower
        gm om (123 / 1000) (26 / 1000) hgm hom
        (by norm_num) (by linarith only [hom])
      have hxProd := nonnegative_product_lower
        gx ox (362 / 1000) (41 / 1000) hgx hox
        (by norm_num) (by linarith only [hox])
      have hpProd := nonnegative_product_lower
        gp op (247 / 1000) (4 / 1000) hgp hop
        (by norm_num) (by linarith only [hop])
      rw [hsecEq]
      nlinarith only [hmProd, hxProd, hpProd]
    have hcoupling : (-1574 / 100000 : ℝ) ≤
        quadraticSecant gcoupling C cornerC := by
      let Sq := alignedTopPair q11 q13 q33 su sv su sv
      let Sh := alignedTopPair h11 h13 h33 su sv su sv
      let S4q := oddCouplingCross su u4 sv v4 q11 q13 q33
      let S4h := oddCouplingCross su u4 sv v4 h11 h13 h33
      let Q4q := oddCouplingFour u4 v4 q11 q13 q33
      let Q4h := oddCouplingFour u4 v4 h11 h13 h33
      have hsu0 : 0 ≤ su := by linarith only [hsuL]
      have hsv0 : 0 ≤ sv := by linarith only [hsvL]
      have hu40 : 0 ≤ u4 := by linarith only [hu4L]
      have htL : (1 / 500 : ℝ) ≤ -v4 := by linarith only [hv4U]
      have htU : -v4 ≤ (1 / 250 : ℝ) := by linarith only [hv4L]
      have ht0 : 0 ≤ -v4 := by linarith only [htL]
      have hq110 : 0 ≤ q11 := by linarith only [hq11L]
      have hq130 : 0 ≤ q13 := by linarith only [hq13L]
      have hq330 : 0 ≤ q33 := by linarith only [hq33L]
      have hh110 : 0 ≤ h11 := by linarith only [hh11L]
      have hk13L : (9 / 1000 : ℝ) ≤ -h13 := by
        linarith only [hh13U]
      have hk13U : -h13 ≤ (11 / 1000 : ℝ) := by
        linarith only [hh13L]
      have hk130 : 0 ≤ -h13 := by linarith only [hk13L]
      have hk33L : (117 / 1000 : ℝ) ≤ -h33 := by
        linarith only [hh33U]
      have hk33U : -h33 ≤ (120 / 1000 : ℝ) := by
        linarith only [hh33L]
      have hk330 : 0 ≤ -h33 := by linarith only [hk33L]
      have hSqBounds := alignedTopPair_bounds
        q11 q13 q33 su sv su sv
        (889 / 5000) (179 / 1000) (1 / 5) (1001 / 5000)
        (663 / 2000) (333 / 1000)
        (7021 / 12500) (56173 / 100000)
        (10763 / 20000) (13459 / 25000)
        (7021 / 12500) (56173 / 100000)
        (10763 / 20000) (13459 / 25000)
        hq11L hq11U hq13L hq13U hq33L hq33U
        hsuL hsuU hsvL hsvU hsuL hsuU hsvL hsvU
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
      have hSqU : Sq ≤ (360476172741 / 10000000000000 : ℝ) :=
        le_trans hSqBounds.2 (by norm_num [Sq])
      have hSq0 : 0 ≤ Sq :=
        le_trans (by norm_num [Sq]) hSqBounds.1
      have hk33suU := nonnegative_triple_upper
        (-h33) su su (120 / 1000) (56173 / 100000) (56173 / 100000)
        hk33U hsuU hsuU (by norm_num) (by norm_num) hsu0 hsu0
      have hk13susvL := nonnegative_triple_lower
        (-h13) su sv (9 / 1000) (7021 / 12500) (10763 / 20000)
        hk13L hsuL hsvL (by norm_num) (by norm_num) hsu0 hsv0
      have hh11svL := nonnegative_triple_lower
        h11 sv sv (7 / 500) (10763 / 20000) (10763 / 20000)
        hh11L hsvL hsvL (by norm_num) (by norm_num) hsv0 hsv0
      have hShL : (-28369569577 / 1000000000000 : ℝ) ≤ Sh := by
        dsimp only [Sh]
        unfold alignedTopPair
        nlinarith only [hk33suU, hk13susvL, hh11svL]
      have hS4qBounds := oddCouplingCross_negative_four_bounds
        su u4 sv v4 q11 q13 q33
        (7021 / 12500) (56173 / 100000) (141 / 1000) (18 / 125)
        (10763 / 20000) (13459 / 25000) (1 / 500) (1 / 250)
        (889 / 5000) (179 / 1000) (1 / 5) (1001 / 5000)
        (663 / 2000) (333 / 1000)
        hsuL hsuU hu4L hu4U hsvL hsvU htL htU
        hq11L hq11U hq13L hq13U hq33L hq33U
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
      have hS4qL : (1321587399 / 125000000000 : ℝ) ≤ S4q :=
        le_trans (by norm_num [S4q]) hS4qBounds.1
      have hS4q0 : 0 ≤ S4q := le_trans (by norm_num) hS4qL
      have hk33su4L := nonnegative_triple_lower
        (-h33) su u4 (117 / 1000) (7021 / 12500) (141 / 1000)
        hk33L hsuL hu4L (by norm_num) (by norm_num) hsu0 hu40
      have hk13sutL := nonnegative_triple_lower
        (-h13) su (-v4) (9 / 1000) (7021 / 12500) (1 / 500)
        hk13L hsuL htL (by norm_num) (by norm_num) hsu0 ht0
      have hk13u4svU := nonnegative_triple_upper
        (-h13) u4 sv (11 / 1000) (18 / 125) (13459 / 25000)
        hk13U hu4U hsvU (by norm_num) (by norm_num) hu40 hsv0
      have hh11svtL := nonnegative_triple_lower
        h11 sv (-v4) (7 / 500) (10763 / 20000) (1 / 500)
        hh11L hsvL htL (by norm_num) (by norm_num) hsv0 ht0
      have hnegS4hL : (210961279 / 25000000000 : ℝ) ≤ -S4h := by
        dsimp only [S4h]
        unfold oddCouplingCross
        nlinarith only [hk33su4L, hk13sutL, hk13u4svU, hh11svtL]
      have hnegS4h0 : 0 ≤ -S4h := le_trans (by norm_num) hnegS4hL
      have hQ4qRaw := oddCouplingFour_negative_upper
        u4 v4 q11 q13 q33 (18 / 125) (1 / 250)
        (179 / 1000) (1001 / 5000) (333 / 1000)
        hu4U htU hq11U hq13U hq33U hu40 ht0 hq110 hq130 hq330
      have hQ4qU : Q4q ≤ (2230807 / 312500000 : ℝ) :=
        le_trans hQ4qRaw (by norm_num [Q4q])
      have hq33u4u4 : 0 ≤ q33 * u4 * u4 :=
        mul_nonneg (mul_nonneg hq330 hu40) hu40
      have hq13u4t : 0 ≤ q13 * u4 * (-v4) :=
        mul_nonneg (mul_nonneg hq130 hu40) ht0
      have hq11tt : 0 ≤ q11 * (-v4) * (-v4) :=
        mul_nonneg (mul_nonneg hq110 ht0) ht0
      have hQ4q0 : 0 ≤ Q4q := by
        dsimp only [Q4q]
        unfold oddCouplingFour
        nlinarith only [hq33u4u4, hq13u4t, hq11tt]
      have hk33u4U := nonnegative_triple_upper
        (-h33) u4 u4 (120 / 1000) (18 / 125) (18 / 125)
        hk33U hu4U hu4U (by norm_num) (by norm_num) hu40 hu40
      have hk13u4tU := nonnegative_triple_upper
        (-h13) u4 (-v4) (11 / 1000) (18 / 125) (1 / 250)
        hk13U hu4U htU (by norm_num) (by norm_num) hu40 ht0
      have hh11ttL := nonnegative_triple_lower
        h11 (-v4) (-v4) (7 / 500) (1 / 500) (1 / 500)
        hh11L htL htL (by norm_num) (by norm_num) ht0 ht0
      have hQ4hL : (-312617 / 125000000 : ℝ) ≤ Q4h := by
        dsimp only [Q4h]
        unfold oddCouplingFour
        nlinarith only [hk33u4U, hk13u4tU, hh11ttL]
      have hcSq0 : 0 ≤ (3 * F + f) / 4 := by
        nlinarith only [hFL, hfL]
      have hcSqU : (3 * F + f) / 4 ≤ (28041 / 100000 : ℝ) := by
        nlinarith only [hFU, hfU]
      have hcSh0 : 0 ≤ (F - f) / 4 := by
        nlinarith only [hFL, hfU]
      have hcShU : (F - f) / 4 ≤ (3464 / 100000 : ℝ) := by
        nlinarith only [hFU, hfL]
      have hcS4qL : (389134 / 1000000 : ℝ) ≤
          (3 * cornerR + r) / 2 := by
        norm_num [cornerR] at ⊢
        linarith only [hrL]
      have hcS4q0 : 0 ≤ (3 * cornerR + r) / 2 := by
        norm_num [cornerR] at ⊢
        linarith only [hrL]
      have hcS4hL : (92817 / 1000000 : ℝ) ≤
          (cornerR - r) / 2 := by
        norm_num [cornerR] at ⊢
        linarith only [hrU]
      have hcS4h0 : 0 ≤ (cornerR - r) / 2 := by
        norm_num [cornerR] at ⊢
        linarith only [hrU]
      have hcQ4q0 : 0 ≤ (3 * cornerA + a) / 4 := by
        norm_num [cornerA] at ⊢
        linarith only [haL]
      have hcQ4qU : (3 * cornerA + a) / 4 ≤
          (123728875 / 100000000 : ℝ) := by
        norm_num [cornerA] at ⊢
        linarith only [haU]
      have hcQ4h0 : 0 ≤ (cornerA - a) / 4 := by
        norm_num [cornerA] at ⊢
        linarith only [haU]
      have hcQ4hU : (cornerA - a) / 4 ≤
          (13743775 / 100000000 : ℝ) := by
        norm_num [cornerA] at ⊢
        linarith only [haL]
      have hSqProd := nonnegative_product_upper
        ((3 * F + f) / 4) Sq (28041 / 100000)
        (360476172741 / 10000000000000) hcSqU hSqU (by norm_num) hSq0
      have hShProd := positive_negative_product_lower
        ((F - f) / 4) Sh (3464 / 100000)
        (-28369569577 / 1000000000000) hcSh0 hShL (by norm_num) hcShU
      have hS4qProd := nonnegative_product_lower
        ((3 * cornerR + r) / 2) S4q (389134 / 1000000)
        (1321587399 / 125000000000) hcS4qL hS4qL (by norm_num) hS4q0
      have hS4hProd := nonnegative_product_lower
        ((cornerR - r) / 2) (-S4h) (92817 / 1000000)
        (210961279 / 25000000000) hcS4hL hnegS4hL
        (by norm_num) hnegS4h0
      have hQ4qProd := nonnegative_product_upper
        ((3 * cornerA + a) / 4) Q4q (123728875 / 100000000)
        (2230807 / 312500000) hcQ4qU hQ4qU (by norm_num) hQ4q0
      have hQ4hProd := positive_negative_product_lower
        ((cornerA - a) / 4) Q4h (13743775 / 100000000)
        (-312617 / 125000000) hcQ4h0 hQ4hL (by norm_num) hcQ4hU
      have hsecEq : quadraticSecant gcoupling C cornerC =
          -((3 * F + f) / 4) * Sq + ((F - f) / 4) * Sh +
            ((3 * cornerR + r) / 2) * S4q +
              ((cornerR - r) / 2) * (-S4h) -
                ((3 * cornerA + a) / 4) * Q4q +
                  ((cornerA - a) / 4) * Q4h := by
        unfold gcoupling quadraticSecant correlatedCouplingBlock
          alignedAdjugatePair alignedMixedAdjugatePair
        dsimp only [Sq, Sh, S4q, S4h, Q4q, Q4h]
        unfold alignedTopPair oddCouplingCross oddCouplingFour
        simp only [cornerA, cornerX, cornerR, cornerC]
        ring
      rw [hsecEq]
      nlinarith only [hSqProd, hShProd, hS4qProd, hS4hProd,
        hQ4qProd, hQ4hProd]
    have hcross : (148 / 100000 : ℝ) ≤
        quadraticSecant gcross C cornerC := by
      have hP := (correlated_cross_gap_bounds
        A X R C D F a x r c d f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33 hbox).1
      have hfac := mul_nonneg
        (by linarith only [hP] :
          0 ≤ (u4 * sv - v4 * su) - 77 / 1000)
        (by linarith only [hP] :
          0 ≤ (u4 * sv - v4 * su) + 77 / 1000)
      have hsq : (77 / 1000 : ℝ) ^ 2 ≤
          (u4 * sv - v4 * su) ^ 2 := by
        nlinarith only [hfac]
      unfold gcross quadraticSecant correlatedCrossBlock alignedCrossEnergy
      dsimp only
      simp only [cornerA, cornerX, cornerR, cornerC]
      ring_nf
      nlinarith only [hsq]
    have hsplit : quadraticSecant g C cornerC =
        quadraticSecant gdet C cornerC +
          quadraticSecant gcoupling C cornerC +
            quadraticSecant gcross C cornerC := by
      unfold g gdet gcoupling gcross quadraticSecant
      simp only [correlatedCoefficientThree_eq_blocks]
      ring
    nlinarith only [hsplit, hdet, hcoupling, hcross]
  have hid : g C - g cornerC =
      (C - cornerC) * quadraticSecant g C cornerC := by
    unfold g quadraticSecant correlatedCoefficientThree alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  exact quadraticSecant_lower_endpoint g C cornerC
    (by simpa only [cornerC] using hbox.C_mem.1) hsec hid

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3Structural
