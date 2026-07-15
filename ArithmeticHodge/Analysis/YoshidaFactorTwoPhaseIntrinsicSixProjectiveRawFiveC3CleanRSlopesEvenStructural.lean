import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3CleanRCoreStructural

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

private theorem cleanROddCorner_bounds
    (q33 h11 h13 h33 : ℝ)
    (hq33L : (3315 / 10000 : ℝ) ≤ q33)
    (hh11L : (14 / 1000 : ℝ) ≤ h11)
    (hh11U : h11 ≤ (20 / 1000 : ℝ))
    (hh13L : (-11 / 1000 : ℝ) ≤ h13)
    (hh13U : h13 ≤ (-9 / 1000 : ℝ))
    (hh33L : (-120 / 1000 : ℝ) ≤ h33)
    (hh33U : h33 ≤ (-117 / 1000 : ℝ)) :
    (4 / 1000 : ℝ) ≤
        (cornerQ11 + h11) * (q33 + h33) - (cornerQ13 + h13) ^ 2 ∧
      (26 / 1000 : ℝ) ≤
        (cornerQ11 - h11) * (q33 - h33) - (cornerQ13 - h13) ^ 2 ∧
      (41 / 1000 : ℝ) ≤
        (cornerQ11 + h11) * (q33 - h33) +
          (cornerQ11 - h11) * (q33 + h33) -
            2 * (cornerQ13 + h13) * (cornerQ13 - h13) := by
  have hp11L : (1918 / 10000 : ℝ) ≤ cornerQ11 + h11 := by
    norm_num [cornerQ11] at ⊢
    linarith only [hh11L]
  have hp13U : cornerQ13 + h13 ≤ (1912 / 10000 : ℝ) := by
    norm_num [cornerQ13] at ⊢
    linarith only [hh13U]
  have hp13Nonneg : 0 ≤ cornerQ13 + h13 := by
    norm_num [cornerQ13] at ⊢
    linarith only [hh13L]
  have hp33L : (2115 / 10000 : ℝ) ≤ q33 + h33 := by
    linarith only [hq33L, hh33L]
  have hpProd := nonnegative_product_lower
    (cornerQ11 + h11) (q33 + h33)
    (1918 / 10000) (2115 / 10000) hp11L hp33L
    (by norm_num) (by linarith only [hp33L])
  have hpSq : (cornerQ13 + h13) ^ 2 ≤ (1912 / 10000 : ℝ) ^ 2 := by
    have hfac := mul_nonneg (sub_nonneg.mpr hp13U)
      (by
        norm_num [cornerQ13] at hp13Nonneg ⊢
        linarith only [hp13Nonneg] :
        0 ≤ cornerQ13 + h13 + 1912 / 10000)
    nlinarith only [hfac]
  have hPlus : (4 / 1000 : ℝ) ≤
      (cornerQ11 + h11) * (q33 + h33) -
        (cornerQ13 + h13) ^ 2 := by
    nlinarith only [hpProd, hpSq]
  have hm11L : (1578 / 10000 : ℝ) ≤ cornerQ11 - h11 := by
    norm_num [cornerQ11] at ⊢
    linarith only [hh11U]
  have hm13U : cornerQ13 - h13 ≤ (2112 / 10000 : ℝ) := by
    norm_num [cornerQ13] at ⊢
    linarith only [hh13L]
  have hm13Nonneg : 0 ≤ cornerQ13 - h13 := by
    norm_num [cornerQ13] at ⊢
    linarith only [hh13U]
  have hm33L : (4485 / 10000 : ℝ) ≤ q33 - h33 := by
    linarith only [hq33L, hh33U]
  have hmProd := nonnegative_product_lower
    (cornerQ11 - h11) (q33 - h33)
    (1578 / 10000) (4485 / 10000) hm11L hm33L
    (by norm_num) (by linarith only [hm33L])
  have hmSq : (cornerQ13 - h13) ^ 2 ≤ (2112 / 10000 : ℝ) ^ 2 := by
    have hfac := mul_nonneg (sub_nonneg.mpr hm13U)
      (by
        norm_num [cornerQ13] at hm13Nonneg ⊢
        linarith only [hm13Nonneg] :
        0 ≤ cornerQ13 - h13 + 2112 / 10000)
    nlinarith only [hfac]
  have hMinus : (26 / 1000 : ℝ) ≤
      (cornerQ11 - h11) * (q33 - h33) -
        (cornerQ13 - h13) ^ 2 := by
    nlinarith only [hmProd, hmSq]
  have hhProd := nonnegative_product_lower
    h11 (-h33) (14 / 1000) (117 / 1000)
    hh11L (by linarith only [hh33U]) (by norm_num)
    (by linarith only [hh33U])
  have hhSq : (9 / 1000 : ℝ) ^ 2 ≤ h13 ^ 2 := by
    have hfac := mul_nonneg
      (by linarith only [hh13U] : 0 ≤ -h13 - 9 / 1000)
      (by linarith only [hh13U] : 0 ≤ -h13 + 9 / 1000)
    nlinarith only [hfac]
  have hMixed : (41 / 1000 : ℝ) ≤
      (cornerQ11 + h11) * (q33 - h33) +
        (cornerQ11 - h11) * (q33 + h33) -
          2 * (cornerQ13 + h13) * (cornerQ13 - h13) := by
    norm_num [cornerQ11, cornerQ13] at ⊢
    ring_nf
    nlinarith only [hq33L, hhProd, hhSq]
  exact ⟨hPlus, hMinus, hMixed⟩

set_option maxHeartbeats 5000000 in
theorem cleanRSlopeD_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    cleanRSlopeD
    R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 ≤ (-3 / 1000 : ℝ) := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
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
  norm_num at hRL hRU hCL hCU hDL hDU hFL hFU haL haU hxL hxU hrL hrU hcL hcU hdL hdU hfL hfU hsuL hsuU hduL hduU hu4L hu4U hsvL hsvU hdvL hdvU hv4L hv4U hq11L hq11U hq13L hq13U hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
  rcases cleanROddCorner_bounds q33 h11 h13 h33
      (by norm_num at ⊢; linarith only [hq33L])
      (by norm_num at ⊢; linarith only [hh11L])
      (by norm_num at ⊢; linarith only [hh11U])
      (by norm_num at ⊢; linarith only [hh13L])
      (by norm_num at ⊢; linarith only [hh13U])
      (by norm_num at ⊢; linarith only [hh33L])
      (by norm_num at ⊢; linarith only [hh33U]) with
    ⟨hOp, hOm, hOx⟩
  let op : ℝ :=
    (cornerQ11 + h11) * (q33 + h33) - (cornerQ13 + h13) ^ 2
  let om : ℝ :=
    (cornerQ11 - h11) * (q33 - h33) - (cornerQ13 - h13) ^ 2
  let ox : ℝ :=
    (cornerQ11 + h11) * (q33 - h33) +
      (cornerQ11 - h11) * (q33 + h33) -
        2 * (cornerQ13 + h13) * (cornerQ13 - h13)
  have hop : (4 / 1000 : ℝ) ≤ op := by simpa only [op] using hOp
  have hom : (26 / 1000 : ℝ) ≤ om := by simpa only [om] using hOm
  have hox : (41 / 1000 : ℝ) ≤ ox := by simpa only [ox] using hOx
  have hcp : (77 / 1000 : ℝ) ≤ x + cornerX := by
    norm_num [cornerX] at ⊢
    linarith only [hxL]
  have hcm : (79 / 1000 : ℝ) ≤ 3 * cornerX - x := by
    norm_num [cornerX] at ⊢
    linarith only [hxU]
  have hcx : (157 / 1000 : ℝ) ≤ x + 3 * cornerX := by
    norm_num [cornerX] at ⊢
    linarith only [hxL]
  have hpTerm := nonnegative_product_lower
    (x + cornerX) op (77 / 1000) (4 / 1000)
    hcp hop (by norm_num) (by linarith only [hop])
  have hmTerm := nonnegative_product_lower
    (3 * cornerX - x) om (79 / 1000) (26 / 1000)
    hcm hom (by norm_num) (by linarith only [hom])
  have hxTerm := nonnegative_product_lower
    (x + 3 * cornerX) ox (157 / 1000) (41 / 1000)
    hcx hox (by norm_num) (by linarith only [hox])
  have hdet :
      -((x + cornerX) * op + (3 * cornerX - x) * om +
          (x + 3 * cornerX) * ox) / 2 ≤ (-439 / 100000 : ℝ) := by
    nlinarith only [hpTerm, hmTerm, hxTerm]
  have ho33U : 3 * q33 - h33 ≤ (1119 / 1000 : ℝ) := by
    linarith only [hq33U, hh33L]
  have ho13L : (6096 / 10000 : ℝ) ≤
      3 * cornerQ13 - h13 := by
    norm_num [cornerQ13] at ⊢
    linarith only [hh13U]
  have ho11U : 3 * cornerQ11 - h11 ≤ (5194 / 10000 : ℝ) := by
    norm_num [cornerQ11] at ⊢
    linarith only [hh11L]
  have hdu0 : 0 ≤ du := by linarith only [hduL]
  have hdv0 : 0 ≤ dv := by linarith only [hdvL]
  have hsu0 : 0 ≤ su := by linarith only [hsuL]
  have hsv0 : 0 ≤ sv := by linarith only [hsvL]
  have hPos := nonnegative_triple_upper
    (3 * q33 - h33) du su
    (1119 / 1000) (423 / 25000) (56173 / 100000)
    ho33U hduU hsuU (by norm_num) (by norm_num) hdu0 hsu0
  have hNegOne := nonnegative_triple_lower
    (3 * cornerQ13 - h13) du sv
    (6096 / 10000) (1687 / 100000) (10763 / 20000)
    ho13L hduL hsvL (by norm_num) (by norm_num) hdu0 hsv0
  have hNegTwo := nonnegative_triple_lower
    (3 * cornerQ13 - h13) dv su
    (6096 / 10000) (111 / 2000) (7021 / 12500)
    ho13L hdvL hsuL (by norm_num) (by norm_num) hdv0 hsu0
  have hLast := nonnegative_triple_upper
    (3 * cornerQ11 - h11) dv sv
    (5194 / 10000) (279 / 5000) (13459 / 25000)
    ho11U hdvU hsvU (by norm_num) (by norm_num) hdv0 hsv0
  have hcoupling :
      ((3 * q33 - h33) * du * su -
          (3 * cornerQ13 - h13) * (du * sv + dv * su) +
            (3 * cornerQ11 - h11) * dv * sv) / 2 ≤
        (86 / 100000 : ℝ) := by
    nlinarith only [hPos, hNegOne, hNegTwo, hLast]
  have hsplit :
      cleanRSlopeD R C D F a x r c d f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33 =
        -((x + cornerX) * op + (3 * cornerX - x) * om +
            (x + 3 * cornerX) * ox) / 2 +
          ((3 * q33 - h33) * du * su -
            (3 * cornerQ13 - h13) * (du * sv + dv * su) +
              (3 * cornerQ11 - h11) * dv * sv) / 2 := by
    unfold cleanRSlopeD cleanRSecant quadraticSecant
      correlatedCoefficientThree alignedDeterminant alignedMixedDeterminant
      alignedAdjugatePair alignedMixedAdjugatePair alignedCrossEnergy
      alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
      alignedEntry24 mixedDeterminantOne
    dsimp only [op, om, ox]
    simp only [cornerA, cornerX, cornerR, cornerC, cornerD, cornerU4,
      cornerDv, cornerQ11, cornerQ13, cornerQ33, cornerH11, cornerH13]
    ring
  rw [hsplit]
  nlinarith only [hdet, hcoupling]

set_option maxHeartbeats 5000000 in
theorem cleanRSlopeC_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    cleanRSlopeC
    R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 ≤ (-3 / 1000 : ℝ) := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
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
  norm_num at hRL hRU hCL hCU hDL hDU hFL hFU haL haU hxL hxU hrL hrU hcL hcU hdL hdU hfL hfU hsuL hsuU hduL hduU hu4L hu4U hsvL hsvU hdvL hdvU hv4L hv4U hq11L hq11U hq13L hq13U hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
  rcases cleanROddCorner_bounds q33 h11 h13 h33
      (by norm_num at ⊢; linarith only [hq33L])
      (by norm_num at ⊢; linarith only [hh11L])
      (by norm_num at ⊢; linarith only [hh11U])
      (by norm_num at ⊢; linarith only [hh13L])
      (by norm_num at ⊢; linarith only [hh13U])
      (by norm_num at ⊢; linarith only [hh33L])
      (by norm_num at ⊢; linarith only [hh33U]) with
    ⟨hOp, hOm, hOx⟩
  let op : ℝ :=
    (cornerQ11 + h11) * (q33 + h33) - (cornerQ13 + h13) ^ 2
  let om : ℝ :=
    (cornerQ11 - h11) * (q33 - h33) - (cornerQ13 - h13) ^ 2
  let ox : ℝ :=
    (cornerQ11 + h11) * (q33 - h33) +
      (cornerQ11 - h11) * (q33 + h33) -
        2 * (cornerQ13 + h13) * (cornerQ13 - h13)
  have hop : (4 / 1000 : ℝ) ≤ op := by simpa only [op] using hOp
  have hom : (26 / 1000 : ℝ) ≤ om := by simpa only [om] using hOm
  have hox : (41 / 1000 : ℝ) ≤ ox := by simpa only [ox] using hOx
  have hcp : (585 / 1000 : ℝ) ≤ R + cornerR + 2 * r := by
    norm_num [cornerR] at ⊢
    linarith only [hRL, hrL]
  have hcm : (1342 / 1000 : ℝ) ≤
      3 * (R + cornerR) - 2 * r := by
    norm_num [cornerR] at ⊢
    linarith only [hRL, hrU]
  have hcx : (1556 / 1000 : ℝ) ≤
      3 * (R + cornerR) + 2 * r := by
    norm_num [cornerR] at ⊢
    linarith only [hRL, hrL]
  have hpTerm := nonnegative_product_lower
    (R + cornerR + 2 * r) op (585 / 1000) (4 / 1000)
    hcp hop (by norm_num) (by linarith only [hop])
  have hmTerm := nonnegative_product_lower
    (3 * (R + cornerR) - 2 * r) om
    (1342 / 1000) (26 / 1000) hcm hom
    (by norm_num) (by linarith only [hom])
  have hxTerm := nonnegative_product_lower
    (3 * (R + cornerR) + 2 * r) ox
    (1556 / 1000) (41 / 1000) hcx hox
    (by norm_num) (by linarith only [hox])
  have hdet :
      -((R + cornerR + 2 * r) * op +
          (3 * (R + cornerR) - 2 * r) * om +
            (3 * (R + cornerR) + 2 * r) * ox) / 4 ≤
        (-25257 / 1000000 : ℝ) := by
    nlinarith only [hpTerm, hmTerm, hxTerm]
  have ho33L : (11115 / 10000 : ℝ) ≤ 3 * q33 - h33 := by
    linarith only [hq33L, hh33U]
  have ho33U : 3 * q33 - h33 ≤ (1119 / 1000 : ℝ) := by
    linarith only [hq33U, hh33L]
  have ho13L : (6096 / 10000 : ℝ) ≤
      3 * cornerQ13 - h13 := by
    norm_num [cornerQ13] at ⊢
    linarith only [hh13U]
  have ho13U : 3 * cornerQ13 - h13 ≤ (6116 / 10000 : ℝ) := by
    norm_num [cornerQ13] at ⊢
    linarith only [hh13L]
  have ho11L : (5134 / 10000 : ℝ) ≤
      3 * cornerQ11 - h11 := by
    norm_num [cornerQ11] at ⊢
    linarith only [hh11U]
  have ho11U : 3 * cornerQ11 - h11 ≤ (5194 / 10000 : ℝ) := by
    norm_num [cornerQ11] at ⊢
    linarith only [hh11L]
  have hsu0 : 0 ≤ su := by linarith only [hsuL]
  have hsv0 : 0 ≤ sv := by linarith only [hsvL]
  have hu40 : 0 ≤ u4 := by linarith only [hu4L]
  have ht0 : 0 ≤ -v4 := by linarith only [hv4U]
  have h33suL := nonnegative_product_lower
    (3 * q33 - h33) su (11115 / 10000) (7021 / 12500)
    ho33L hsuL (by norm_num) hsu0
  have h33suU := nonnegative_product_upper
    (3 * q33 - h33) su (1119 / 1000) (56173 / 100000)
    ho33U hsuU (by norm_num) hsu0
  have h13svL := nonnegative_product_lower
    (3 * cornerQ13 - h13) sv (6096 / 10000) (10763 / 20000)
    ho13L hsvL (by norm_num) hsv0
  have h13svU := nonnegative_product_upper
    (3 * cornerQ13 - h13) sv (6116 / 10000) (13459 / 25000)
    ho13U hsvU (by norm_num) hsv0
  have h13suL := nonnegative_product_lower
    (3 * cornerQ13 - h13) su (6096 / 10000) (7021 / 12500)
    ho13L hsuL (by norm_num) hsu0
  have h13suU := nonnegative_product_upper
    (3 * cornerQ13 - h13) su (6116 / 10000) (56173 / 100000)
    ho13U hsuU (by norm_num) hsu0
  have h11svL := nonnegative_product_lower
    (3 * cornerQ11 - h11) sv (5134 / 10000) (10763 / 20000)
    ho11L hsvL (by norm_num) hsv0
  have h11svU := nonnegative_product_upper
    (3 * cornerQ11 - h11) sv (5194 / 10000) (13459 / 25000)
    ho11U hsvU (by norm_num) hsv0
  let b1 : ℝ := (3 * q33 - h33) * su -
    (3 * cornerQ13 - h13) * sv
  let b2 : ℝ := (3 * cornerQ13 - h13) * su -
    (3 * cornerQ11 - h11) * sv
  have hb1L : (295 / 1000 : ℝ) ≤ b1 := by
    dsimp only [b1]
    nlinarith only [h33suL, h13svU]
  have hb1U : b1 ≤ (3006 / 10000 : ℝ) := by
    dsimp only [b1]
    nlinarith only [h33suU, h13svL]
  have hb2L : (62 / 1000 : ℝ) ≤ b2 := by
    dsimp only [b2]
    nlinarith only [h13suL, h11svU]
  have hb2U : b2 ≤ (673 / 10000 : ℝ) := by
    dsimp only [b2]
    nlinarith only [h13suU, h11svL]
  have hu4Term := nonnegative_product_upper
    u4 b1 (18 / 125) (3006 / 10000) hu4U hb1U
    (by norm_num) (by linarith only [hb1L])
  have htTerm := nonnegative_product_upper
    (-v4) b2 (4 / 1000) (673 / 10000)
    (by linarith only [hv4L]) hb2U (by norm_num)
    (by linarith only [hb2L])
  have hcoupling : (u4 * b1 + (-v4) * b2) / 2 ≤
      (218 / 10000 : ℝ) := by
    nlinarith only [hu4Term, htTerm]
  have hsplit :
      cleanRSlopeC R C D F a x r c d f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33 =
        -((R + cornerR + 2 * r) * op +
            (3 * (R + cornerR) - 2 * r) * om +
              (3 * (R + cornerR) + 2 * r) * ox) / 4 +
          (u4 * b1 + (-v4) * b2) / 2 := by
    unfold cleanRSlopeC cleanRSecant quadraticSecant
      correlatedCoefficientThree alignedDeterminant alignedMixedDeterminant
      alignedAdjugatePair alignedMixedAdjugatePair alignedCrossEnergy
      alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
      alignedEntry24 mixedDeterminantOne
    dsimp only [op, om, ox, b1, b2]
    simp only [cornerA, cornerX, cornerR, cornerC, cornerD, cornerU4,
      cornerDv, cornerQ11, cornerQ13, cornerQ33, cornerH11, cornerH13]
    ring
  rw [hsplit]
  nlinarith only [hdet, hcoupling]

set_option maxHeartbeats 5000000 in
theorem cleanRSlopeH11_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    cleanRSlopeH11
    R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 ≤ (-1 / 1000 : ℝ) := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
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
  norm_num at hRL hRU hCL hCU hDL hDU hFL hFU haL haU hxL hxU hrL hrU hcL hcU hdL hdU hfL hfU hsuL hsuU hduL hduU hu4L hu4U hsvL hsvU hdvL hdvU hv4L hv4U hq11L hq11U hq13L hq13U hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
  let mh : ℝ :=
    R * (c + cornerC) / 2 + c * (cornerR / 2 - r) +
      d * (cornerX - x) + cornerC * r +
        (42817 / 1000000) * x + 82740059 / 25000000000
  let qg : ℝ :=
    R * (c - cornerC) / 2 + c * (r + cornerR / 2) +
      d * (x + cornerX) + cornerC * r +
        (42817 / 1000000) * x - 82740059 / 25000000000
  have hR0 : 0 ≤ R := by linarith only [hRL]
  have hc0 : 0 ≤ c := by linarith only [hcL]
  have hd0 : 0 ≤ d := by linarith only [hdL]
  have hr0 : 0 ≤ r := by linarith only [hrL]
  have hx0 : 0 ≤ x := by linarith only [hxL]
  have hcPlusL : (5179 / 1000000 : ℝ) + cornerC ≤
      c + cornerC := by linarith only [hcL]
  have hcPlus0 : 0 ≤ c + cornerC := by
    norm_num [cornerC] at ⊢
    linarith only [hcL]
  have hRcPlus := nonnegative_product_lower
    R (c + cornerC) (242817 / 1000000) (5179 / 1000000 + cornerC)
    hRL hcPlusL (by norm_num [cornerC]) hcPlus0
  have hRGap : (cornerR / 2 - 57183 / 1000000 : ℝ) ≤
      cornerR / 2 - r := by linarith only [hrU]
  have hRGap0 : 0 ≤ cornerR / 2 - r := by
    norm_num [cornerR] at ⊢
    linarith only [hrU]
  have hcRGap := nonnegative_product_lower
    c (cornerR / 2 - r) (5179 / 1000000)
      (cornerR / 2 - 57183 / 1000000)
    hcL hRGap (by norm_num) hRGap0
  have hXGap : (cornerX - 39761 / 1000000 : ℝ) ≤
      cornerX - x := by linarith only [hxU]
  have hXGap0 : 0 ≤ cornerX - x := by
    norm_num [cornerX] at ⊢
    linarith only [hxU]
  have hdXGap := nonnegative_product_lower
    d (cornerX - x) (23317 / 1000000)
      (cornerX - 39761 / 1000000)
    hdL hXGap (by norm_num) hXGap0
  have hcrLower :
      (5179 / 1000000 : ℝ) *
            (cornerR / 2 - 49817 / 1000000) +
          cornerC * (49817 / 1000000) ≤
        c * (cornerR / 2 - r) + cornerC * r := by
    have hcrShift : 0 ≤
        (c - 5179 / 1000000) * (cornerR / 2 - r) :=
      mul_nonneg (sub_nonneg.mpr hcL) hRGap0
    have hcrRise : 0 ≤
        (cornerC - 5179 / 1000000) * (r - 49817 / 1000000) :=
      mul_nonneg (by norm_num [cornerC]) (sub_nonneg.mpr hrL)
    nlinarith only [hcrShift, hcrRise]
  have hdxLower :
      (23317 / 1000000 : ℝ) *
            (cornerX - 37851 / 1000000) +
          (42817 / 1000000) * (37851 / 1000000) ≤
        d * (cornerX - x) + (42817 / 1000000) * x := by
    have hdxShift : 0 ≤
        (d - 23317 / 1000000) * (cornerX - x) :=
      mul_nonneg (sub_nonneg.mpr hdL) hXGap0
    have hdxRise : 0 ≤
        ((42817 / 1000000 : ℝ) - 23317 / 1000000) *
          (x - 37851 / 1000000) :=
      mul_nonneg (by norm_num) (sub_nonneg.mpr hxL)
    nlinarith only [hdxShift, hdxRise]
  have hmh : (82 / 10000 : ℝ) ≤ mh := by
    calc
      (82 / 10000 : ℝ) ≤
          ((242817 / 1000000) *
              (5179 / 1000000 + cornerC)) / 2 +
            ((5179 / 1000000) *
                (cornerR / 2 - 49817 / 1000000) +
              cornerC * (49817 / 1000000)) +
            ((23317 / 1000000) *
                (cornerX - 37851 / 1000000) +
              (42817 / 1000000) * (37851 / 1000000)) +
            82740059 / 25000000000 := by
              norm_num [cornerC, cornerR, cornerX]
      _ ≤ mh := by
        dsimp only [mh]
        nlinarith only [hRcPlus, hcrLower, hdxLower]
  have hcMinusL : (5179 / 1000000 : ℝ) - cornerC ≤
      c - cornerC := by linarith only [hcL]
  have hcMinusLNeg :
      (5179 / 1000000 : ℝ) - cornerC ≤ 0 := by
    norm_num [cornerC]
  have hRcMinus := positive_negative_product_lower
    R (c - cornerC) cornerR (5179 / 1000000 - cornerC)
    hR0 hcMinusL hcMinusLNeg
    (by
      norm_num [cornerR] at ⊢
      exact hRU)
  have hrPlusL : (49817 / 1000000 : ℝ) + cornerR / 2 ≤
      r + cornerR / 2 := by linarith only [hrL]
  have hrPlus0 : 0 ≤ r + cornerR / 2 := by
    norm_num [cornerR] at ⊢
    linarith only [hrL]
  have hcRPlus := nonnegative_product_lower
    c (r + cornerR / 2) (5179 / 1000000)
      (49817 / 1000000 + cornerR / 2)
    hcL hrPlusL (by norm_num) hrPlus0
  have hxPlusL : (37851 / 1000000 : ℝ) + cornerX ≤
      x + cornerX := by linarith only [hxL]
  have hxPlus0 : 0 ≤ x + cornerX := by
    norm_num [cornerX] at ⊢
    linarith only [hxL]
  have hdXPlus := nonnegative_product_lower
    d (x + cornerX) (23317 / 1000000)
      (37851 / 1000000 + cornerX)
    hdL hxPlusL (by norm_num) hxPlus0
  have hqg : (68 / 100000 : ℝ) ≤ qg := by
    dsimp only [qg]
    norm_num [cornerC, cornerR, cornerX] at hRcMinus hcRPlus hdXPlus ⊢
    nlinarith only [hRcMinus, hcRPlus, hdXPlus, hrL, hxL]
  have hhmag : (117 / 1000 : ℝ) ≤ -h33 := by
    linarith only [hh33U]
  have hdetProd := nonnegative_product_lower
    (-h33) mh (117 / 1000) (82 / 10000)
    hhmag hmh (by norm_num) (by linarith only [hmh])
  have hdet : -((-h33) * mh + cornerQ33 * qg) ≤
      (-11 / 10000 : ℝ) := by
    norm_num [cornerQ33] at ⊢
    nlinarith only [hdetProd, hqg]
  have hRCoef : (371 / 1000 : ℝ) ≤ R + cornerR - 2 * r := by
    norm_num [cornerR] at ⊢
    linarith only [hRL, hrU]
  have hDCoef : (15 / 1000 : ℝ) ≤
      (42817 / 1000000) - d := by
    linarith only [hdU]
  have hdv0 : 0 ≤ dv := by linarith only [hdvL]
  have hsv0 : 0 ≤ sv := by linarith only [hsvL]
  have ht0 : 0 ≤ -v4 := by linarith only [hv4U]
  have hFirst := nonnegative_triple_lower
    (R + cornerR - 2 * r) dv dv
    (371 / 1000) (111 / 2000) (111 / 2000)
    hRCoef hdvL hdvL (by norm_num) (by norm_num) hdv0 hdv0
  have hSecond := nonnegative_triple_lower
    ((42817 / 1000000) - d) dv sv
    (15 / 1000) (111 / 2000) (10763 / 20000)
    hDCoef hdvL hsvL (by norm_num) (by norm_num) hdv0 hsv0
  have hCmag0 : 0 ≤ cornerC - c := by
    norm_num [cornerC] at ⊢
    linarith only [hcU]
  have hCmagU : cornerC - c ≤ (81 / 10000 : ℝ) := by
    norm_num [cornerC] at ⊢
    linarith only [hcL]
  have hLast := nonnegative_triple_upper
    (cornerC - c) sv (-v4)
    (81 / 10000) (13459 / 25000) (4 / 1000)
    hCmagU hsvU (by linarith only [hv4L])
    (by norm_num) (by norm_num) hsv0 ht0
  let rem : ℝ :=
    (R + cornerR - 2 * r) * dv ^ 2 / 4 +
      ((42817 / 1000000) - d) * dv * sv / 2 +
        (cornerX - x) * dv * (-v4) / 2 -
          (cornerC - c) * sv * (-v4) / 2
  have hrem : 0 ≤ rem := by
    have hThird : 0 ≤ (cornerX - x) * dv * (-v4) :=
      mul_nonneg (mul_nonneg hXGap0 hdv0) ht0
    dsimp only [rem]
    norm_num [cornerR, cornerX, cornerC] at hFirst hSecond hThird hLast ⊢
    nlinarith only [hFirst, hSecond, hThird, hLast]
  have hsplit :
      cleanRSlopeH11 R C D F a x r c d f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33 =
        -((-h33) * mh + cornerQ33 * qg) - rem := by
    unfold cleanRSlopeH11 cleanRSecant quadraticSecant
      correlatedCoefficientThree alignedDeterminant alignedMixedDeterminant
      alignedAdjugatePair alignedMixedAdjugatePair alignedCrossEnergy
      alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
      alignedEntry24 mixedDeterminantOne
    dsimp only [mh, qg, rem]
    simp only [cornerA, cornerX, cornerR, cornerC, cornerD, cornerU4,
      cornerDv, cornerQ11, cornerQ13, cornerQ33, cornerH11, cornerH13]
    ring
  rw [hsplit]
  nlinarith only [hdet, hrem]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3Structural
