import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3CleanRCoreStructural

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
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

/-! The `R`-secants which occur in the three odd-Gram slopes have a common
factorization.  We record their positive magnitudes, rather than asking an
interval tactic to rediscover the fully expanded polynomial. -/

private def cleanRDetMinusMagnitude
    (R C D x r c d : ℝ) : ℝ :=
  ((3 * C - c) * (R + cornerR) - 2 * (C + c) * r +
      2 * (3 * D * cornerX - D * x - cornerX * d - d * x)) / 4

private def cleanRDetMixedMagnitude
    (R C D x r c d : ℝ) : ℝ :=
  ((3 * C + c) * (R + cornerR) + 2 * (C - c) * r +
      2 * (3 * D * cornerX + D * x + cornerX * d - d * x)) / 4

private def cleanRDetPlusMagnitude
    (R C D x r c d : ℝ) : ℝ :=
  ((C + c) * (R + cornerR + 2 * r) +
      2 * (D + d) * (cornerX + x)) / 4

private def cleanRAdjPlusMagnitude
    (R C D x r c d sx dx zx sy dy zy : ℝ) : ℝ :=
  ((C + c) * (sx * zy + zx * sy) +
      (D + d) * (dx * sy + sx * dy) +
      (R + cornerR + 2 * r) * dx * dy -
      (cornerX + x) * (dx * zy + zx * dy)) / 4

private def cleanRAdjMixedMagnitude
    (R C D sx dx zx sy dy zy : ℝ) : ℝ :=
  (C * (sx * zy + zx * sy) +
      D * (dx * sy + sx * dy) +
      (R + cornerR) * dx * dy -
      cornerX * (dx * zy + zx * dy)) / 2

private theorem cleanRSlopeQ13_factorization
    (R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    cleanRSlopeQ13
        R C D F a x r c d f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33 =
      cleanRDetMinusMagnitude R C D x r c d *
          (q13 + cornerQ13 - 2 * h13) +
        2 * cleanRDetMixedMagnitude R C D x r c d *
          (q13 + cornerQ13) +
        cleanRDetPlusMagnitude R C D x r c d *
          (q13 + cornerQ13 + 2 * h13) -
        2 * cleanRAdjPlusMagnitude R C D x r c d
          su du u4 sv dv v4 -
        2 * cleanRAdjMixedMagnitude R C D
          su du u4 sv dv v4 := by
  unfold cleanRSlopeQ13 cleanRSecant quadraticSecant
    correlatedCoefficientThree alignedDeterminant alignedMixedDeterminant
    alignedAdjugatePair alignedMixedAdjugatePair alignedCrossEnergy
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne cleanRDetMinusMagnitude
    cleanRDetMixedMagnitude cleanRDetPlusMagnitude
    cleanRAdjPlusMagnitude cleanRAdjMixedMagnitude
  dsimp only
  simp only [cornerA, cornerX, cornerR, cornerQ13]
  ring

private theorem cleanRSlopeQ11_factorization
    (R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    cleanRSlopeQ11
        R C D F a x r c d f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33 =
      -cleanRDetMinusMagnitude R C D x r c d * (q33 - h33) -
        2 * cleanRDetMixedMagnitude R C D x r c d * q33 -
        cleanRDetPlusMagnitude R C D x r c d * (q33 + h33) +
        cleanRAdjPlusMagnitude R C D x r c d
          sv dv v4 sv dv v4 +
        cleanRAdjMixedMagnitude R C D sv dv v4 sv dv v4 := by
  unfold cleanRSlopeQ11 cleanRSecant quadraticSecant
    correlatedCoefficientThree alignedDeterminant alignedMixedDeterminant
    alignedAdjugatePair alignedMixedAdjugatePair alignedCrossEnergy
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne cleanRDetMinusMagnitude
    cleanRDetMixedMagnitude cleanRDetPlusMagnitude
    cleanRAdjPlusMagnitude cleanRAdjMixedMagnitude
  dsimp only
  simp only [cornerA, cornerX, cornerR, cornerQ11, cornerQ13]
  ring

private theorem cleanRSlopeQ33_factorization
    (R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    cleanRSlopeQ33
        R C D F a x r c d f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33 =
      -cleanRDetMinusMagnitude R cornerC (42817 / 1000000)
          x r c d * (cornerQ11 - h11) -
        2 * cleanRDetMixedMagnitude R cornerC (42817 / 1000000)
          x r c d * cornerQ11 -
        cleanRDetPlusMagnitude R cornerC (42817 / 1000000)
          x r c d * (cornerQ11 + h11) +
        cleanRAdjPlusMagnitude R cornerC (42817 / 1000000)
          x r c d su du u4 su du u4 +
        cleanRAdjMixedMagnitude R cornerC (42817 / 1000000)
          su du u4 su du u4 := by
  unfold cleanRSlopeQ33 cleanRSecant quadraticSecant
    correlatedCoefficientThree alignedDeterminant alignedMixedDeterminant
    alignedAdjugatePair alignedMixedAdjugatePair alignedCrossEnergy
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne cleanRDetMinusMagnitude
    cleanRDetMixedMagnitude cleanRDetPlusMagnitude
    cleanRAdjPlusMagnitude cleanRAdjMixedMagnitude
  dsimp only
  simp only [cornerA, cornerX, cornerR, cornerC, cornerQ11,
    cornerQ13, cornerQ33]
  ring

private theorem cleanRDetMagnitude_lower_bounds
    (R C D x r c d : ℝ)
    (hRL : (242817 / 1000000 : ℝ) ≤ R)
    (hRU : R ≤ 242898 / 1000000)
    (hCL : (1323 / 100000 : ℝ) ≤ C)
    (hCU : C ≤ 1342 / 100000)
    (hDL : (42817 / 1000000 : ℝ) ≤ D)
    (hDU : D ≤ 42898 / 1000000)
    (hxL : (37851 / 1000000 : ℝ) ≤ x)
    (hxU : x ≤ 39761 / 1000000)
    (hrL : (49817 / 1000000 : ℝ) ≤ r)
    (hrU : r ≤ 57183 / 1000000)
    (hcL : (5179 / 1000000 : ℝ) ≤ c)
    (hcU : c ≤ 7165 / 1000000)
    (hdL : (23317 / 1000000 : ℝ) ≤ d)
    (hdU : d ≤ 27183 / 1000000) :
    (39 / 10000 : ℝ) ≤ cleanRDetMinusMagnitude R C D x r c d ∧
      (88 / 10000 : ℝ) ≤ cleanRDetMixedMagnitude R C D x r c d ∧
      (52 / 10000 : ℝ) ≤ cleanRDetPlusMagnitude R C D x r c d := by
  have hR0 : (0 : ℝ) ≤ R := le_trans (by norm_num) hRL
  have hC0 : (0 : ℝ) ≤ C := le_trans (by norm_num) hCL
  have hD0 : (0 : ℝ) ≤ D := le_trans (by norm_num) hDL
  have hx0 : (0 : ℝ) ≤ x := le_trans (by norm_num) hxL
  have hr0 : (0 : ℝ) ≤ r := le_trans (by norm_num) hrL
  have hc0 : (0 : ℝ) ≤ c := le_trans (by norm_num) hcL
  have hd0 : (0 : ℝ) ≤ d := le_trans (by norm_num) hdL
  have hRsumL : (485715 / 1000000 : ℝ) ≤ R + cornerR := by
    norm_num [cornerR] at ⊢
    linarith only [hRL]
  have hRsum0 : (0 : ℝ) ≤ R + cornerR :=
    le_trans (by norm_num) hRsumL
  have hCmL : (32525 / 1000000 : ℝ) ≤ 3 * C - c := by
    linarith only [hCL, hcU]
  have hm1 : (1579 / 100000 : ℝ) ≤
      (3 * C - c) * (R + cornerR) := by
    have hprod := nonnegative_product_lower
      (3 * C - c) (R + cornerR)
      (32525 / 1000000) (485715 / 1000000)
      hCmL hRsumL (by norm_num) hRsum0
    exact le_trans (by norm_num) hprod
  have hCcU : C + c ≤ (20585 / 1000000 : ℝ) := by
    linarith only [hCU, hcU]
  have hm2 : (C + c) * r ≤ (118 / 100000 : ℝ) := by
    have hprod := nonnegative_product_upper
      (C + c) r (20585 / 1000000) (57183 / 1000000)
      hCcU hrU (by norm_num) hr0
    exact le_trans hprod (by norm_num)
  have hm3 : (170 / 100000 : ℝ) ≤ D * cornerX := by
    have hprod := nonnegative_product_lower
      D cornerX (42817 / 1000000) cornerX
      hDL le_rfl (by norm_num) (by norm_num [cornerX])
    exact le_trans (by norm_num [cornerX]) hprod
  have hm4 : D * x ≤ (171 / 100000 : ℝ) := by
    have hprod := nonnegative_product_upper
      D x (42898 / 1000000) (39761 / 1000000)
      hDU hxU (by norm_num) hx0
    exact le_trans hprod (by norm_num)
  have hm5 : cornerX * d ≤ (109 / 100000 : ℝ) := by
    have hprod := nonnegative_product_upper
      cornerX d cornerX (27183 / 1000000)
      le_rfl hdU (by norm_num [cornerX]) hd0
    exact le_trans hprod (by norm_num [cornerX])
  have hm6 : d * x ≤ (109 / 100000 : ℝ) := by
    have hprod := nonnegative_product_upper
      d x (27183 / 1000000) (39761 / 1000000)
      hdU hxU (by norm_num) hx0
    exact le_trans hprod (by norm_num)
  have hCpL : (44869 / 1000000 : ℝ) ≤ 3 * C + c := by
    linarith only [hCL, hcL]
  have hx1 : (2179 / 100000 : ℝ) ≤
      (3 * C + c) * (R + cornerR) := by
    have hprod := nonnegative_product_lower
      (3 * C + c) (R + cornerR)
      (44869 / 1000000) (485715 / 1000000)
      hCpL hRsumL (by norm_num) hRsum0
    exact le_trans (by norm_num) hprod
  have hCsubcL : (6065 / 1000000 : ℝ) ≤ C - c := by
    linarith only [hCL, hcU]
  have hx2 : (30 / 100000 : ℝ) ≤ (C - c) * r := by
    have hprod := nonnegative_product_lower
      (C - c) r (6065 / 1000000) (49817 / 1000000)
      hCsubcL hrL (by norm_num) hr0
    exact le_trans (by norm_num) hprod
  have hx3 : (162 / 100000 : ℝ) ≤ D * x := by
    have hprod := nonnegative_product_lower
      D x (42817 / 1000000) (37851 / 1000000)
      hDL hxL (by norm_num) hx0
    exact le_trans (by norm_num) hprod
  have hx4 : (92 / 100000 : ℝ) ≤ cornerX * d := by
    have hprod := nonnegative_product_lower
      cornerX d cornerX (23317 / 1000000)
      le_rfl hdL (by norm_num [cornerX]) hd0
    exact le_trans (by norm_num [cornerX]) hprod
  have hCcL : (18409 / 1000000 : ℝ) ≤ C + c := by
    linarith only [hCL, hcL]
  have hRtworL : (585349 / 1000000 : ℝ) ≤
      R + cornerR + 2 * r := by
    norm_num [cornerR] at ⊢
    linarith only [hRL, hrL]
  have hRtwor0 : (0 : ℝ) ≤ R + cornerR + 2 * r :=
    le_trans (by norm_num) hRtworL
  have hp1 : (1077 / 100000 : ℝ) ≤
      (C + c) * (R + cornerR + 2 * r) := by
    have hprod := nonnegative_product_lower
      (C + c) (R + cornerR + 2 * r)
      (18409 / 1000000) (585349 / 1000000)
      hCcL hRtworL (by norm_num) hRtwor0
    exact le_trans (by norm_num) hprod
  have hDdL : (66134 / 1000000 : ℝ) ≤ D + d := by
    linarith only [hDL, hdL]
  have hXxL : (77621 / 1000000 : ℝ) ≤ cornerX + x := by
    norm_num [cornerX] at ⊢
    linarith only [hxL]
  have hXx0 : (0 : ℝ) ≤ cornerX + x :=
    le_trans (by norm_num) hXxL
  have hp2 : (513 / 100000 : ℝ) ≤
      (D + d) * (cornerX + x) := by
    have hprod := nonnegative_product_lower
      (D + d) (cornerX + x)
      (66134 / 1000000) (77621 / 1000000)
      hDdL hXxL (by norm_num) hXx0
    exact le_trans (by norm_num) hprod
  constructor
  · unfold cleanRDetMinusMagnitude
    nlinarith only [hm1, hm2, hm3, hm4, hm5, hm6]
  constructor
  · unfold cleanRDetMixedMagnitude
    nlinarith only [hx1, hx2, hm3, hx3, hx4, hm6]
  · unfold cleanRDetPlusMagnitude
    nlinarith only [hp1, hp2]

private theorem cleanRAdjUV_upper_bounds
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    cleanRAdjPlusMagnitude R C D x r c d
        su du u4 sv dv v4 ≤ (11 / 10000 : ℝ) ∧
      cleanRAdjMixedMagnitude R C D su du u4 sv dv v4 ≤
        (15 / 10000 : ℝ) := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  have hsu0 : (0 : ℝ) ≤ su := le_trans (by norm_num) hsuL
  have hdu0 : (0 : ℝ) ≤ du := le_trans (by norm_num) hduL
  have hu40 : (0 : ℝ) ≤ u4 := le_trans (by norm_num) hu4L
  have hsv0 : (0 : ℝ) ≤ sv := le_trans (by norm_num) hsvL
  have hdv0 : (0 : ℝ) ≤ dv := le_trans (by norm_num) hdvL
  have hv40 : v4 ≤ (0 : ℝ) := le_trans hv4U (by norm_num)
  have hsuv4L := positive_negative_product_lower
    su v4 (56173 / 100000) (-4 / 1000)
    hsu0 hv4L (by norm_num) hsuU
  have hsuv4U := positive_negative_product_upper
    su v4 (56168 / 100000) (-2 / 1000)
    hsuL hv40 (by norm_num) hv4U
  have hu4svL := nonnegative_product_lower
    u4 sv (141 / 1000) (53815 / 100000)
    hu4L hsvL (by norm_num) hsv0
  have hu4svU := nonnegative_product_upper
    u4 sv (144 / 1000) (53836 / 100000)
    hu4U hsvU (by norm_num) hsv0
  have hsxyzL : (73 / 1000 : ℝ) ≤ su * v4 + u4 * sv := by
    nlinarith only [hsuv4L, hu4svL]
  have hsxyzU : su * v4 + u4 * sv ≤ (765 / 10000 : ℝ) := by
    nlinarith only [hsuv4U, hu4svU]
  have hsxyz0 : (0 : ℝ) ≤ su * v4 + u4 * sv :=
    le_trans (by norm_num) hsxyzL
  have hduSvU := nonnegative_product_upper
    du sv (1692 / 100000) (53836 / 100000)
    hduU hsvU (by norm_num) hsv0
  have hsuDvU := nonnegative_product_upper
    su dv (56173 / 100000) (558 / 10000)
    hsuU hdvU (by norm_num) hdv0
  have hdxsyU : du * sv + su * dv ≤ (405 / 10000 : ℝ) := by
    nlinarith only [hduSvU, hsuDvU]
  have hdxsy0 : (0 : ℝ) ≤ du * sv + su * dv :=
    add_nonneg (mul_nonneg hdu0 hsv0) (mul_nonneg hsu0 hdv0)
  have hduv4L := positive_negative_product_lower
    du v4 (1692 / 100000) (-4 / 1000)
    hdu0 hv4L (by norm_num) hduU
  have hu4dvL := nonnegative_product_lower
    u4 dv (141 / 1000) (555 / 10000)
    hu4L hdvL (by norm_num) hdv0
  have hdxzyL : (775 / 100000 : ℝ) ≤ du * v4 + u4 * dv := by
    nlinarith only [hduv4L, hu4dvL]
  have hdxzy0 : (0 : ℝ) ≤ du * v4 + u4 * dv :=
    le_trans (by norm_num) hdxzyL
  have hCcU : C + c ≤ (20585 / 1000000 : ℝ) := by
    linarith only [hCU, hcU]
  have hDdU : D + d ≤ (70081 / 1000000 : ℝ) := by
    linarith only [hDU, hdU]
  have hRtworU : R + cornerR + 2 * r ≤ (600162 / 1000000 : ℝ) := by
    norm_num [cornerR] at ⊢
    linarith only [hRU, hrU]
  have hRtwor0 : (0 : ℝ) ≤ R + cornerR + 2 * r := by
    norm_num [cornerR] at ⊢
    linarith only [hRL, hrL]
  have hXxL : (77621 / 1000000 : ℝ) ≤ cornerX + x := by
    norm_num [cornerX] at ⊢
    linarith only [hxL]
  have hXx0 : (0 : ℝ) ≤ cornerX + x :=
    le_trans (by norm_num) hXxL
  have hp1 : (C + c) * (su * v4 + u4 * sv) ≤
      (158 / 100000 : ℝ) := by
    have hprod := nonnegative_product_upper
      (C + c) (su * v4 + u4 * sv)
      (20585 / 1000000) (765 / 10000)
      hCcU hsxyzU (by norm_num) hsxyz0
    exact le_trans hprod (by norm_num)
  have hp2 : (D + d) * (du * sv + su * dv) ≤
      (284 / 100000 : ℝ) := by
    have hprod := nonnegative_product_upper
      (D + d) (du * sv + su * dv)
      (70081 / 1000000) (405 / 10000)
      hDdU hdxsyU (by norm_num) hdxsy0
    exact le_trans hprod (by norm_num)
  have hp3 : (R + cornerR + 2 * r) * du * dv ≤
      (57 / 100000 : ℝ) := by
    have hprod := nonnegative_triple_upper
      (R + cornerR + 2 * r) du dv
      (600162 / 1000000) (1692 / 100000) (558 / 10000)
      hRtworU hduU hdvU (by norm_num) (by norm_num) hdu0 hdv0
    exact le_trans hprod (by norm_num)
  have hp4 : (59 / 100000 : ℝ) ≤
      (cornerX + x) * (du * v4 + u4 * dv) := by
    have hprod := nonnegative_product_lower
      (cornerX + x) (du * v4 + u4 * dv)
      (77621 / 1000000) (775 / 100000)
      hXxL hdxzyL (by norm_num) hdxzy0
    exact le_trans (by norm_num) hprod
  have hm1 : C * (su * v4 + u4 * sv) ≤
      (103 / 100000 : ℝ) := by
    have hprod := nonnegative_product_upper
      C (su * v4 + u4 * sv)
      (1342 / 100000) (765 / 10000)
      hCU hsxyzU (by norm_num) hsxyz0
    exact le_trans hprod (by norm_num)
  have hm2 : D * (du * sv + su * dv) ≤
      (174 / 100000 : ℝ) := by
    have hprod := nonnegative_product_upper
      D (du * sv + su * dv)
      (42898 / 1000000) (405 / 10000)
      hDU hdxsyU (by norm_num) hdxsy0
    exact le_trans hprod (by norm_num)
  have hRsumU : R + cornerR ≤ (485796 / 1000000 : ℝ) := by
    norm_num [cornerR] at ⊢
    linarith only [hRU]
  have hRsum0 : (0 : ℝ) ≤ R + cornerR := by
    norm_num [cornerR] at ⊢
    linarith only [hRL]
  have hm3 : (R + cornerR) * du * dv ≤
      (46 / 100000 : ℝ) := by
    have hprod := nonnegative_triple_upper
      (R + cornerR) du dv
      (485796 / 1000000) (1692 / 100000) (558 / 10000)
      hRsumU hduU hdvU (by norm_num) (by norm_num) hdu0 hdv0
    exact le_trans hprod (by norm_num)
  have hm4 : (30 / 100000 : ℝ) ≤
      cornerX * (du * v4 + u4 * dv) := by
    have hprod := nonnegative_product_lower
      cornerX (du * v4 + u4 * dv)
      cornerX (775 / 100000)
      le_rfl hdxzyL (by norm_num [cornerX]) hdxzy0
    exact le_trans (by norm_num [cornerX]) hprod
  constructor
  · unfold cleanRAdjPlusMagnitude
    nlinarith only [hp1, hp2, hp3, hp4]
  · unfold cleanRAdjMixedMagnitude
    nlinarith only [hm1, hm2, hm3, hm4]

private theorem cleanRAdjVV_upper_bounds
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    cleanRAdjPlusMagnitude R C D x r c d
        sv dv v4 sv dv v4 ≤ (61 / 40000 : ℝ) ∧
      cleanRAdjMixedMagnitude R C D sv dv v4 sv dv v4 ≤
        (41 / 20000 : ℝ) := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  have hsv0 : (0 : ℝ) ≤ sv := le_trans (by norm_num) hsvL
  have hdv0 : (0 : ℝ) ≤ dv := le_trans (by norm_num) hdvL
  have hv40 : v4 ≤ (0 : ℝ) := le_trans hv4U (by norm_num)
  have hsvv4U := positive_negative_product_upper
    sv v4 (53815 / 100000) (-2 / 1000)
    hsvL hv40 (by norm_num) hv4U
  have hsnegU : sv * v4 + v4 * sv ≤ (-10763 / 5000000 : ℝ) := by
    nlinarith only [hsvv4U]
  have hsneg0 : sv * v4 + v4 * sv ≤ (0 : ℝ) :=
    le_trans hsnegU (by norm_num)
  have hdvsvU := nonnegative_product_upper
    dv sv (558 / 10000) (53836 / 100000)
    hdvU hsvU (by norm_num) hsv0
  have hdxsyU : dv * sv + sv * dv ≤ (601 / 10000 : ℝ) := by
    nlinarith only [hdvsvU]
  have hdxsy0 : (0 : ℝ) ≤ dv * sv + sv * dv :=
    add_nonneg (mul_nonneg hdv0 hsv0) (mul_nonneg hsv0 hdv0)
  have hnegv40 : (0 : ℝ) ≤ -v4 := by linarith only [hv40]
  have hnegv4U : -v4 ≤ (4 / 1000 : ℝ) := by
    linarith only [hv4L]
  have hdvnegv4U := nonnegative_product_upper
    dv (-v4) (558 / 10000) (4 / 1000)
    hdvU hnegv4U (by norm_num) hnegv40
  have hnegformU : dv * (-v4) + (-v4) * dv ≤
      (45 / 100000 : ℝ) := by
    nlinarith only [hdvnegv4U]
  have hnegform0 : (0 : ℝ) ≤ dv * (-v4) + (-v4) * dv :=
    add_nonneg (mul_nonneg hdv0 hnegv40) (mul_nonneg hnegv40 hdv0)
  have hCcL : (18409 / 1000000 : ℝ) ≤ C + c := by
    linarith only [hCL, hcL]
  have hCcU : C + c ≤ (20585 / 1000000 : ℝ) := by
    linarith only [hCU, hcU]
  have hDdU : D + d ≤ (70081 / 1000000 : ℝ) := by
    linarith only [hDU, hdU]
  have hRtworU : R + cornerR + 2 * r ≤ (600162 / 1000000 : ℝ) := by
    norm_num [cornerR] at ⊢
    linarith only [hRU, hrU]
  have hXxU : cornerX + x ≤ (79531 / 1000000 : ℝ) := by
    norm_num [cornerX] at ⊢
    linarith only [hxU]
  have hp1 : (C + c) * (sv * v4 + v4 * sv) ≤
      (-39 / 1000000 : ℝ) := by
    have hprod := positive_negative_product_upper
      (C + c) (sv * v4 + v4 * sv)
      (18409 / 1000000) (-10763 / 5000000)
      hCcL hsneg0 (by norm_num) hsnegU
    exact le_trans hprod (by norm_num)
  have hp2 : (D + d) * (dv * sv + sv * dv) ≤
      (422 / 100000 : ℝ) := by
    have hprod := nonnegative_product_upper
      (D + d) (dv * sv + sv * dv)
      (70081 / 1000000) (601 / 10000)
      hDdU hdxsyU (by norm_num) hdxsy0
    exact le_trans hprod (by norm_num)
  have hp3 : (R + cornerR + 2 * r) * dv * dv ≤
      (187 / 100000 : ℝ) := by
    have hprod := nonnegative_triple_upper
      (R + cornerR + 2 * r) dv dv
      (600162 / 1000000) (558 / 10000) (558 / 10000)
      hRtworU hdvU hdvU (by norm_num) (by norm_num) hdv0 hdv0
    exact le_trans hprod (by norm_num)
  have hp4 : -(cornerX + x) * (dv * v4 + v4 * dv) ≤
      (36 / 1000000 : ℝ) := by
    have hprod := nonnegative_product_upper
      (cornerX + x) (dv * (-v4) + (-v4) * dv)
      (79531 / 1000000) (45 / 100000)
      hXxU hnegformU (by norm_num) hnegform0
    calc
      -(cornerX + x) * (dv * v4 + v4 * dv) =
          (cornerX + x) * (dv * (-v4) + (-v4) * dv) := by ring
      _ ≤ (36 / 1000000 : ℝ) := le_trans hprod (by norm_num)
  have hm1 : C * (sv * v4 + v4 * sv) ≤
      (-28 / 1000000 : ℝ) := by
    have hprod := positive_negative_product_upper
      C (sv * v4 + v4 * sv)
      (1323 / 100000) (-10763 / 5000000)
      hCL hsneg0 (by norm_num) hsnegU
    exact le_trans hprod (by norm_num)
  have hm2 : D * (dv * sv + sv * dv) ≤
      (258 / 100000 : ℝ) := by
    have hprod := nonnegative_product_upper
      D (dv * sv + sv * dv)
      (42898 / 1000000) (601 / 10000)
      hDU hdxsyU (by norm_num) hdxsy0
    exact le_trans hprod (by norm_num)
  have hRsumU : R + cornerR ≤ (485796 / 1000000 : ℝ) := by
    norm_num [cornerR] at ⊢
    linarith only [hRU]
  have hm3 : (R + cornerR) * dv * dv ≤
      (152 / 100000 : ℝ) := by
    have hprod := nonnegative_triple_upper
      (R + cornerR) dv dv
      (485796 / 1000000) (558 / 10000) (558 / 10000)
      hRsumU hdvU hdvU (by norm_num) (by norm_num) hdv0 hdv0
    exact le_trans hprod (by norm_num)
  have hm4 : -cornerX * (dv * v4 + v4 * dv) ≤
      (18 / 1000000 : ℝ) := by
    have hprod := nonnegative_product_upper
      cornerX (dv * (-v4) + (-v4) * dv)
      cornerX (45 / 100000)
      le_rfl hnegformU (by norm_num [cornerX]) hnegform0
    calc
      -cornerX * (dv * v4 + v4 * dv) =
          cornerX * (dv * (-v4) + (-v4) * dv) := by ring
      _ ≤ (18 / 1000000 : ℝ) := le_trans hprod (by norm_num [cornerX])
  constructor
  · unfold cleanRAdjPlusMagnitude
    nlinarith only [hp1, hp2, hp3, hp4]
  · unfold cleanRAdjMixedMagnitude
    nlinarith only [hm1, hm2, hm3, hm4]

private theorem cleanRAdjUU_upper_bounds
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    cleanRAdjPlusMagnitude R cornerC (42817 / 1000000)
        x r c d su du u4 su du u4 ≤ (9 / 8000 : ℝ) ∧
      cleanRAdjMixedMagnitude R cornerC (42817 / 1000000)
        su du u4 su du u4 ≤ (3 / 2000 : ℝ) := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  have hsu0 : (0 : ℝ) ≤ su := le_trans (by norm_num) hsuL
  have hdu0 : (0 : ℝ) ≤ du := le_trans (by norm_num) hduL
  have hu40 : (0 : ℝ) ≤ u4 := le_trans (by norm_num) hu4L
  have hsuu4U := nonnegative_product_upper
    su u4 (56173 / 100000) (144 / 1000)
    hsuU hu4U (by norm_num) hu40
  have hsxyzU : su * u4 + u4 * su ≤ (162 / 1000 : ℝ) := by
    nlinarith only [hsuu4U]
  have hsxyz0 : (0 : ℝ) ≤ su * u4 + u4 * su :=
    add_nonneg (mul_nonneg hsu0 hu40) (mul_nonneg hu40 hsu0)
  have hdusuU := nonnegative_product_upper
    du su (1692 / 100000) (56173 / 100000)
    hduU hsuU (by norm_num) hsu0
  have hdxsyU : du * su + su * du ≤ (191 / 10000 : ℝ) := by
    nlinarith only [hdusuU]
  have hdxsy0 : (0 : ℝ) ≤ du * su + su * du :=
    add_nonneg (mul_nonneg hdu0 hsu0) (mul_nonneg hsu0 hdu0)
  have hduu4L := nonnegative_product_lower
    du u4 (1687 / 100000) (141 / 1000)
    hduL hu4L (by norm_num) hu40
  have hdxzyL : (475 / 100000 : ℝ) ≤ du * u4 + u4 * du := by
    nlinarith only [hduu4L]
  have hdxzy0 : (0 : ℝ) ≤ du * u4 + u4 * du :=
    le_trans (by norm_num) hdxzyL
  have hCcU : cornerC + c ≤ (20395 / 1000000 : ℝ) := by
    norm_num [cornerC] at ⊢
    linarith only [hcU]
  have hDdU : (42817 / 1000000 : ℝ) + d ≤
      (70000 / 1000000 : ℝ) := by
    linarith only [hdU]
  have hRtworU : R + cornerR + 2 * r ≤ (600162 / 1000000 : ℝ) := by
    norm_num [cornerR] at ⊢
    linarith only [hRU, hrU]
  have hXxL : (77621 / 1000000 : ℝ) ≤ cornerX + x := by
    norm_num [cornerX] at ⊢
    linarith only [hxL]
  have hXx0 : (0 : ℝ) ≤ cornerX + x :=
    le_trans (by norm_num) hXxL
  have hp1 : (cornerC + c) * (su * u4 + u4 * su) ≤
      (334 / 100000 : ℝ) := by
    have hprod := nonnegative_product_upper
      (cornerC + c) (su * u4 + u4 * su)
      (20395 / 1000000) (162 / 1000)
      hCcU hsxyzU (by norm_num) hsxyz0
    exact le_trans hprod (by norm_num)
  have hp2 : ((42817 / 1000000 : ℝ) + d) *
      (du * su + su * du) ≤ (134 / 100000 : ℝ) := by
    have hprod := nonnegative_product_upper
      ((42817 / 1000000 : ℝ) + d) (du * su + su * du)
      (70000 / 1000000) (191 / 10000)
      hDdU hdxsyU (by norm_num) hdxsy0
    exact le_trans hprod (by norm_num)
  have hp3 : (R + cornerR + 2 * r) * du * du ≤
      (18 / 100000 : ℝ) := by
    have hprod := nonnegative_triple_upper
      (R + cornerR + 2 * r) du du
      (600162 / 1000000) (1692 / 100000) (1692 / 100000)
      hRtworU hduU hduU (by norm_num) (by norm_num) hdu0 hdu0
    exact le_trans hprod (by norm_num)
  have hp4 : (36 / 100000 : ℝ) ≤
      (cornerX + x) * (du * u4 + u4 * du) := by
    have hprod := nonnegative_product_lower
      (cornerX + x) (du * u4 + u4 * du)
      (77621 / 1000000) (475 / 100000)
      hXxL hdxzyL (by norm_num) hdxzy0
    exact le_trans (by norm_num) hprod
  have hm1 : cornerC * (su * u4 + u4 * su) ≤
      (218 / 100000 : ℝ) := by
    have hprod := nonnegative_product_upper
      cornerC (su * u4 + u4 * su)
      cornerC (162 / 1000)
      le_rfl hsxyzU (by norm_num [cornerC]) hsxyz0
    exact le_trans hprod (by norm_num [cornerC])
  have hm2 : (42817 / 1000000 : ℝ) * (du * su + su * du) ≤
      (82 / 100000 : ℝ) := by
    have hprod := nonnegative_product_upper
      (42817 / 1000000 : ℝ) (du * su + su * du)
      (42817 / 1000000) (191 / 10000)
      le_rfl hdxsyU (by norm_num) hdxsy0
    exact le_trans hprod (by norm_num)
  have hRsumU : R + cornerR ≤ (485796 / 1000000 : ℝ) := by
    norm_num [cornerR] at ⊢
    linarith only [hRU]
  have hm3 : (R + cornerR) * du * du ≤
      (14 / 100000 : ℝ) := by
    have hprod := nonnegative_triple_upper
      (R + cornerR) du du
      (485796 / 1000000) (1692 / 100000) (1692 / 100000)
      hRsumU hduU hduU (by norm_num) (by norm_num) hdu0 hdu0
    exact le_trans hprod (by norm_num)
  have hm4 : (18 / 100000 : ℝ) ≤
      cornerX * (du * u4 + u4 * du) := by
    have hprod := nonnegative_product_lower
      cornerX (du * u4 + u4 * du)
      cornerX (475 / 100000)
      le_rfl hdxzyL (by norm_num [cornerX]) hdxzy0
    exact le_trans (by norm_num [cornerX]) hprod
  constructor
  · unfold cleanRAdjPlusMagnitude
    nlinarith only [hp1, hp2, hp3, hp4]
  · unfold cleanRAdjMixedMagnitude
    nlinarith only [hm1, hm2, hm3, hm4]

set_option maxHeartbeats 5000000 in
theorem cleanRSlopeQ13_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (5 / 1000 : ℝ) ≤ cleanRSlopeQ13
    R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.q13_mem with ⟨hq13L, _hq13U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  have hdet := cleanRDetMagnitude_lower_bounds R C D x r c d
    hRL hRU hCL hCU hDL hDU hxL hxU hrL hrU hcL hcU hdL hdU
  have hadj := cleanRAdjUV_upper_bounds A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hqm : (4182 / 10000 : ℝ) ≤
      q13 + cornerQ13 - 2 * h13 := by
    norm_num [cornerQ13] at ⊢
    linarith only [hq13L, hh13U]
  have hqx : (4002 / 10000 : ℝ) ≤ q13 + cornerQ13 := by
    norm_num [cornerQ13] at ⊢
    linarith only [hq13L]
  have hqp : (3782 / 10000 : ℝ) ≤
      q13 + cornerQ13 + 2 * h13 := by
    norm_num [cornerQ13] at ⊢
    linarith only [hq13L, hh13L]
  have hqm0 : (0 : ℝ) ≤ q13 + cornerQ13 - 2 * h13 :=
    le_trans (by norm_num) hqm
  have hqx0 : (0 : ℝ) ≤ q13 + cornerQ13 :=
    le_trans (by norm_num) hqx
  have hqp0 : (0 : ℝ) ≤ q13 + cornerQ13 + 2 * h13 :=
    le_trans (by norm_num) hqp
  have htermM := nonnegative_product_lower
    (cleanRDetMinusMagnitude R C D x r c d)
    (q13 + cornerQ13 - 2 * h13)
    (39 / 10000) (4182 / 10000) hdet.1 hqm
    (by norm_num) hqm0
  have htermX := nonnegative_product_lower
    (cleanRDetMixedMagnitude R C D x r c d)
    (q13 + cornerQ13)
    (88 / 10000) (4002 / 10000) hdet.2.1 hqx
    (by norm_num) hqx0
  have htermP := nonnegative_product_lower
    (cleanRDetPlusMagnitude R C D x r c d)
    (q13 + cornerQ13 + 2 * h13)
    (52 / 10000) (3782 / 10000) hdet.2.2 hqp
    (by norm_num) hqp0
  rw [cleanRSlopeQ13_factorization]
  nlinarith only [htermM, htermX, htermP, hadj.1, hadj.2]

set_option maxHeartbeats 5000000 in
theorem cleanRSlopeQ11_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    cleanRSlopeQ11
    R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 ≤ (-5 / 1000 : ℝ) := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.q33_mem with ⟨hq33L, _hq33U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  have hdet := cleanRDetMagnitude_lower_bounds R C D x r c d
    hRL hRU hCL hCU hDL hDU hxL hxU hrL hrU hcL hcU hdL hdU
  have hadj := cleanRAdjVV_upper_bounds A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hqm : (4485 / 10000 : ℝ) ≤ q33 - h33 := by
    linarith only [hq33L, hh33U]
  have hqx : (3315 / 10000 : ℝ) ≤ q33 := hq33L
  have hqp : (2115 / 10000 : ℝ) ≤ q33 + h33 := by
    linarith only [hq33L, hh33L]
  have hqm0 : (0 : ℝ) ≤ q33 - h33 :=
    le_trans (by norm_num) hqm
  have hqx0 : (0 : ℝ) ≤ q33 :=
    le_trans (by norm_num) hqx
  have hqp0 : (0 : ℝ) ≤ q33 + h33 :=
    le_trans (by norm_num) hqp
  have htermM := nonnegative_product_lower
    (cleanRDetMinusMagnitude R C D x r c d) (q33 - h33)
    (39 / 10000) (4485 / 10000) hdet.1 hqm
    (by norm_num) hqm0
  have htermX := nonnegative_product_lower
    (cleanRDetMixedMagnitude R C D x r c d) q33
    (88 / 10000) (3315 / 10000) hdet.2.1 hqx
    (by norm_num) hqx0
  have htermP := nonnegative_product_lower
    (cleanRDetPlusMagnitude R C D x r c d) (q33 + h33)
    (52 / 10000) (2115 / 10000) hdet.2.2 hqp
    (by norm_num) hqp0
  rw [cleanRSlopeQ11_factorization]
  nlinarith only [htermM, htermX, htermP, hadj.1, hadj.2]

set_option maxHeartbeats 5000000 in
theorem cleanRSlopeQ33_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    cleanRSlopeQ33
    R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 ≤ (-2 / 1000 : ℝ) := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  have hdet := cleanRDetMagnitude_lower_bounds
    R cornerC (42817 / 1000000) x r c d
    hRL hRU (by norm_num [cornerC]) (by norm_num [cornerC])
    (by norm_num) (by norm_num)
    hxL hxU hrL hrU hcL hcU hdL hdU
  have hadj := cleanRAdjUU_upper_bounds A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hqm : (1578 / 10000 : ℝ) ≤ cornerQ11 - h11 := by
    norm_num [cornerQ11] at ⊢
    linarith only [hh11U]
  have hqx : (1778 / 10000 : ℝ) ≤ cornerQ11 := by
    norm_num [cornerQ11]
  have hqp : (1918 / 10000 : ℝ) ≤ cornerQ11 + h11 := by
    norm_num [cornerQ11] at ⊢
    linarith only [hh11L]
  have hqm0 : (0 : ℝ) ≤ cornerQ11 - h11 :=
    le_trans (by norm_num) hqm
  have hqx0 : (0 : ℝ) ≤ cornerQ11 :=
    le_trans (by norm_num) hqx
  have hqp0 : (0 : ℝ) ≤ cornerQ11 + h11 :=
    le_trans (by norm_num) hqp
  have htermM := nonnegative_product_lower
    (cleanRDetMinusMagnitude R cornerC (42817 / 1000000) x r c d)
    (cornerQ11 - h11) (39 / 10000) (1578 / 10000)
    hdet.1 hqm (by norm_num) hqm0
  have htermX := nonnegative_product_lower
    (cleanRDetMixedMagnitude R cornerC (42817 / 1000000) x r c d)
    cornerQ11 (88 / 10000) (1778 / 10000)
    hdet.2.1 hqx (by norm_num) hqx0
  have htermP := nonnegative_product_lower
    (cleanRDetPlusMagnitude R cornerC (42817 / 1000000) x r c d)
    (cornerQ11 + h11) (52 / 10000) (1918 / 10000)
    hdet.2.2 hqp (by norm_num) hqp0
  rw [cleanRSlopeQ33_factorization]
  nlinarith only [htermM, htermX, htermP, hadj.1, hadj.2]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3Structural
