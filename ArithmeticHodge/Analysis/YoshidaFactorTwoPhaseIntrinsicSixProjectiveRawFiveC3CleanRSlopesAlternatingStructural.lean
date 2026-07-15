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

private theorem product_upper_of_nonnegative_left
    (a b aU bU : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ aU)
    (hb : b ≤ bU) (hbU0 : 0 ≤ bU) :
    a * b ≤ aU * bU := by
  have hfirst := mul_nonneg (sub_nonneg.mpr ha) hbU0
  have hsecond := mul_nonneg ha0 (sub_nonneg.mpr hb)
  nlinarith only [hfirst, hsecond]

private def cleanRDetMinusCoefficient (R x r c d : ℝ) : ℝ :=
  (-3 * cornerC * R - 3 * cornerC * cornerR + 2 * cornerC * r -
      6 * (42817 / 1000000) * cornerX + 2 * (42817 / 1000000) * x +
      R * c + cornerR * c + 2 * cornerX * d + 2 * c * r + 2 * d * x) / 4

private def cleanRDetMixedCoefficient (R x r c d : ℝ) : ℝ :=
  (-3 * cornerC * R - 3 * cornerC * cornerR - 2 * cornerC * r -
      6 * (42817 / 1000000) * cornerX - 2 * (42817 / 1000000) * x -
      R * c - cornerR * c - 2 * cornerX * d + 2 * c * r + 2 * d * x) / 4

private def cleanRDetPlusCoefficient (R x r c d : ℝ) : ℝ :=
  -(cornerC * R + cornerC * cornerR + 2 * cornerC * r +
      2 * (42817 / 1000000) * cornerX + 2 * (42817 / 1000000) * x +
      R * c + cornerR * c + 2 * cornerX * d + 2 * c * r + 2 * d * x) / 4

private def cleanRBilinear (R su du sv v4 : ℝ) : ℝ :=
  cornerC * (su * v4 + sv * cornerU4) +
    (42817 / 1000000) * (du * sv + cornerDv * su) +
      (R + cornerR) * du * cornerDv -
        cornerX * (du * v4 + cornerDv * cornerU4)

private def perturbRBilinear (x r c d su du sv v4 : ℝ) : ℝ :=
  c * (su * v4 + sv * cornerU4) +
    d * (du * sv + cornerDv * su) + 2 * r * du * cornerDv -
      x * (du * v4 + cornerDv * cornerU4)

private def cleanRUQuadratic (R su du : ℝ) : ℝ :=
  2 * cornerC * su * cornerU4 +
    2 * (42817 / 1000000) * du * su + (R + cornerR) * du ^ 2 -
      2 * cornerX * du * cornerU4

private def cleanRVQuadratic (R sv v4 : ℝ) : ℝ :=
  2 * cornerC * sv * v4 +
    2 * (42817 / 1000000) * cornerDv * sv +
      (R + cornerR) * cornerDv ^ 2 - 2 * cornerX * cornerDv * v4

private def perturbRUQuadratic (x r c d su du : ℝ) : ℝ :=
  2 * c * su * cornerU4 + 2 * d * du * su + 2 * r * du ^ 2 -
    2 * x * du * cornerU4

private def perturbRVQuadratic (x r c d sv v4 : ℝ) : ℝ :=
  2 * c * sv * v4 + 2 * d * cornerDv * sv +
    2 * r * cornerDv ^ 2 - 2 * x * cornerDv * v4

private theorem cleanR_determinant_coefficient_bounds
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (-458 / 100000 : ℝ) ≤ cleanRDetMinusCoefficient R x r c d ∧
      cleanRDetMinusCoefficient R x r c d ≤ (-398 / 100000 : ℝ) ∧
      cleanRDetMixedCoefficient R x r c d ≤ (-9 / 1000 : ℝ) ∧
      cleanRDetPlusCoefficient R x r c d ≤ (-52 / 10000 : ℝ) := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  norm_num at hRL hRU hxL hxU hrL hrU hcL hcU hdL hdU
  have hR0 : 0 ≤ R := by linarith only [hRL]
  have hx0 : 0 ≤ x := by linarith only [hxL]
  have hr0 : 0 ≤ r := by linarith only [hrL]
  have hc0 : 0 ≤ c := by linarith only [hcL]
  have hd0 : 0 ≤ d := by linarith only [hdL]
  have hRcL := nonnegative_product_lower
    R c (242817 / 1000000) (5179 / 1000000)
    hRL hcL (by norm_num) hc0
  have hRcU := nonnegative_product_upper
    R c (121449 / 500000) (1433 / 200000)
    hRU hcU (by norm_num) hc0
  have hcrL := nonnegative_product_lower
    c r (5179 / 1000000) (49817 / 1000000)
    hcL hrL (by norm_num) hr0
  have hcrU := nonnegative_product_upper
    c r (1433 / 200000) (57183 / 1000000)
    hcU hrU (by norm_num) hr0
  have hdxL := nonnegative_product_lower
    d x (23317 / 1000000) (37851 / 1000000)
    hdL hxL (by norm_num) hx0
  have hdxU := nonnegative_product_upper
    d x (27183 / 1000000) (39761 / 1000000)
    hdU hxU (by norm_num) hx0
  constructor
  · unfold cleanRDetMinusCoefficient
    norm_num [cornerC, cornerR, cornerX] at ⊢
    nlinarith only [hRU, hrL, hxL, hRcL, hcL, hdL, hcrL, hdxL]
  constructor
  · unfold cleanRDetMinusCoefficient
    norm_num [cornerC, cornerR, cornerX] at ⊢
    nlinarith only [hRL, hrU, hxU, hRcU, hcU, hdU, hcrU, hdxU]
  constructor
  · unfold cleanRDetMixedCoefficient
    norm_num [cornerC, cornerR, cornerX] at ⊢
    nlinarith only [hRL, hrL, hxL, hRcL, hcL, hdL, hcrU, hdxU]
  · unfold cleanRDetPlusCoefficient
    norm_num [cornerC, cornerR, cornerX] at ⊢
    nlinarith only [hRL, hrL, hxL, hRcL, hcL, hdL, hcrL, hdxL]

private theorem cleanR_bilinear_bounds
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (285 / 100000 : ℝ) ≤ cleanRBilinear R su du sv v4 ∧
      (110 / 100000 : ℝ) ≤ perturbRBilinear x r c d su du sv v4 ∧
      perturbRBilinear x r c d su du sv v4 ≤ (146 / 100000 : ℝ) := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  norm_num at hRL hRU hxL hxU hrL hrU hcL hcU hdL hdU hsuL hsuU hduL hduU hsvL hsvU hv4L hv4U
  have hR0 : 0 ≤ R := by linarith only [hRL]
  have hx0 : 0 ≤ x := by linarith only [hxL]
  have hr0 : 0 ≤ r := by linarith only [hrL]
  have hc0 : 0 ≤ c := by linarith only [hcL]
  have hd0 : 0 ≤ d := by linarith only [hdL]
  have hsu0 : 0 ≤ su := by linarith only [hsuL]
  have hdu0 : 0 ≤ du := by linarith only [hduL]
  have hsv0 : 0 ≤ sv := by linarith only [hsvL]
  have htL : (2 / 1000 : ℝ) ≤ -v4 := by linarith only [hv4U]
  have htU : -v4 ≤ (4 / 1000 : ℝ) := by linarith only [hv4L]
  have ht0 : 0 ≤ -v4 := by linarith only [htL]
  have hsuTL := nonnegative_product_lower
    su (-v4) (7021 / 12500) (2 / 1000)
    hsuL htL (by norm_num) ht0
  have hsuTU := nonnegative_product_upper
    su (-v4) (56173 / 100000) (4 / 1000)
    hsuU htU (by norm_num) ht0
  have hduTL := nonnegative_product_lower
    du (-v4) (1687 / 100000) (2 / 1000)
    hduL htL (by norm_num) ht0
  have hduTU := nonnegative_product_upper
    du (-v4) (423 / 25000) (4 / 1000)
    hduU htU (by norm_num) ht0
  have hduSvL := nonnegative_product_lower
    du sv (1687 / 100000) (10763 / 20000)
    hduL hsvL (by norm_num) hsv0
  have hduSvU := nonnegative_product_upper
    du sv (423 / 25000) (13459 / 25000)
    hduU hsvU (by norm_num) hsv0
  let g1 : ℝ := sv * cornerU4 - su * (-v4)
  let g2 : ℝ := du * sv + cornerDv * su
  let g4 : ℝ := cornerDv * cornerU4 - du * (-v4)
  let duV : ℝ := du * cornerDv
  have hg1L : (7524 / 100000 : ℝ) ≤ g1 := by
    dsimp only [g1]
    norm_num [cornerU4] at ⊢
    nlinarith only [hsvL, hsuTU]
  have hg1U : g1 ≤ (7641 / 100000 : ℝ) := by
    dsimp only [g1]
    norm_num [cornerU4] at ⊢
    nlinarith only [hsvU, hsuTL]
  have hg2L : (4042 / 100000 : ℝ) ≤ g2 := by
    dsimp only [g2]
    norm_num [cornerDv] at ⊢
    nlinarith only [hduSvL, hsuL]
  have hg2U : g2 ≤ (4046 / 100000 : ℝ) := by
    dsimp only [g2]
    norm_num [cornerDv] at ⊢
    nlinarith only [hduSvU, hsuU]
  have hg4L : (796 / 100000 : ℝ) ≤ g4 := by
    dsimp only [g4]
    norm_num [cornerDv, cornerU4] at ⊢
    nlinarith only [hduTU]
  have hg4U : g4 ≤ (8002 / 1000000 : ℝ) := by
    dsimp only [g4]
    norm_num [cornerDv, cornerU4] at ⊢
    nlinarith only [hduTL]
  have hduVL : (941 / 1000000 : ℝ) ≤ duV := by
    dsimp only [duV]
    norm_num [cornerDv] at ⊢
    linarith only [hduL]
  have hduVU : duV ≤ (945 / 1000000 : ℝ) := by
    dsimp only [duV]
    norm_num [cornerDv] at ⊢
    linarith only [hduU]
  have hg10 : 0 ≤ g1 := by linarith only [hg1L]
  have hg20 : 0 ≤ g2 := by linarith only [hg2L]
  have hg40 : 0 ≤ g4 := by linarith only [hg4L]
  have hduV0 : 0 ≤ duV := by linarith only [hduVL]
  have hRplusL : (242817 / 1000000 + cornerR : ℝ) ≤ R + cornerR := by
    linarith only [hRL]
  have hRplus0 : 0 ≤ R + cornerR := by
    norm_num [cornerR] at ⊢
    linarith only [hRL]
  have hRduVL := nonnegative_product_lower
    (R + cornerR) duV (242817 / 1000000 + cornerR) (941 / 1000000)
    hRplusL hduVL (by norm_num [cornerR]) hduV0
  have hcg1L := nonnegative_product_lower
    c g1 (5179 / 1000000) (7524 / 100000)
    hcL hg1L (by norm_num) hg10
  have hcg1U := nonnegative_product_upper
    c g1 (1433 / 200000) (7641 / 100000)
    hcU hg1U (by norm_num) hg10
  have hdg2L := nonnegative_product_lower
    d g2 (23317 / 1000000) (4042 / 100000)
    hdL hg2L (by norm_num) hg20
  have hdg2U := nonnegative_product_upper
    d g2 (27183 / 1000000) (4046 / 100000)
    hdU hg2U (by norm_num) hg20
  have hrduVL := nonnegative_product_lower
    r duV (49817 / 1000000) (941 / 1000000)
    hrL hduVL (by norm_num) hduV0
  have hrduVU := nonnegative_product_upper
    r duV (57183 / 1000000) (945 / 1000000)
    hrU hduVU (by norm_num) hduV0
  have hxg4L := nonnegative_product_lower
    x g4 (37851 / 1000000) (796 / 100000)
    hxL hg4L (by norm_num) hg40
  have hxg4U := nonnegative_product_upper
    x g4 (39761 / 1000000) (8002 / 1000000)
    hxU hg4U (by norm_num) hg40
  constructor
  · unfold cleanRBilinear
    dsimp only [g1, g2, g4, duV] at *
    ring_nf at ⊢
    norm_num [cornerC, cornerX] at ⊢
    nlinarith only [hg1L, hg2L, hRduVL, hg4U]
  constructor
  · unfold perturbRBilinear
    dsimp only [g1, g2, g4, duV] at *
    ring_nf at ⊢
    nlinarith only [hcg1L, hdg2L, hrduVL, hxg4U]
  · unfold perturbRBilinear
    dsimp only [g1, g2, g4, duV] at *
    ring_nf at ⊢
    nlinarith only [hcg1U, hdg2U, hrduVU, hxg4L]

private theorem cleanR_quadratic_and_cross_bounds
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    cleanRUQuadratic R su du ≤ (291 / 100000 : ℝ) ∧
      cleanRVQuadratic R sv v4 ≤ (408 / 100000 : ℝ) ∧
      perturbRUQuadratic x r c d su du ≤ (153 / 100000 : ℝ) ∧
      perturbRVQuadratic x r c d sv v4 ≤ (2 / 1000 : ℝ) ∧
      (79 / 10000 : ℝ) ≤ cornerU4 * cornerDv - v4 * du ∧
      (11 / 1000 : ℝ) ≤ (su * cornerDv - du * sv) / 2 := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  norm_num at hRL hRU hxL hxU hrL hrU hcL hcU hdL hdU hsuL hsuU hduL hduU hsvL hsvU hv4L hv4U
  have hR0 : 0 ≤ R := by linarith only [hRL]
  have hx0 : 0 ≤ x := by linarith only [hxL]
  have hr0 : 0 ≤ r := by linarith only [hrL]
  have hc0 : 0 ≤ c := by linarith only [hcL]
  have hd0 : 0 ≤ d := by linarith only [hdL]
  have hsu0 : 0 ≤ su := by linarith only [hsuL]
  have hdu0 : 0 ≤ du := by linarith only [hduL]
  have hsv0 : 0 ≤ sv := by linarith only [hsvL]
  have htL : (2 / 1000 : ℝ) ≤ -v4 := by linarith only [hv4U]
  have htU : -v4 ≤ (4 / 1000 : ℝ) := by linarith only [hv4L]
  have ht0 : 0 ≤ -v4 := by linarith only [htL]
  have hRplusU : R + cornerR ≤ (242898 / 1000000 + cornerR : ℝ) := by
    linarith only [hRU]
  have hRplus0 : 0 ≤ R + cornerR := by
    norm_num [cornerR] at ⊢
    linarith only [hRL]
  have hduSuU := nonnegative_product_upper
    du su (423 / 25000) (56173 / 100000)
    hduU hsuU (by norm_num) hsu0
  have hRdu2U := nonnegative_triple_upper
    (R + cornerR) du du
    (242898 / 1000000 + cornerR) (423 / 25000) (423 / 25000)
    hRplusU hduU hduU (by norm_num [cornerR]) (by norm_num) hdu0 hdu0
  have hsuTL := nonnegative_product_lower
    su (-v4) (7021 / 12500) (2 / 1000)
    hsuL htL (by norm_num) ht0
  have hsvTL := nonnegative_product_lower
    sv (-v4) (10763 / 20000) (2 / 1000)
    hsvL htL (by norm_num) ht0
  have hduTL := nonnegative_product_lower
    du (-v4) (1687 / 100000) (2 / 1000)
    hduL htL (by norm_num) ht0
  have hcsuU := nonnegative_product_upper
    c su (1433 / 200000) (56173 / 100000)
    hcU hsuU (by norm_num) hsu0
  have hdDuSuU := nonnegative_triple_upper
    d du su (27183 / 1000000) (423 / 25000) (56173 / 100000)
    hdU hduU hsuU (by norm_num) (by norm_num) hdu0 hsu0
  have hrDu2U := nonnegative_triple_upper
    r du du (57183 / 1000000) (423 / 25000) (423 / 25000)
    hrU hduU hduU (by norm_num) (by norm_num) hdu0 hdu0
  have hxduL := nonnegative_product_lower
    x du (37851 / 1000000) (1687 / 100000)
    hxL hduL (by norm_num) hdu0
  have hcSvTL := nonnegative_triple_lower
    c sv (-v4) (5179 / 1000000) (10763 / 20000) (2 / 1000)
    hcL hsvL htL (by norm_num) (by norm_num) hsv0 ht0
  have hdsvU := nonnegative_product_upper
    d sv (27183 / 1000000) (13459 / 25000)
    hdU hsvU (by norm_num) hsv0
  have hxtU := nonnegative_product_upper
    x (-v4) (39761 / 1000000) (4 / 1000)
    hxU htU (by norm_num) ht0
  have hduSvU := nonnegative_product_upper
    du sv (423 / 25000) (13459 / 25000)
    hduU hsvU (by norm_num) hsv0
  constructor
  · unfold cleanRUQuadratic
    norm_num [cornerC, cornerR, cornerX, cornerU4] at ⊢
    nlinarith only [hsuU, hduSuU, hRdu2U, hduL]
  constructor
  · unfold cleanRVQuadratic
    norm_num [cornerC, cornerR, cornerX, cornerDv] at ⊢
    nlinarith only [hsvTL, hsvU, hRU, htU]
  constructor
  · unfold perturbRUQuadratic
    norm_num [cornerU4] at ⊢
    nlinarith only [hcsuU, hdDuSuU, hrDu2U, hxduL]
  constructor
  · unfold perturbRVQuadratic
    norm_num [cornerDv] at ⊢
    nlinarith only [hcSvTL, hdsvU, hrU, hxtU]
  constructor
  · norm_num [cornerU4, cornerDv] at ⊢
    nlinarith only [hduTL]
  · norm_num [cornerDv] at ⊢
    nlinarith only [hsuL, hduSvU]

private theorem cleanR_corner_odd_bounds
    (h33 : ℝ)
    (hh33L : (-120 / 1000 : ℝ) ≤ h33)
    (hh33U : h33 ≤ (-117 / 1000 : ℝ)) :
    (296 / 10000 : ℝ) ≤
        (cornerQ11 - cornerH11) * (cornerQ33 - h33) -
          (cornerQ13 - cornerH13) ^ 2 ∧
      (411 / 10000 : ℝ) ≤
        (cornerQ11 + cornerH11) * (cornerQ33 - h33) +
          (cornerQ11 - cornerH11) * (cornerQ33 + h33) -
            2 * (cornerQ13 + cornerH13) * (cornerQ13 - cornerH13) ∧
      (4 / 1000 : ℝ) ≤
        (cornerQ11 + cornerH11) * (cornerQ33 + h33) -
          (cornerQ13 + cornerH13) ^ 2 := by
  norm_num [cornerQ11, cornerQ13, cornerQ33, cornerH11, cornerH13] at ⊢
  constructor
  · linarith only [hh33U]
  constructor
  · linarith only [hh33L, hh33U]
  · linarith only [hh33L]

set_option maxHeartbeats 5000000 in
theorem cleanRSlopeU4_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (1 / 1000 : ℝ) ≤ cleanRSlopeU4
    R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 := by
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at hxL hxU hcL hcU hsuL hsuU hduL hduU hsvL hsvU hdvL hdvU hh13L hh13U hh33L hh33U
  have hx0 : 0 ≤ x := by linarith only [hxL]
  have hc0 : 0 ≤ c := by linarith only [hcL]
  have hsu0 : 0 ≤ su := by linarith only [hsuL]
  have hdu0 : 0 ≤ du := by linarith only [hduL]
  have hsv0 : 0 ≤ sv := by linarith only [hsvL]
  have hdv0 : 0 ≤ dv := by linarith only [hdvL]
  let bU : ℝ := cornerC * su - cornerX * du
  let bV : ℝ := cornerC * sv - cornerX * dv
  let pU : ℝ := c * su - x * du
  let pV : ℝ := c * sv - x * dv
  let z : ℝ := (du * sv - su * dv) / 2
  have hbUL : (675 / 100000 : ℝ) ≤ bU := by
    dsimp only [bU]
    norm_num [cornerC, cornerX] at ⊢
    nlinarith only [hsuL, hduU]
  have hbVL : 0 ≤ bV := by
    dsimp only [bV]
    norm_num [cornerC, cornerX] at ⊢
    nlinarith only [hsvL, hdvU]
  have hbVU : bV ≤ (492 / 100000 : ℝ) := by
    dsimp only [bV]
    norm_num [cornerC, cornerX] at ⊢
    nlinarith only [hsvU, hdvL]
  have hcsuL := nonnegative_product_lower
    c su (5179 / 1000000) (7021 / 12500)
    hcL hsuL (by norm_num) hsu0
  have hxduU := nonnegative_product_upper
    x du (39761 / 1000000) (423 / 25000)
    hxU hduU (by norm_num) hdu0
  have hpUL : (22 / 10000 : ℝ) ≤ pU := by
    dsimp only [pU]
    nlinarith only [hcsuL, hxduU]
  have hcsvL := nonnegative_product_lower
    c sv (5179 / 1000000) (10763 / 20000)
    hcL hsvL (by norm_num) hsv0
  have hcsvU := nonnegative_product_upper
    c sv (1433 / 200000) (13459 / 25000)
    hcU hsvU (by norm_num) hsv0
  have hxdvL := nonnegative_product_lower
    x dv (37851 / 1000000) (111 / 2000)
    hxL hdvL (by norm_num) hdv0
  have hxdvU := nonnegative_product_upper
    x dv (39761 / 1000000) (279 / 5000)
    hxU hdvU (by norm_num) hdv0
  have hpVL : 0 ≤ pV := by
    dsimp only [pV]
    nlinarith only [hcsvL, hxdvU]
  have hpVU : pV ≤ (176 / 100000 : ℝ) := by
    dsimp only [pV]
    nlinarith only [hcsvU, hxdvL]
  have hduSvL := nonnegative_product_lower
    du sv (1687 / 100000) (10763 / 20000)
    hduL hsvL (by norm_num) hsv0
  have hsuDvU := nonnegative_product_upper
    su dv (56173 / 100000) (279 / 5000)
    hsuU hdvU (by norm_num) hdv0
  have hzL : (-112 / 10000 : ℝ) ≤ z := by
    dsimp only [z]
    nlinarith only [hduSvL, hsuDvU]
  have hw1L : (1111 / 1000 : ℝ) ≤ 3 * cornerQ33 - h33 := by
    norm_num [cornerQ33] at ⊢
    linarith only [hh33U]
  have hw2U : 3 * cornerQ13 - h13 ≤ (612 / 1000 : ℝ) := by
    norm_num [cornerQ13] at ⊢
    linarith only [hh13L]
  have hw2Nonneg : 0 ≤ 3 * cornerQ13 - h13 := by
    norm_num [cornerQ13] at ⊢
    linarith only [hh13U]
  have hw3L : (211 / 1000 : ℝ) ≤ cornerQ33 + h33 := by
    norm_num [cornerQ33] at ⊢
    linarith only [hh33L]
  have hw4U : cornerQ13 + h13 ≤ (192 / 1000 : ℝ) := by
    norm_num [cornerQ13] at ⊢
    linarith only [hh13U]
  have hw4Nonneg : 0 ≤ cornerQ13 + h13 := by
    norm_num [cornerQ13] at ⊢
    linarith only [hh13L]
  have ht1 := nonnegative_product_lower
    (3 * cornerQ33 - h33) bU (1111 / 1000) (675 / 100000)
    hw1L hbUL (by norm_num) (by linarith only [hbUL])
  have ht2 := nonnegative_product_upper
    (3 * cornerQ13 - h13) bV (612 / 1000) (492 / 100000)
    hw2U hbVU (by norm_num) hbVL
  have ht3 := nonnegative_product_lower
    (cornerQ33 + h33) pU (211 / 1000) (22 / 10000)
    hw3L hpUL (by norm_num) (by linarith only [hpUL])
  have ht4 := nonnegative_product_upper
    (cornerQ13 + h13) pV (192 / 1000) (176 / 100000)
    hw4U hpVU (by norm_num) hpVL
  have htz := positive_negative_product_lower
    dv z (279 / 5000) (-112 / 10000)
    hdv0 hzL (by norm_num) hdvU
  have hsplit :
      cleanRSlopeU4 R C D F a x r c d f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33 =
        ((3 * cornerQ33 - h33) * bU -
            (3 * cornerQ13 - h13) * bV +
            (cornerQ33 + h33) * pU -
            (cornerQ13 + h13) * pV) / 2 + dv * z := by
    unfold cleanRSlopeU4 cleanRSecant quadraticSecant
      correlatedCoefficientThree alignedDeterminant alignedMixedDeterminant
      alignedAdjugatePair alignedMixedAdjugatePair alignedCrossEnergy
      alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
      alignedEntry24 mixedDeterminantOne
    dsimp only [bU, bV, pU, pV, z]
    simp only [cornerA, cornerX, cornerR, cornerC, cornerU4,
      cornerQ11, cornerQ13, cornerQ33, cornerH11]
    ring
  rw [hsplit]
  nlinarith only [ht1, ht2, ht3, ht4, htz]

set_option maxHeartbeats 5000000 in
theorem cleanRSlopeDv_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (1 / 1000 : ℝ) ≤ cleanRSlopeDv
    R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  norm_num at hRL hRU hxL hxU hrL hrU hdL hdU hsuL hsuU hduL hduU hsvL hsvU hdvL hdvU hv4L hv4U hh13L hh13U
  have hR0 : 0 ≤ R := by linarith only [hRL]
  have hx0 : 0 ≤ x := by linarith only [hxL]
  have hr0 : 0 ≤ r := by linarith only [hrL]
  have hd0 : 0 ≤ d := by linarith only [hdL]
  have hsu0 : 0 ≤ su := by linarith only [hsuL]
  have hdu0 : 0 ≤ du := by linarith only [hduL]
  have hsv0 : 0 ≤ sv := by linarith only [hsvL]
  have hdv0 : 0 ≤ dv := by linarith only [hdvL]
  have htL : (2 / 1000 : ℝ) ≤ -v4 := by linarith only [hv4U]
  have htU : -v4 ≤ (4 / 1000 : ℝ) := by linarith only [hv4L]
  have ht0 : 0 ≤ -v4 := by linarith only [htL]
  have hRplusL : (242817 / 1000000 + cornerR : ℝ) ≤ R + cornerR := by
    linarith only [hRL]
  have hRplusU : R + cornerR ≤ (242898 / 1000000 + cornerR : ℝ) := by
    linarith only [hRU]
  have hRplus0 : 0 ≤ R + cornerR := by
    norm_num [cornerR] at ⊢
    linarith only [hRL]
  have hRduL := nonnegative_product_lower
    (R + cornerR) du (242817 / 1000000 + cornerR) (1687 / 100000)
    hRplusL hduL (by norm_num [cornerR]) hdu0
  have hRduU := nonnegative_product_upper
    (R + cornerR) du (242898 / 1000000 + cornerR) (423 / 25000)
    hRplusU hduU (by norm_num [cornerR]) hdu0
  let vsum : ℝ := dv + cornerDv
  have hvsumL : (1113 / 10000 : ℝ) ≤ vsum := by
    dsimp only [vsum]
    norm_num [cornerDv] at ⊢
    linarith only [hdvL]
  have hvsumU : vsum ≤ (1116 / 10000 : ℝ) := by
    dsimp only [vsum]
    norm_num [cornerDv] at ⊢
    linarith only [hdvU]
  have hvsum0 : 0 ≤ vsum := by linarith only [hvsumL]
  have hRvsumL := nonnegative_product_lower
    (R + cornerR) vsum (242817 / 1000000 + cornerR) (1113 / 10000)
    hRplusL hvsumL (by norm_num [cornerR]) hvsum0
  have hRvsumL' :
      (242817 / 1000000 + cornerR) * (1113 / 10000) ≤
        (R + cornerR) * (dv + cornerDv) := by
    simpa only [vsum] using hRvsumL
  have hdsuL := nonnegative_product_lower
    d su (23317 / 1000000) (7021 / 12500)
    hdL hsuL (by norm_num) hsu0
  have hdsuU := nonnegative_product_upper
    d su (27183 / 1000000) (56173 / 100000)
    hdU hsuU (by norm_num) hsu0
  have hrduL := nonnegative_product_lower
    r du (49817 / 1000000) (1687 / 100000)
    hrL hduL (by norm_num) hdu0
  have hrduU := nonnegative_product_upper
    r du (57183 / 1000000) (423 / 25000)
    hrU hduU (by norm_num) hdu0
  have hdsvL := nonnegative_product_lower
    d sv (23317 / 1000000) (10763 / 20000)
    hdL hsvL (by norm_num) hsv0
  have hxtL := nonnegative_product_lower
    x (-v4) (37851 / 1000000) (2 / 1000)
    hxL htL (by norm_num) ht0
  have hrvsumL := nonnegative_product_lower
    r vsum (49817 / 1000000) (1113 / 10000)
    hrL hvsumL (by norm_num) hvsum0
  have hrvsumL' :
      (49817 / 1000000) * (1113 / 10000) ≤ r * (dv + cornerDv) := by
    simpa only [vsum] using hrvsumL
  have hsuTU := nonnegative_product_upper
    su (-v4) (56173 / 100000) (4 / 1000)
    hsuU htU (by norm_num) ht0
  let bU : ℝ :=
    (42817 / 1000000) * su + (R + cornerR) * du -
      cornerX * cornerU4
  let bV : ℝ :=
    2 * (42817 / 1000000) * sv - 2 * cornerX * v4 +
      (R + cornerR) * vsum
  let pU : ℝ := d * su + 2 * r * du - x * cornerU4
  let pV : ℝ := 2 * d * sv - 2 * x * v4 + 2 * r * vsum
  let gap : ℝ := cornerU4 * sv + v4 * su
  have hbU0 : 0 ≤ bU := by
    dsimp only [bU]
    norm_num [cornerX, cornerU4] at ⊢
    nlinarith only [hsuL, hRduL]
  have hbUU : bU ≤ (267 / 10000 : ℝ) := by
    dsimp only [bU]
    norm_num [cornerX, cornerU4] at ⊢
    nlinarith only [hsuU, hRduU]
  have hbVL : (100 / 1000 : ℝ) ≤ bV := by
    dsimp only [bV, vsum]
    norm_num [cornerX] at ⊢
    nlinarith only [hsvL, htL, hRvsumL']
  have hpU0 : 0 ≤ pU := by
    dsimp only [pU]
    norm_num [cornerU4] at ⊢
    nlinarith only [hdsuL, hrduL, hxU]
  have hpUU : pU ≤ (119 / 10000 : ℝ) := by
    dsimp only [pU]
    norm_num [cornerU4] at ⊢
    nlinarith only [hdsuU, hrduU, hxL]
  have hpVL : (363 / 10000 : ℝ) ≤ pV := by
    dsimp only [pV, vsum]
    nlinarith only [hdsvL, hxtL, hrvsumL']
  have hgapL : (736 / 10000 : ℝ) ≤ gap := by
    dsimp only [gap]
    norm_num [cornerU4] at ⊢
    nlinarith only [hsvL, hsuTU]
  have hw1U : 3 * cornerQ13 - h13 ≤ (612 / 1000 : ℝ) := by
    norm_num [cornerQ13] at ⊢
    linarith only [hh13L]
  have hw3U : cornerQ13 + h13 ≤ (192 / 1000 : ℝ) := by
    norm_num [cornerQ13] at ⊢
    linarith only [hh13U]
  have ht1 := nonnegative_product_upper
    (3 * cornerQ13 - h13) bU (612 / 1000) (267 / 10000)
    hw1U hbUU (by norm_num) hbU0
  have ht2 := nonnegative_product_lower
    (3 * cornerQ11 - cornerH11) bV (519 / 1000) (100 / 1000)
    (by norm_num [cornerQ11, cornerH11]) hbVL (by norm_num)
      (by linarith only [hbVL])
  have ht3 := nonnegative_product_upper
    (cornerQ13 + h13) pU (192 / 1000) (119 / 10000)
    hw3U hpUU (by norm_num) hpU0
  have ht4 := nonnegative_product_lower
    (cornerQ11 + cornerH11) pV (191 / 1000) (363 / 10000)
    (by norm_num [cornerQ11, cornerH11]) hpVL (by norm_num)
      (by linarith only [hpVL])
  have hduGap := nonnegative_product_lower
    du gap (1687 / 100000) (736 / 10000)
    hduL hgapL (by norm_num) (by linarith only [hgapL])
  have hsuVsum := nonnegative_product_upper
    su vsum (56173 / 100000) (1116 / 10000)
    hsuU hvsumU (by norm_num) hvsum0
  have hcross : (-390 / 100000 : ℝ) ≤
      du * gap / 2 - cornerU4 * su * vsum / 2 := by
    norm_num [cornerU4] at ⊢
    nlinarith only [hduGap, hsuVsum]
  have hsplit :
      cleanRSlopeDv R C D F a x r c d f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33 =
        -(3 * cornerQ13 - h13) * bU / 2 +
          (3 * cornerQ11 - cornerH11) * bV / 4 -
          (cornerQ13 + h13) * pU / 2 +
          (cornerQ11 + cornerH11) * pV / 4 +
          (du * gap / 2 - cornerU4 * su * vsum / 2) := by
    unfold cleanRSlopeDv cleanRSecant quadraticSecant
      correlatedCoefficientThree alignedDeterminant alignedMixedDeterminant
      alignedAdjugatePair alignedMixedAdjugatePair alignedCrossEnergy
      alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
      alignedEntry24 mixedDeterminantOne
    dsimp only [bU, bV, pU, pV, gap, vsum]
    simp only [cornerA, cornerX, cornerR, cornerC, cornerU4,
      cornerDv, cornerQ11, cornerQ13, cornerQ33, cornerH11]
    ring
  rw [hsplit]
  nlinarith only [ht1, ht2, ht3, ht4, hcross]

set_option maxHeartbeats 5000000 in
theorem cleanRSlopeH13_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (1 / 1000 : ℝ) ≤ cleanRSlopeH13
    R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 := by
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  norm_num at hh13L hh13U
  rcases cleanR_determinant_coefficient_bounds
      A X R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 hbox with
    ⟨hrmL, hrmU, hrxU, hrpU⟩
  rcases cleanR_bilinear_bounds
      A X R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 hbox with
    ⟨hBuvL, _hPuvL, hPuvU⟩
  let rm : ℝ := cleanRDetMinusCoefficient R x r c d
  let rx : ℝ := cleanRDetMixedCoefficient R x r c d
  let rp : ℝ := cleanRDetPlusCoefficient R x r c d
  let Buv : ℝ := cleanRBilinear R su du sv v4
  let Puv : ℝ := perturbRBilinear x r c d su du sv v4
  have hrmL' : (-458 / 100000 : ℝ) ≤ rm := by
    simpa only [rm] using hrmL
  have hrxMag : (9 / 1000 : ℝ) ≤ -rx := by
    dsimp only [rx]
    linarith only [hrxU]
  have hrpMag : (52 / 10000 : ℝ) ≤ -rp := by
    dsimp only [rp]
    linarith only [hrpU]
  have hBuvL' : (285 / 100000 : ℝ) ≤ Buv := by
    simpa only [Buv] using hBuvL
  have hPuvU' : Puv ≤ (146 / 100000 : ℝ) := by
    simpa only [Puv] using hPuvU
  let alpha : ℝ := 2 * cornerQ13 - h13 - cornerH13
  let beta : ℝ := -2 * (h13 + cornerH13)
  let gamma : ℝ := 2 * cornerQ13 + h13 + cornerH13
  have halpha0 : 0 ≤ alpha := by
    dsimp only [alpha]
    norm_num [cornerQ13, cornerH13] at ⊢
    linarith only [hh13U]
  have halphaU : alpha ≤ (421 / 1000 : ℝ) := by
    dsimp only [alpha]
    norm_num [cornerQ13, cornerH13] at ⊢
    linarith only [hh13L]
  have hbetaL : (36 / 1000 : ℝ) ≤ beta := by
    dsimp only [beta]
    norm_num [cornerH13] at ⊢
    linarith only [hh13U]
  have hgammaL : (380 / 1000 : ℝ) ≤ gamma := by
    dsimp only [gamma]
    norm_num [cornerQ13, cornerH13] at ⊢
    linarith only [hh13L]
  have ht1 := positive_negative_product_lower
    alpha rm (421 / 1000) (-458 / 100000)
    halpha0 hrmL' (by norm_num) halphaU
  have ht2 := nonnegative_product_lower
    (-rx) beta (9 / 1000) (36 / 1000)
    hrxMag hbetaL (by norm_num) (by linarith only [hbetaL])
  have ht3 := nonnegative_product_lower
    (-rp) gamma (52 / 10000) (380 / 1000)
    hrpMag hgammaL (by norm_num) (by linarith only [hgammaL])
  have hsplit :
      cleanRSlopeH13 R C D F a x r c d f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33 =
        rm * alpha + (-rx) * beta + (-rp) * gamma + (Buv - Puv) / 2 := by
    unfold cleanRSlopeH13 cleanRSecant quadraticSecant
      correlatedCoefficientThree alignedDeterminant alignedMixedDeterminant
      alignedAdjugatePair alignedMixedAdjugatePair alignedCrossEnergy
      alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
      alignedEntry24 mixedDeterminantOne
    dsimp only [rm, rx, rp, Buv, Puv, alpha, beta, gamma,
      cleanRDetMinusCoefficient, cleanRDetMixedCoefficient,
      cleanRDetPlusCoefficient, cleanRBilinear, perturbRBilinear]
    simp only [cornerA, cornerX, cornerR, cornerC, cornerU4,
      cornerDv, cornerQ11, cornerQ13, cornerQ33, cornerH11, cornerH13]
    ring
  rw [hsplit]
  nlinarith only [ht1, ht2, ht3, hBuvL', hPuvU']

set_option maxHeartbeats 5000000 in
theorem cleanRSecant_corner_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    cleanRSecant
    R cornerC (42817 / 1000000) F a x r c d f
      su du cornerU4 sv cornerDv v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 h33 ≤
    (-4 / 100000 : ℝ) := by
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at hh33L hh33U
  rcases cleanR_determinant_coefficient_bounds
      A X R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 hbox with
    ⟨_hrmL, hrmU, hrxU, hrpU⟩
  rcases cleanR_bilinear_bounds
      A X R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 hbox with
    ⟨hBuvL, hPuvL, _hPuvU⟩
  rcases cleanR_quadratic_and_cross_bounds
      A X R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 hbox with
    ⟨hBuuU, hBvvU, hPuuU, hPvvU, hzsL, hzgL⟩
  rcases cleanR_corner_odd_bounds h33
      (by norm_num at ⊢; linarith only [hh33L])
      (by norm_num at ⊢; linarith only [hh33U]) with
    ⟨homL, hoxL, hopL⟩
  let rm : ℝ := cleanRDetMinusCoefficient R x r c d
  let rx : ℝ := cleanRDetMixedCoefficient R x r c d
  let rp : ℝ := cleanRDetPlusCoefficient R x r c d
  let om : ℝ :=
    (cornerQ11 - cornerH11) * (cornerQ33 - h33) -
      (cornerQ13 - cornerH13) ^ 2
  let ox : ℝ :=
    (cornerQ11 + cornerH11) * (cornerQ33 - h33) +
      (cornerQ11 - cornerH11) * (cornerQ33 + h33) -
        2 * (cornerQ13 + cornerH13) * (cornerQ13 - cornerH13)
  let op : ℝ :=
    (cornerQ11 + cornerH11) * (cornerQ33 + h33) -
      (cornerQ13 + cornerH13) ^ 2
  let Buu : ℝ := cleanRUQuadratic R su du
  let Buv : ℝ := cleanRBilinear R su du sv v4
  let Bvv : ℝ := cleanRVQuadratic R sv v4
  let Puu : ℝ := perturbRUQuadratic x r c d su du
  let Puv : ℝ := perturbRBilinear x r c d su du sv v4
  let Pvv : ℝ := perturbRVQuadratic x r c d sv v4
  let zs : ℝ := cornerU4 * cornerDv - v4 * du
  let zg : ℝ := (su * cornerDv - du * sv) / 2
  have hrmU' : rm ≤ (-398 / 100000 : ℝ) := by
    simpa only [rm] using hrmU
  have hrxU' : rx ≤ (-9 / 1000 : ℝ) := by
    simpa only [rx] using hrxU
  have hrpU' : rp ≤ (-52 / 10000 : ℝ) := by
    simpa only [rp] using hrpU
  have homL' : (296 / 10000 : ℝ) ≤ om := by simpa only [om] using homL
  have hoxL' : (411 / 10000 : ℝ) ≤ ox := by simpa only [ox] using hoxL
  have hopL' : (4 / 1000 : ℝ) ≤ op := by simpa only [op] using hopL
  have hdetM := positive_negative_product_upper
    om rm (296 / 10000) (-398 / 100000)
    homL' (by linarith only [hrmU']) (by norm_num) hrmU'
  have hdetX := positive_negative_product_upper
    ox rx (411 / 10000) (-9 / 1000)
    hoxL' (by linarith only [hrxU']) (by norm_num) hrxU'
  have hdetP := positive_negative_product_upper
    op rp (4 / 1000) (-52 / 10000)
    hopL' (by linarith only [hrpU']) (by norm_num) hrpU'
  have hdet : rm * om + rx * ox + rp * op ≤ (-508 / 1000000 : ℝ) := by
    nlinarith only [hdetM, hdetX, hdetP]
  have hBuuU' : Buu ≤ (291 / 100000 : ℝ) := by
    simpa only [Buu] using hBuuU
  have hBuvL' : (285 / 100000 : ℝ) ≤ Buv := by
    simpa only [Buv] using hBuvL
  have hBvvU' : Bvv ≤ (408 / 100000 : ℝ) := by
    simpa only [Bvv] using hBvvU
  have hPuuU' : Puu ≤ (153 / 100000 : ℝ) := by
    simpa only [Puu] using hPuuU
  have hPuvL' : (110 / 100000 : ℝ) ≤ Puv := by
    simpa only [Puv] using hPuvL
  have hPvvU' : Pvv ≤ (2 / 1000 : ℝ) := by
    simpa only [Pvv] using hPvvU
  have hw1Nonneg : 0 ≤ 3 * cornerQ33 - h33 := by
    norm_num [cornerQ33] at ⊢
    linarith only [hh33U]
  have hw1U : 3 * cornerQ33 - h33 ≤ (1115 / 1000 : ℝ) := by
    norm_num [cornerQ33] at ⊢
    linarith only [hh33L]
  have hw4Nonneg : 0 ≤ cornerQ33 + h33 := by
    norm_num [cornerQ33] at ⊢
    linarith only [hh33L]
  have hw4U : cornerQ33 + h33 ≤ (215 / 1000 : ℝ) := by
    norm_num [cornerQ33] at ⊢
    linarith only [hh33U]
  have hc1 := product_upper_of_nonnegative_left
    (3 * cornerQ33 - h33) Buu (1115 / 1000) (291 / 100000)
    hw1Nonneg hw1U hBuuU' (by norm_num)
  have hc2 := nonnegative_product_lower
    (2 * (3 * cornerQ13 - cornerH13)) Buv
    (1219 / 1000) (285 / 100000)
    (by norm_num [cornerQ13, cornerH13]) hBuvL' (by norm_num)
      (by linarith only [hBuvL'])
  have hc3 := product_upper_of_nonnegative_left
    (3 * cornerQ11 - cornerH11) Bvv
    (5194 / 10000) (408 / 100000)
    (by norm_num [cornerQ11, cornerH11])
    (by norm_num [cornerQ11, cornerH11]) hBvvU' (by norm_num)
  have hc4 := product_upper_of_nonnegative_left
    (cornerQ33 + h33) Puu (215 / 1000) (153 / 100000)
    hw4Nonneg hw4U hPuuU' (by norm_num)
  have hc5 := nonnegative_product_lower
    (2 * (cornerQ13 + cornerH13)) Puv
    (382 / 1000) (110 / 100000)
    (by norm_num [cornerQ13, cornerH13]) hPuvL' (by norm_num)
      (by linarith only [hPuvL'])
  have hc6 := product_upper_of_nonnegative_left
    (cornerQ11 + cornerH11) Pvv
    (1918 / 10000) (2 / 1000)
    (by norm_num [cornerQ11, cornerH11])
    (by norm_num [cornerQ11, cornerH11]) hPvvU' (by norm_num)
  have hcoupling :
      ((3 * cornerQ33 - h33) * Buu -
          2 * (3 * cornerQ13 - cornerH13) * Buv +
          (3 * cornerQ11 - cornerH11) * Bvv +
          (cornerQ33 + h33) * Puu -
          2 * (cornerQ13 + cornerH13) * Puv +
          (cornerQ11 + cornerH11) * Pvv) / 4 ≤
        (546 / 1000000 : ℝ) := by
    nlinarith only [hc1, hc2, hc3, hc4, hc5, hc6]
  have hzsL' : (79 / 10000 : ℝ) ≤ zs := by simpa only [zs] using hzsL
  have hzgL' : (11 / 1000 : ℝ) ≤ zg := by simpa only [zg] using hzgL
  have hcrossProd := nonnegative_product_lower
    zs zg (79 / 10000) (11 / 1000)
    hzsL' hzgL' (by norm_num) (by linarith only [hzgL'])
  have hsplit :
      cleanRSecant R cornerC (42817 / 1000000) F a x r c d f
          su du cornerU4 sv cornerDv v4
            cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 h33 =
        rm * om + rx * ox + rp * op +
          ((3 * cornerQ33 - h33) * Buu -
            2 * (3 * cornerQ13 - cornerH13) * Buv +
            (3 * cornerQ11 - cornerH11) * Bvv +
            (cornerQ33 + h33) * Puu -
            2 * (cornerQ13 + cornerH13) * Puv +
            (cornerQ11 + cornerH11) * Pvv) / 4 - zs * zg := by
    unfold cleanRSecant quadraticSecant correlatedCoefficientThree
      alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
      alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00 alignedEntry02
      alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only [rm, rx, rp, om, ox, op, Buu, Buv, Bvv, Puu, Puv, Pvv,
      zs, zg, cleanRDetMinusCoefficient, cleanRDetMixedCoefficient,
      cleanRDetPlusCoefficient, cleanRUQuadratic, cleanRBilinear,
      cleanRVQuadratic, perturbRUQuadratic, perturbRBilinear,
      perturbRVQuadratic]
    simp only [cornerA, cornerX, cornerR, cornerC, cornerU4,
      cornerDv, cornerQ11, cornerQ13, cornerQ33, cornerH11, cornerH13]
    ring
  rw [hsplit]
  nlinarith only [hdet, hcoupling, hcrossProd]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3Structural
