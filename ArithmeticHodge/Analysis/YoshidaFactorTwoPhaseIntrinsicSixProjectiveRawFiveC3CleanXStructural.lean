import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3CleanFDCStructural

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
# Structural clean-X endpoint step for the third raw five-mode coefficient

The three X-secant blocks are bounded through signed products of correlated
coordinates.  In particular, the cross block remains one product of two
oriented gaps rather than an expanded interval polynomial.
-/

private theorem oddCouplingCross_nonnegative_upper
    (u z v w o11 o13 o33
      uL uU zL zU vL vU wL wU
      o11L o11U o13L o13U o33L o33U : ℝ)
    (huL : uL ≤ u) (huU : u ≤ uU)
    (hzL : zL ≤ z) (hzU : z ≤ zU)
    (hvL : vL ≤ v) (hvU : v ≤ vU)
    (hwL : wL ≤ w) (hwU : w ≤ wU)
    (ho11L : o11L ≤ o11) (ho11U : o11 ≤ o11U)
    (ho13L : o13L ≤ o13) (ho13U : o13 ≤ o13U)
    (ho33L : o33L ≤ o33) (ho33U : o33 ≤ o33U)
    (huL0 : 0 ≤ uL) (hzL0 : 0 ≤ zL)
    (hvL0 : 0 ≤ vL) (hwL0 : 0 ≤ wL)
    (ho11L0 : 0 ≤ o11L) (ho13L0 : 0 ≤ o13L)
    (ho33L0 : 0 ≤ o33L) :
    oddCouplingCross u z v w o11 o13 o33 ≤
      o33U * uU * zU - o13L * (uL * wL + zL * vL) +
        o11U * vU * wU := by
  have hu0 : 0 ≤ u := le_trans huL0 huL
  have hz0 : 0 ≤ z := le_trans hzL0 hzL
  have hv0 : 0 ≤ v := le_trans hvL0 hvL
  have hw0 : 0 ≤ w := le_trans hwL0 hwL
  have huU0 : 0 ≤ uU := le_trans hu0 huU
  have hzU0 : 0 ≤ zU := le_trans hz0 hzU
  have hvU0 : 0 ≤ vU := le_trans hv0 hvU
  have hwU0 : 0 ≤ wU := le_trans hw0 hwU
  have ho11U0 : 0 ≤ o11U := le_trans (le_trans ho11L0 ho11L) ho11U
  have ho33U0 : 0 ≤ o33U := le_trans (le_trans ho33L0 ho33L) ho33U
  have h33 := nonnegative_triple_upper
    o33 u z o33U uU zU ho33U huU hzU ho33U0 huU0 hu0 hz0
  have h13uw := nonnegative_triple_lower
    o13 u w o13L uL wL ho13L huL hwL ho13L0 huL0
      (le_trans huL0 huL) hw0
  have h13zv := nonnegative_triple_lower
    o13 z v o13L zL vL ho13L hzL hvL ho13L0 hzL0
      (le_trans hzL0 hzL) hv0
  have h11 := nonnegative_triple_upper
    o11 v w o11U vU wU ho11U hvU hwU ho11U0 hvU0 hv0 hw0
  unfold oddCouplingCross
  nlinarith only [h33, h13uw, h13zv, h11]

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
  have huU0 : 0 ≤ uU := le_trans hu0 huU
  have hzU0 : 0 ≤ zU := le_trans hz0 hzU
  have hvU0 : 0 ≤ vU := le_trans hv0 hvU
  have htU0 : 0 ≤ tU := le_trans ht0 htU
  have ho11U0 : 0 ≤ o11U := le_trans (le_trans ho11L0 ho11L) ho11U
  have ho13U0 : 0 ≤ o13U := le_trans (le_trans ho13L0 ho13L) ho13U
  have ho33U0 : 0 ≤ o33U := le_trans (le_trans ho33L0 ho33L) ho33U
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

private theorem cleanX_cross_gap_bounds
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (77 / 1000 : ℝ) ≤ u4 * sv - v4 * su ∧
      (78 / 10000 : ℝ) ≤ u4 * dv - v4 * du := by
  rcases hbox.su_mem with ⟨hsuL, _⟩
  rcases hbox.du_mem with ⟨hduL, _⟩
  rcases hbox.u4_mem with ⟨hu4L, _⟩
  rcases hbox.sv_mem with ⟨hsvL, _⟩
  rcases hbox.dv_mem with ⟨hdvL, _⟩
  rcases hbox.v4_mem with ⟨_, hv4U⟩
  have hsu0 : 0 ≤ su := by linarith only [hsuL]
  have hdu0 : 0 ≤ du := by linarith only [hduL]
  have hsv0 : 0 ≤ sv := by linarith only [hsvL]
  have hdv0 : 0 ≤ dv := by linarith only [hdvL]
  have hnv4L : (1 / 500 : ℝ) ≤ -v4 := by linarith only [hv4U]
  have hu4svL := nonnegative_product_lower
    u4 sv (141 / 1000) (53815 / 100000)
    hu4L hsvL (by norm_num) hsv0
  have hnv4suL := nonnegative_product_lower
    (-v4) su (1 / 500) (56168 / 100000)
    hnv4L hsuL (by norm_num) hsu0
  have hu4dvL := nonnegative_product_lower
    u4 dv (141 / 1000) (555 / 10000)
    hu4L hdvL (by norm_num) hdv0
  have hnv4duL := nonnegative_product_lower
    (-v4) du (1 / 500) (1687 / 100000)
    hnv4L hduL (by norm_num) hdu0
  constructor <;>
    nlinarith only [hu4svL, hnv4suL, hu4dvL, hnv4duL]

private def cleanXDetMinusCoefficient
    (X R D F x r d f : ℝ) : ℝ :=
  -3 * D * R / 2 + D * r / 2 - 3 * F * X / 4 -
    3 * F * cornerX / 4 + F * x / 2 + R * d / 2 + X * f / 4 +
      cornerX * f / 4 + d * r / 2 + f * x / 2

private def cleanXDetMixedCoefficient
    (X R D F x r d f : ℝ) : ℝ :=
  -3 * D * R / 2 - D * r / 2 - 3 * F * X / 4 -
    3 * F * cornerX / 4 - F * x / 2 - R * d / 2 - X * f / 4 -
      cornerX * f / 4 + d * r / 2 + f * x / 2

private def cleanXDetPlusCoefficient
    (X R D F x r d f : ℝ) : ℝ :=
  -(D * R / 2 + D * r / 2 + F * X / 4 + F * cornerX / 4 +
    F * x / 2 + R * d / 2 + X * f / 4 + cornerX * f / 4 +
      d * r / 2 + f * x / 2)

private theorem cleanX_determinant_coefficient_bounds
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    cleanXDetMinusCoefficient X R D F x r d f ≤ (-15 / 1000 : ℝ) ∧
      cleanXDetMixedCoefficient X R D F x r d f ≤ (-43 / 1000 : ℝ) ∧
        cleanXDetPlusCoefficient X R D F x r d f ≤ (-28 / 1000 : ℝ) := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  norm_num at hXL hXU hRL hRU hDL hDU hFL hFU hxL hxU hrL hrU hdL hdU hfL hfU
  have hX0 : 0 ≤ X := by linarith only [hXL]
  have hR0 : 0 ≤ R := by linarith only [hRL]
  have hD0 : 0 ≤ D := by linarith only [hDL]
  have hF0 : 0 ≤ F := by linarith only [hFL]
  have hx0 : 0 ≤ x := by linarith only [hxL]
  have hr0 : 0 ≤ r := by linarith only [hrL]
  have hd0 : 0 ≤ d := by linarith only [hdL]
  have hf0 : 0 ≤ f := by linarith only [hfL]
  have hDRL := nonnegative_product_lower
    D R (42817 / 1000000) (242817 / 1000000)
    hDL hRL (by norm_num) hR0
  have hDrL := nonnegative_product_lower
    D r (42817 / 1000000) (49817 / 1000000)
    hDL hrL (by norm_num) hr0
  have hDrU := nonnegative_product_upper
    D r (21449 / 500000) (57183 / 1000000)
    hDU hrU (by norm_num) hr0
  have hFXL := nonnegative_product_lower
    F X (1571 / 5000) (1981 / 50000)
    hFL hXL (by norm_num) hX0
  have hFxL := nonnegative_product_lower
    F x (1571 / 5000) (37851 / 1000000)
    hFL hxL (by norm_num) hx0
  have hFxU := nonnegative_product_upper
    F x (63 / 200) (39761 / 1000000)
    hFU hxU (by norm_num) hx0
  have hRdL := nonnegative_product_lower
    R d (242817 / 1000000) (23317 / 1000000)
    hRL hdL (by norm_num) hd0
  have hRdU := nonnegative_product_upper
    R d (121449 / 500000) (27183 / 1000000)
    hRU hdU (by norm_num) hd0
  have hXfL := nonnegative_product_lower
    X f (1981 / 50000) (4411 / 25000)
    hXL hfL (by norm_num) hf0
  have hXfU := nonnegative_product_upper
    X f (3977 / 100000) (552 / 3125)
    hXU hfU (by norm_num) hf0
  have hdrL := nonnegative_product_lower
    d r (23317 / 1000000) (49817 / 1000000)
    hdL hrL (by norm_num) hr0
  have hdrU := nonnegative_product_upper
    d r (27183 / 1000000) (57183 / 1000000)
    hdU hrU (by norm_num) hr0
  have hfxL := nonnegative_product_lower
    f x (4411 / 25000) (37851 / 1000000)
    hfL hxL (by norm_num) hx0
  have hfxU := nonnegative_product_upper
    f x (552 / 3125) (39761 / 1000000)
    hfU hxU (by norm_num) hx0
  constructor
  · unfold cleanXDetMinusCoefficient
    norm_num [cornerX] at ⊢
    nlinarith only [hDRL, hDrU, hFXL, hFL, hFxU, hRdU, hXfU,
      hfU, hdrU, hfxU]
  constructor
  · unfold cleanXDetMixedCoefficient
    norm_num [cornerX] at ⊢
    nlinarith only [hDRL, hDrL, hFXL, hFL, hFxL, hRdL, hXfL,
      hfL, hdrU, hfxU]
  · unfold cleanXDetPlusCoefficient
    norm_num [cornerX] at ⊢
    nlinarith only [hDRL, hDrL, hFXL, hFL, hFxL, hRdL, hXfL,
      hfL, hdrL, hfxL]

private theorem cleanX_coupling_form_bounds
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddCouplingCross su u4 sv v4
        (q11 + h11) (q13 + h13) (q33 + h33) ≤ (3355 / 1000000 : ℝ) ∧
      oddCouplingCross du su dv sv
        (q11 + h11) (q13 + h13) (q33 + h33) ≤ (424 / 1000000 : ℝ) ∧
      (-1072 / 1000000 : ℝ) ≤ oddCouplingCross du u4 dv v4
        (q11 + h11) (q13 + h13) (q33 + h33) ∧
      oddCouplingFour u4 v4
        (q11 + h11) (q13 + h13) (q33 + h33) ≤ (4703 / 1000000 : ℝ) ∧
      oddCouplingCross su u4 sv v4
        (q11 - h11) (q13 - h13) (q33 - h33) ≤ (2109 / 100000 : ℝ) ∧
      oddCouplingCross du su dv sv
        (q11 - h11) (q13 - h13) (q33 - h33) ≤ (850 / 1000000 : ℝ) ∧
      (-660 / 1000000 : ℝ) ≤ oddCouplingCross du u4 dv v4
        (q11 - h11) (q13 - h13) (q33 - h33) ∧
      oddCouplingFour u4 v4
        (q11 - h11) (q13 - h13) (q33 - h33) ≤ (964 / 100000 : ℝ) := by
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
  norm_num at hsuL hsuU hduL hduU hu4L hu4U hsvL hsvU hdvL hdvU hv4L hv4U hq11L hq11U hq13L hq13U hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
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
  have hSDp := oddCouplingCross_nonnegative_upper
    du su dv sv p11 p13 p33
    (1687 / 100000) (423 / 25000)
    (7021 / 12500) (56173 / 100000)
    (111 / 2000) (279 / 5000)
    (10763 / 20000) (13459 / 25000)
    (1918 / 10000) (199 / 1000)
    (189 / 1000) (1912 / 10000)
    (2115 / 10000) (216 / 1000)
    hduL hduU hsuL hsuU hdvL hdvU hsvL hsvU
    hp11L hp11U hp13L hp13U hp33L hp33U
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hSDm := oddCouplingCross_nonnegative_upper
    du su dv sv m11 m13 m33
    (1687 / 100000) (423 / 25000)
    (7021 / 12500) (56173 / 100000)
    (111 / 2000) (279 / 5000)
    (10763 / 20000) (13459 / 25000)
    (1578 / 10000) (165 / 1000)
    (209 / 1000) (2112 / 10000)
    (4485 / 10000) (453 / 1000)
    hduL hduU hsuL hsuU hdvL hdvU hsvL hsvU
    hm11L hm11U hm13L hm13U hm33L hm33U
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hS4p := oddCouplingCross_negative_four_bounds
    su u4 sv v4 p11 p13 p33
    (7021 / 12500) (56173 / 100000)
    (141 / 1000) (18 / 125)
    (10763 / 20000) (13459 / 25000)
    (1 / 500) (1 / 250)
    (1918 / 10000) (199 / 1000)
    (189 / 1000) (1912 / 10000)
    (2115 / 10000) (216 / 1000)
    hsuL hsuU hu4L hu4U hsvL hsvU htL htU
    hp11L hp11U hp13L hp13U hp33L hp33U
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hD4p := oddCouplingCross_negative_four_bounds
    du u4 dv v4 p11 p13 p33
    (1687 / 100000) (423 / 25000)
    (141 / 1000) (18 / 125)
    (111 / 2000) (279 / 5000)
    (1 / 500) (1 / 250)
    (1918 / 10000) (199 / 1000)
    (189 / 1000) (1912 / 10000)
    (2115 / 10000) (216 / 1000)
    hduL hduU hu4L hu4U hdvL hdvU htL htU
    hp11L hp11U hp13L hp13U hp33L hp33U
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hS4m := oddCouplingCross_negative_four_bounds
    su u4 sv v4 m11 m13 m33
    (7021 / 12500) (56173 / 100000)
    (141 / 1000) (18 / 125)
    (10763 / 20000) (13459 / 25000)
    (1 / 500) (1 / 250)
    (1578 / 10000) (165 / 1000)
    (209 / 1000) (2112 / 10000)
    (4485 / 10000) (453 / 1000)
    hsuL hsuU hu4L hu4U hsvL hsvU htL htU
    hm11L hm11U hm13L hm13U hm33L hm33U
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hD4m := oddCouplingCross_negative_four_bounds
    du u4 dv v4 m11 m13 m33
    (1687 / 100000) (423 / 25000)
    (141 / 1000) (18 / 125)
    (111 / 2000) (279 / 5000)
    (1 / 500) (1 / 250)
    (1578 / 10000) (165 / 1000)
    (209 / 1000) (2112 / 10000)
    (4485 / 10000) (453 / 1000)
    hduL hduU hu4L hu4U hdvL hdvU htL htU
    hm11L hm11U hm13L hm13U hm33L hm33U
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hW4p := oddCouplingFour_negative_upper
    u4 v4 p11 p13 p33 (18 / 125) (1 / 250)
    (199 / 1000) (1912 / 10000) (216 / 1000)
    hu4U htU hp11U hp13U hp33U
    (by linarith only [hu4L]) (by linarith only [htL])
    (by linarith only [hp11L]) (by linarith only [hp13L])
    (by linarith only [hp33L])
  have hW4m := oddCouplingFour_negative_upper
    u4 v4 m11 m13 m33 (18 / 125) (1 / 250)
    (165 / 1000) (2112 / 10000) (453 / 1000)
    hu4U htU hm11U hm13U hm33U
    (by linarith only [hu4L]) (by linarith only [htL])
    (by linarith only [hm11L]) (by linarith only [hm13L])
    (by linarith only [hm33L])
  have hS4pU : oddCouplingCross su u4 sv v4 p11 p13 p33 ≤
      (3355 / 1000000 : ℝ) := le_trans hS4p.2 (by norm_num)
  have hSDpU : oddCouplingCross du su dv sv p11 p13 p33 ≤
      (424 / 1000000 : ℝ) := le_trans hSDp (by norm_num)
  have hD4pL : (-1072 / 1000000 : ℝ) ≤
      oddCouplingCross du u4 dv v4 p11 p13 p33 :=
    le_trans (by norm_num) hD4p.1
  have hW4pU : oddCouplingFour u4 v4 p11 p13 p33 ≤
      (4703 / 1000000 : ℝ) := le_trans hW4p (by norm_num)
  have hS4mU : oddCouplingCross su u4 sv v4 m11 m13 m33 ≤
      (2109 / 100000 : ℝ) := le_trans hS4m.2 (by norm_num)
  have hSDmU : oddCouplingCross du su dv sv m11 m13 m33 ≤
      (850 / 1000000 : ℝ) := le_trans hSDm (by norm_num)
  have hD4mL : (-660 / 1000000 : ℝ) ≤
      oddCouplingCross du u4 dv v4 m11 m13 m33 :=
    le_trans (by norm_num) hD4m.1
  have hW4mU : oddCouplingFour u4 v4 m11 m13 m33 ≤
      (964 / 100000 : ℝ) := le_trans hW4m (by norm_num)
  dsimp only [p11, p13, p33, m11, m13, m33] at hS4pU hSDpU hD4pL hW4pU hS4mU hSDmU hD4mL hW4mU
  exact ⟨hS4pU, hSDpU, hD4pL, hW4pU,
    hS4mU, hSDmU, hD4mL, hW4mU⟩

set_option maxHeartbeats 3000000 in
theorem correlated_clean_unfix_X
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    correlatedCoefficientThree
        cornerA cornerX R C D F
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 ≤
      correlatedCoefficientThree
        cornerA X R C D F
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  norm_num at hXL hXU hRL hRU hDL hDU hFL hFU hxL hxU hrL hrU hdL hdU hfL hfU
  let g : ℝ → ℝ := fun z ↦ correlatedCoefficientThree
    cornerA z R C D F
    a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33
  have hsec : quadraticSecant g X cornerX ≤ (0 : ℝ) := by
    let gdet : ℝ → ℝ := fun z ↦ correlatedDeterminantBlock
      cornerA z R C D F a x r c d f q11 q13 q33 h11 h13 h33
    let gcoupling : ℝ → ℝ := fun z ↦ correlatedCouplingBlock
      cornerA z R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33
    let gcross : ℝ → ℝ := fun z ↦ correlatedCrossBlock
      (cornerA + a) (z + x) (R + r) (C + c) (D + d)
        F f su du u4 sv dv v4
    have hdet : quadraticSecant gdet X cornerX ≤ (-214 / 100000 : ℝ) := by
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
      rcases cleanX_determinant_coefficient_bounds
          A X R C D F a x r c d f su du u4 sv dv v4
            q11 q13 q33 h11 h13 h33 hbox with
        ⟨hgm, hgx, hgp⟩
      have hsecEq : quadraticSecant gdet X cornerX =
          cleanXDetMinusCoefficient X R D F x r d f * om +
            cleanXDetMixedCoefficient X R D F x r d f * ox +
              cleanXDetPlusCoefficient X R D F x r d f * op := by
        unfold gdet quadraticSecant correlatedDeterminantBlock
          alignedDeterminant alignedMixedDeterminant alignedEntry00 alignedEntry02
          alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
          cleanXDetMinusCoefficient cleanXDetMixedCoefficient
          cleanXDetPlusCoefficient
        dsimp only [om, ox, op]
        simp only [cornerA, cornerX]
        ring
      have hmProd := positive_negative_product_upper
        om (cleanXDetMinusCoefficient X R D F x r d f)
        (26 / 1000) (-15 / 1000) hom
        (by linarith only [hgm]) (by norm_num) hgm
      have hxProd := positive_negative_product_upper
        ox (cleanXDetMixedCoefficient X R D F x r d f)
        (41 / 1000) (-43 / 1000) hox
        (by linarith only [hgx]) (by norm_num) hgx
      have hpProd := positive_negative_product_upper
        op (cleanXDetPlusCoefficient X R D F x r d f)
        (4 / 1000) (-28 / 1000) hop
        (by linarith only [hgp]) (by norm_num) hgp
      rw [hsecEq]
      nlinarith only [hmProd, hxProd, hpProd]
    have hcoupling : quadraticSecant gcoupling X cornerX ≤
        (230 / 100000 : ℝ) := by
      let S4p : ℝ := oddCouplingCross su u4 sv v4
        (q11 + h11) (q13 + h13) (q33 + h33)
      let SDp : ℝ := oddCouplingCross du su dv sv
        (q11 + h11) (q13 + h13) (q33 + h33)
      let D4p : ℝ := oddCouplingCross du u4 dv v4
        (q11 + h11) (q13 + h13) (q33 + h33)
      let W4p : ℝ := oddCouplingFour u4 v4
        (q11 + h11) (q13 + h13) (q33 + h33)
      let S4m : ℝ := oddCouplingCross su u4 sv v4
        (q11 - h11) (q13 - h13) (q33 - h33)
      let SDm : ℝ := oddCouplingCross du su dv sv
        (q11 - h11) (q13 - h13) (q33 - h33)
      let D4m : ℝ := oddCouplingCross du u4 dv v4
        (q11 - h11) (q13 - h13) (q33 - h33)
      let W4m : ℝ := oddCouplingFour u4 v4
        (q11 - h11) (q13 - h13) (q33 - h33)
      rcases cleanX_coupling_form_bounds
          A X R C D F a x r c d f su du u4 sv dv v4
            q11 q13 q33 h11 h13 h33 hbox with
        ⟨hS4pU, hSDpU, hD4pL, hW4pU, hS4mU, hSDmU, hD4mL, hW4mU⟩
      change S4p ≤ (3355 / 1000000 : ℝ) at hS4pU
      change SDp ≤ (424 / 1000000 : ℝ) at hSDpU
      change (-1072 / 1000000 : ℝ) ≤ D4p at hD4pL
      change W4p ≤ (4703 / 1000000 : ℝ) at hW4pU
      change S4m ≤ (2109 / 100000 : ℝ) at hS4mU
      change SDm ≤ (850 / 1000000 : ℝ) at hSDmU
      change (-660 / 1000000 : ℝ) ≤ D4m at hD4mL
      change W4m ≤ (964 / 100000 : ℝ) at hW4mU
      have hcS4p0 : 0 ≤ 2 * (D + d) := by
        linarith only [hDL, hdL]
      have hcSDp0 : 0 ≤ 2 * (F + f) := by
        linarith only [hFL, hfL]
      have hcD4p0 : 0 ≤ 2 * (R + r) := by
        linarith only [hRL, hrL]
      have hcW4p0 : 0 ≤ X + cornerX + 2 * x := by
        norm_num [cornerX] at ⊢
        linarith only [hXL, hxL]
      have hcS4m0 : 0 ≤ 2 * D := by linarith only [hDL]
      have hcSDm0 : 0 ≤ 2 * F := by linarith only [hFL]
      have hcD4m0 : 0 ≤ 2 * R := by linarith only [hRL]
      have hcW4m0 : 0 ≤ X + cornerX := by
        norm_num [cornerX] at ⊢
        linarith only [hXL]
      have hS4pProd := product_upper_of_nonnegative_left
        (2 * (D + d)) S4p (141 / 1000) (3355 / 1000000)
        hcS4p0 (by linarith only [hDU, hdU]) hS4pU (by norm_num)
      have hSDpProd := product_upper_of_nonnegative_left
        (2 * (F + f)) SDp (984 / 1000) (424 / 1000000)
        hcSDp0 (by linarith only [hFU, hfU]) hSDpU (by norm_num)
      have hD4pProd := product_upper_of_nonnegative_left
        (2 * (R + r)) (-D4p) (601 / 1000) (1072 / 1000000)
        hcD4p0 (by linarith only [hRU, hrU])
        (by linarith only [hD4pL]) (by norm_num)
      have hW4pProd := product_upper_of_nonnegative_left
        (X + cornerX + 2 * x) W4p (160 / 1000) (4703 / 1000000)
        hcW4p0
        (by norm_num [cornerX] at ⊢; linarith only [hXU, hxU])
        hW4pU (by norm_num)
      have hS4mProd := product_upper_of_nonnegative_left
        (2 * D) S4m (86 / 1000) (2109 / 100000)
        hcS4m0 (by linarith only [hDU]) hS4mU (by norm_num)
      have hSDmProd := product_upper_of_nonnegative_left
        (2 * F) SDm (63 / 100) (850 / 1000000)
        hcSDm0 (by linarith only [hFU]) hSDmU (by norm_num)
      have hD4mProd := product_upper_of_nonnegative_left
        (2 * R) (-D4m) (486 / 1000) (660 / 1000000)
        hcD4m0 (by linarith only [hRU])
        (by linarith only [hD4mL]) (by norm_num)
      have hW4mProd := product_upper_of_nonnegative_left
        (X + cornerX) W4m (80 / 1000) (964 / 100000)
        hcW4m0
        (by norm_num [cornerX] at ⊢; linarith only [hXU])
        hW4mU (by norm_num)
      have hsecEq : quadraticSecant gcoupling X cornerX =
          (2 * (D + d) * S4p + 2 * (F + f) * SDp +
              2 * (R + r) * (-D4p) + (X + cornerX + 2 * x) * W4p) / 4 +
            (2 * D * S4m + 2 * F * SDm + 2 * R * (-D4m) +
              (X + cornerX) * W4m) / 2 := by
        unfold gcoupling quadraticSecant correlatedCouplingBlock
          alignedAdjugatePair alignedMixedAdjugatePair
        dsimp only [S4p, SDp, D4p, W4p, S4m, SDm, D4m, W4m]
        unfold oddCouplingCross oddCouplingFour
        simp only [cornerA, cornerX]
        ring
      rw [hsecEq]
      nlinarith only [hS4pProd, hSDpProd, hD4pProd, hW4pProd,
        hS4mProd, hSDmProd, hD4mProd, hW4mProd]
    have hcross : quadraticSecant gcross X cornerX ≤
        (-30 / 100000 : ℝ) := by
      rcases cleanX_cross_gap_bounds
          A X R C D F a x r c d f su du u4 sv dv v4
            q11 q13 q33 h11 h13 h33 hbox with
        ⟨hwide, hnarrow⟩
      have hprod := nonnegative_product_lower
        (u4 * sv - v4 * su) (u4 * dv - v4 * du)
        (77 / 1000) (78 / 10000) hwide hnarrow
        (by norm_num) (by linarith only [hnarrow])
      have hsecEq : quadraticSecant gcross X cornerX =
          -(u4 * sv - v4 * su) * (u4 * dv - v4 * du) / 2 := by
        unfold gcross quadraticSecant correlatedCrossBlock alignedCrossEnergy
        dsimp only
        simp only [cornerA, cornerX]
        ring
      rw [hsecEq]
      nlinarith only [hprod]
    have hsplit : quadraticSecant g X cornerX =
        quadraticSecant gdet X cornerX +
          quadraticSecant gcoupling X cornerX +
            quadraticSecant gcross X cornerX := by
      unfold g gdet gcoupling gcross quadraticSecant
      simp only [correlatedCoefficientThree_eq_blocks]
      ring
    nlinarith only [hsplit, hdet, hcoupling, hcross]
  have hid : g X - g cornerX =
      (X - cornerX) * quadraticSecant g X cornerX := by
    unfold g quadraticSecant correlatedCoefficientThree alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  exact quadraticSecant_upper_endpoint g X cornerX
    (by simpa only [cornerX] using hbox.X_mem.2) hsec hid

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3Structural
