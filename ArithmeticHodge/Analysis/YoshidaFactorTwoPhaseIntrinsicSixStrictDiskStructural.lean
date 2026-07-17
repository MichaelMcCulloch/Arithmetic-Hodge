import ArithmeticHodge.Analysis.ThreeByThreeConvexPencil
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusNonnegativeStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusFinalDeterminantStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixStrictDiskStructural

noncomputable section

open ThreeByThreeConvexPencil
open ThreeByThreeRankOneSchur
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicFourP45Reduction
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusNonnegativeStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusFinalDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSplitStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Strict positivity of the intrinsic six-mode phase disk

The existing endpoint certificates prove all three strict Sylvester gates of
both even blocks and both fraction-free odd Schur blocks.  The first part of
this file assembles those twelve scalar gates into strict positivity of the
two corrected six-dimensional endpoint forms.

The square-root interpolation used for closed-disk nonnegativity is then
strengthened at exactly one point: for a nonzero six-vector, its two
complementarily scaled copies cannot both vanish.  Hence each of the two
extreme cross forms is strictly positive, and interpolation in the second
phase coordinate preserves strictness on the entire closed disk.
-/

/-! ## Strict fraction-free Schur composition -/

/-- The fraction-free completion identity used below.  It is stated
separately so the strict block argument remains entirely inverse-free. -/
private theorem fractionFree_three_by_three_completion
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4
      c0 c2 c4 r : ℝ) :
    let d := symmetricDeterminant e00 e02 e04 e22 e24 e44
    let v := adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4
    d ^ 2 *
        (symmetricQuadratic e00 e02 e04 e22 e24 e44 c0 c2 c4 +
          2 * (c0 * ell0 + c2 * ell2 + c4 * ell4) + r) =
      symmetricQuadratic e00 e02 e04 e22 e24 e44
          (d * c0 + v 0) (d * c2 + v 1) (d * c4 + v 2) +
        d * (d * r - adjugateQuadratic
          e00 e02 e04 e22 e24 e44 ell0 ell2 ell4) := by
  dsimp only
  simp only [adjugateVector]
  unfold symmetricQuadratic symmetricDeterminant adjugateQuadratic
  ring

/-- Strict version of the reusable inverse-free `3 + 3` Schur reduction.
Strict Sylvester pivots of the leading block and strict positivity of the
fraction-free Schur form make the full block strictly positive away from the
origin. -/
theorem sixBlock_pos_of_fractionFreeSchur
    (e00 e02 e04 e22 e24 e44
      k01 k03 k05 k21 k23 k25 k41 k43 k45
      o11 o13 o15 o33 o35 o55 : ℝ)
    (he00 : 0 < e00)
    (heMinor : 0 < leadingMinorTwo e00 e02 e22)
    (heDet : 0 < symmetricDeterminant e00 e02 e04 e22 e24 e44)
    (hT : ∀ c1 c3 c5 : ℝ,
      c1 ≠ 0 ∨ c3 ≠ 0 ∨ c5 ≠ 0 →
        0 < symmetricDeterminant e00 e02 e04 e22 e24 e44 *
            symmetricQuadratic o11 o13 o15 o33 o35 o55 c1 c3 c5 -
          adjugateQuadratic e00 e02 e04 e22 e24 e44
            (k01 * c1 + k03 * c3 + k05 * c5)
            (k21 * c1 + k23 * c3 + k25 * c5)
            (k41 * c1 + k43 * c3 + k45 * c5))
    (c0 c2 c4 c1 c3 c5 : ℝ)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨
      c1 ≠ 0 ∨ c3 ≠ 0 ∨ c5 ≠ 0) :
    0 < symmetricQuadratic e00 e02 e04 e22 e24 e44 c0 c2 c4 +
      2 * (c0 * (k01 * c1 + k03 * c3 + k05 * c5) +
        c2 * (k21 * c1 + k23 * c3 + k25 * c5) +
        c4 * (k41 * c1 + k43 * c3 + k45 * c5)) +
      symmetricQuadratic o11 o13 o15 o33 o35 o55 c1 c3 c5 := by
  by_cases hOdd : c1 ≠ 0 ∨ c3 ≠ 0 ∨ c5 ≠ 0
  · let d := symmetricDeterminant e00 e02 e04 e22 e24 e44
    let ell0 := k01 * c1 + k03 * c3 + k05 * c5
    let ell2 := k21 * c1 + k23 * c3 + k25 * c5
    let ell4 := k41 * c1 + k43 * c3 + k45 * c5
    let v := adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4
    have hEven : 0 ≤ symmetricQuadratic e00 e02 e04 e22 e24 e44
        (d * c0 + v 0) (d * c2 + v 1) (d * c4 + v 2) :=
      symmetricQuadratic_nonneg e00 e02 e04 e22 e24 e44
        he00 heMinor heDet _ _ _
    have hSchur := hT c1 c3 c5 hOdd
    have hIdentity := fractionFree_three_by_three_completion
      e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 c0 c2 c4
        (symmetricQuadratic o11 o13 o15 o33 o35 o55 c1 c3 c5)
    dsimp only [d, ell0, ell2, ell4, v] at hEven hIdentity
    have hScaled : 0 <
        symmetricDeterminant e00 e02 e04 e22 e24 e44 ^ 2 *
          (symmetricQuadratic e00 e02 e04 e22 e24 e44 c0 c2 c4 +
            2 * (c0 * (k01 * c1 + k03 * c3 + k05 * c5) +
              c2 * (k21 * c1 + k23 * c3 + k25 * c5) +
              c4 * (k41 * c1 + k43 * c3 + k45 * c5)) +
            symmetricQuadratic o11 o13 o15 o33 o35 o55 c1 c3 c5) := by
      rw [hIdentity]
      exact add_pos_of_nonneg_of_pos hEven (mul_pos heDet hSchur)
    exact pos_of_mul_pos_right hScaled (sq_nonneg _)
  · push_neg at hOdd
    rcases hOdd with ⟨rfl, rfl, rfl⟩
    have hEvenNe : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 := by
      simpa using hne
    simpa only [mul_zero, add_zero, zero_mul,
      symmetricQuadratic, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      symmetricQuadratic_pos e00 e02 e04 e22 e24 e44
        he00 heMinor heDet c0 c2 c4 hEvenNe

/-! ## Strict endpoint blocks -/

/-- The positive fraction-free odd Schur block is positive definite. -/
theorem factorTwoIntrinsicSixUnbalancedTPlusQuadratic_pos
    (c1 c3 c5 : ℝ) (hne : c1 ≠ 0 ∨ c3 ≠ 0 ∨ c5 ≠ 0) :
    0 < factorTwoIntrinsicSixUnbalancedTPlusQuadratic c1 c3 c5 := by
  unfold factorTwoIntrinsicSixUnbalancedTPlusQuadratic
  exact symmetricQuadratic_pos
    factorTwoIntrinsicSixUnbalancedTPlus11
    factorTwoIntrinsicSixUnbalancedTPlus13
    factorTwoIntrinsicSixUnbalancedTPlus15
    factorTwoIntrinsicSixUnbalancedTPlus33
    factorTwoIntrinsicSixUnbalancedTPlus35
    factorTwoIntrinsicSixUnbalancedTPlus55
    factorTwoIntrinsicSixUnbalancedTPlus11_pos
    factorTwoIntrinsicSixUnbalancedTPlusMinor_pos
    factorTwoIntrinsicSixUnbalancedTPlusDet_pos c1 c3 c5 hne

/-- The negative fraction-free odd Schur block is positive definite. -/
theorem factorTwoIntrinsicSixUnbalancedTMinusQuadratic_pos
    (c1 c3 c5 : ℝ) (hne : c1 ≠ 0 ∨ c3 ≠ 0 ∨ c5 ≠ 0) :
    0 < factorTwoIntrinsicSixUnbalancedTMinusQuadratic c1 c3 c5 := by
  unfold factorTwoIntrinsicSixUnbalancedTMinusQuadratic
  exact symmetricQuadratic_pos
    factorTwoIntrinsicSixUnbalancedTMinus11
    factorTwoIntrinsicSixUnbalancedTMinus13
    factorTwoIntrinsicSixUnbalancedTMinus15
    factorTwoIntrinsicSixUnbalancedTMinus33
    factorTwoIntrinsicSixUnbalancedTMinus35
    factorTwoIntrinsicSixUnbalancedTMinus55
    factorTwoIntrinsicSixUnbalancedTMinus11_pos
    factorTwoIntrinsicSixUnbalancedTMinusMinor_pos
    factorTwoIntrinsicSixUnbalancedTMinusDet_pos c1 c3 c5 hne

/-- All six strict Sylvester gates assemble to strict positivity of the
corrected positive endpoint. -/
theorem factorTwoIntrinsicSixUnbalancedStaticPlus_pos
    (c0 c2 c4 c1 c3 c5 : ℝ)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨
      c1 ≠ 0 ∨ c3 ≠ 0 ∨ c5 ≠ 0) :
    0 < factorTwoIntrinsicSixUnbalancedStaticPlus
      c0 c2 c4 c1 c3 c5 := by
  rw [factorTwoIntrinsicSixUnbalancedStaticPlus_eq_block]
  rcases factorTwoIntrinsicSixUnbalancedEPlus_positive with
    ⟨he00, heMinor, heDet⟩
  apply sixBlock_pos_of_fractionFreeSchur
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    factorTwoIntrinsicSixUnbalancedKPlus01
    factorTwoIntrinsicSixUnbalancedKPlus03
    factorTwoIntrinsicSixUnbalancedKPlus05
    factorTwoIntrinsicSixUnbalancedKPlus21
    factorTwoIntrinsicSixUnbalancedKPlus23
    factorTwoIntrinsicSixUnbalancedKPlus25
    factorTwoIntrinsicSixUnbalancedKPlus41
    factorTwoIntrinsicSixUnbalancedKPlus43
    factorTwoIntrinsicSixUnbalancedKPlus45
    factorTwoIntrinsicSixUnbalancedOMinus11
    factorTwoIntrinsicSixUnbalancedOMinus13
    factorTwoIntrinsicSixUnbalancedOMinus15
    factorTwoIntrinsicSixUnbalancedOMinus33
    factorTwoIntrinsicSixUnbalancedOMinus35
    factorTwoIntrinsicSixUnbalancedOMinus55
    he00 heMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedEPlusDet] using heDet
  · intro d1 d3 d5 hd
    have h := factorTwoIntrinsicSixUnbalancedTPlusQuadratic_pos d1 d3 d5 hd
    rw [factorTwoIntrinsicSixUnbalancedTPlusQuadratic_eq_fractionFree] at h
    simpa only [factorTwoIntrinsicSixUnbalancedEPlusDet] using h
  · exact hne

/-- All six strict Sylvester gates assemble to strict positivity of the
corrected negative endpoint. -/
theorem factorTwoIntrinsicSixUnbalancedStaticMinus_pos
    (c0 c2 c4 c1 c3 c5 : ℝ)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨
      c1 ≠ 0 ∨ c3 ≠ 0 ∨ c5 ≠ 0) :
    0 < factorTwoIntrinsicSixUnbalancedStaticMinus
      c0 c2 c4 c1 c3 c5 := by
  rw [factorTwoIntrinsicSixUnbalancedStaticMinus_eq_block]
  rcases factorTwoIntrinsicSixUnbalancedEMinus_positive with
    ⟨he00, heMinor, heDet⟩
  apply sixBlock_pos_of_fractionFreeSchur
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    factorTwoIntrinsicSixUnbalancedKMinus01
    factorTwoIntrinsicSixUnbalancedKMinus03
    factorTwoIntrinsicSixUnbalancedKMinus05
    factorTwoIntrinsicSixUnbalancedKMinus21
    factorTwoIntrinsicSixUnbalancedKMinus23
    factorTwoIntrinsicSixUnbalancedKMinus25
    factorTwoIntrinsicSixUnbalancedKMinus41
    factorTwoIntrinsicSixUnbalancedKMinus43
    factorTwoIntrinsicSixUnbalancedKMinus45
    factorTwoIntrinsicSixUnbalancedOPlus11
    factorTwoIntrinsicSixUnbalancedOPlus13
    factorTwoIntrinsicSixUnbalancedOPlus15
    factorTwoIntrinsicSixUnbalancedOPlus33
    factorTwoIntrinsicSixUnbalancedOPlus35
    factorTwoIntrinsicSixUnbalancedOPlus55
    he00 heMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedEMinusDet] using heDet
  · intro d1 d3 d5 hd
    have h := factorTwoIntrinsicSixUnbalancedTMinusQuadratic_pos d1 d3 d5 hd
    rw [factorTwoIntrinsicSixUnbalancedTMinusQuadratic_eq_fractionFree] at h
    simpa only [factorTwoIntrinsicSixUnbalancedEMinusDet] using h
  · exact hne

/-! ## Strict square-root interpolation on the phase disk -/

/-- The complete intrinsic six-coordinate phase quadratic is strictly
positive for every disk phase and every nonzero coefficient vector. -/
theorem factorTwoIntrinsicSixPhaseCoordinates_pos
    (c0 c2 c4 c1 c3 c5 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨
      c1 ≠ 0 ∨ c3 ≠ 0 ∨ c5 ≠ 0) :
    0 < factorTwoIntrinsicSixStaticEven a c0 c2 c4 +
      factorTwoIntrinsicSixStaticOdd (-a) c1 c3 c5 +
      b * factorTwoIntrinsicSixStaticAlternating
        c0 c2 c4 c1 c3 c5 := by
  let EPlus := factorTwoIntrinsicSixStaticEven 1 c0 c2 c4
  let EMinus := factorTwoIntrinsicSixStaticEven (-1) c0 c2 c4
  let OMinus := factorTwoIntrinsicSixStaticOdd 1 c1 c3 c5
  let OPlus := factorTwoIntrinsicSixStaticOdd (-1) c1 c3 c5
  let QE := (EPlus + EMinus) / 2
  let PE := (EPlus - EMinus) / 2
  let QO := (OMinus + OPlus) / 2
  let PO := (OPlus - OMinus) / 2
  let J := factorTwoIntrinsicSixStaticAlternating c0 c2 c4 c1 c3 c5
  let H := factorTwoIntrinsicSixUnbalancedTransfer c0 c2 c4 c1 c3 c5
  have haUpper : a ≤ 1 := by
    nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
  have haLower : -1 ≤ a := by
    nlinarith [sq_nonneg b, sq_nonneg (a + 1)]
  have hLambda : 0 ≤ (1 + a) / 2 := by linarith
  have hMu : 0 ≤ (1 - a) / 2 := by linarith
  let u : ℝ := Real.sqrt ((1 + a) / 2)
  let v : ℝ := Real.sqrt ((1 - a) / 2)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have huSq : u ^ 2 = (1 + a) / 2 := by
    exact Real.sq_sqrt hLambda
  have hvSq : v ^ 2 = (1 - a) / 2 := by
    exact Real.sq_sqrt hMu
  have huv : u ≠ 0 ∨ v ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    rcases hzero with ⟨hu0, hv0⟩
    nlinarith [huSq, hvSq]
  let c : ℝ := 2 * u * v
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hcSq : c ^ 2 = 1 - a ^ 2 := by
    dsimp only [c]
    rw [mul_pow, mul_pow, huSq, hvSq]
    ring
  have hbSq : b ^ 2 ≤ c ^ 2 := by
    rw [hcSq]
    linarith
  have hbUpper : b ≤ c := by
    by_contra hbc
    have hcb : c < b := lt_of_not_ge hbc
    have hb0 : 0 < b := hc.trans_lt hcb
    have hprod : 0 < (b - c) * (b + c) :=
      mul_pos (sub_pos.mpr hcb) (add_pos_of_pos_of_nonneg hb0 hc)
    nlinarith
  have hbLower : -c ≤ b := by
    by_contra hbc
    have hbc' : b < -c := lt_of_not_ge hbc
    have hneg : 0 < -b - c := by linarith
    have hsum : 0 < -b + c := by linarith
    have hprod : 0 < (-b - c) * (-b + c) := mul_pos hneg hsum
    nlinarith
  let plusNE : Prop :=
    u * c0 ≠ 0 ∨ u * c2 ≠ 0 ∨ u * c4 ≠ 0 ∨
      v * c1 ≠ 0 ∨ v * c3 ≠ 0 ∨ v * c5 ≠ 0
  let minusNE : Prop :=
    v * c0 ≠ 0 ∨ v * c2 ≠ 0 ∨ v * c4 ≠ 0 ∨
      u * c1 ≠ 0 ∨ u * c3 ≠ 0 ∨ u * c5 ≠ 0
  have hscaledNE : plusNE ∨ minusNE := by
    dsimp only [plusNE, minusNE]
    rcases huv with hu0 | hv0
    · rcases hne with h0 | h2 | h4 | h1 | h3 | h5
      · exact Or.inl (Or.inl (mul_ne_zero hu0 h0))
      · exact Or.inl (Or.inr (Or.inl (mul_ne_zero hu0 h2)))
      · exact Or.inl (Or.inr (Or.inr (Or.inl (mul_ne_zero hu0 h4))))
      · exact Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl (mul_ne_zero hu0 h1)))))
      · exact Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl (mul_ne_zero hu0 h3))))))
      · exact Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (mul_ne_zero hu0 h5))))))
    · rcases hne with h0 | h2 | h4 | h1 | h3 | h5
      · exact Or.inr (Or.inl (mul_ne_zero hv0 h0))
      · exact Or.inr (Or.inr (Or.inl (mul_ne_zero hv0 h2)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (mul_ne_zero hv0 h4))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
          (mul_ne_zero hv0 h1)))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (mul_ne_zero hv0 h3))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (mul_ne_zero hv0 h5))))))
  have hscaledNegativeNE :
      (u * c0 ≠ 0 ∨ u * c2 ≠ 0 ∨ u * c4 ≠ 0 ∨
        (-v) * c1 ≠ 0 ∨ (-v) * c3 ≠ 0 ∨ (-v) * c5 ≠ 0) ∨
      (v * c0 ≠ 0 ∨ v * c2 ≠ 0 ∨ v * c4 ≠ 0 ∨
        (-u) * c1 ≠ 0 ∨ (-u) * c3 ≠ 0 ∨ (-u) * c5 ≠ 0) := by
    dsimp only [plusNE, minusNE] at hscaledNE
    simpa only [neg_mul, neg_ne_zero] using hscaledNE
  let D : ℝ := QE + QO + a * (PE + PO)
  have hPositiveCross : 0 < D + c * J := by
    have hPlusNonneg :=
      factorTwoIntrinsicSixUnbalancedStaticPlusNonnegative
        (u * c0) (u * c2) (u * c4)
        (v * c1) (v * c3) (v * c5)
    have hMinusNonneg :=
      factorTwoIntrinsicSixUnbalancedStaticMinusNonnegative
        (v * c0) (v * c2) (v * c4)
        (u * c1) (u * c3) (u * c5)
    have hSplit :
        0 < factorTwoIntrinsicSixUnbalancedStaticPlus
              (u * c0) (u * c2) (u * c4)
              (v * c1) (v * c3) (v * c5) +
            factorTwoIntrinsicSixUnbalancedStaticMinus
              (v * c0) (v * c2) (v * c4)
              (u * c1) (u * c3) (u * c5) := by
      rcases hscaledNE with hPlus | hMinus
      · exact add_pos_of_pos_of_nonneg
          (factorTwoIntrinsicSixUnbalancedStaticPlus_pos
            (u * c0) (u * c2) (u * c4)
            (v * c1) (v * c3) (v * c5) hPlus)
          hMinusNonneg
      · exact add_pos_of_nonneg_of_pos hPlusNonneg
          (factorTwoIntrinsicSixUnbalancedStaticMinus_pos
            (v * c0) (v * c2) (v * c4)
            (u * c1) (u * c3) (u * c5) hMinus)
    have hPlusScale :
        factorTwoIntrinsicSixUnbalancedStaticPlus
            (u * c0) (u * c2) (u * c4)
            (v * c1) (v * c3) (v * c5) =
          u ^ 2 * EPlus + v ^ 2 * OMinus + u * v * (J - 2 * H) := by
      dsimp only [EPlus, OMinus, J, H]
      unfold factorTwoIntrinsicSixUnbalancedStaticPlus
        factorTwoIntrinsicSixStaticEven
        factorTwoIntrinsicSixStaticOdd
        factorTwoIntrinsicSixStaticAlternating
        factorTwoIntrinsicSixUnbalancedTransfer
        factorTwoIntrinsicOddPhaseQuadratic
      ring
    have hMinusScale :
        factorTwoIntrinsicSixUnbalancedStaticMinus
            (v * c0) (v * c2) (v * c4)
            (u * c1) (u * c3) (u * c5) =
          v ^ 2 * EMinus + u ^ 2 * OPlus + v * u * (J + 2 * H) := by
      dsimp only [EMinus, OPlus, J, H]
      unfold factorTwoIntrinsicSixUnbalancedStaticMinus
        factorTwoIntrinsicSixStaticEven
        factorTwoIntrinsicSixStaticOdd
        factorTwoIntrinsicSixStaticAlternating
        factorTwoIntrinsicSixUnbalancedTransfer
        factorTwoIntrinsicOddPhaseQuadratic
      ring
    rw [hPlusScale, hMinusScale] at hSplit
    rw [huSq, hvSq] at hSplit
    dsimp only [D, c, QE, PE, QO, PO]
    nlinarith
  have hNegativeCross : 0 < D - c * J := by
    have hPlusNonneg :=
      factorTwoIntrinsicSixUnbalancedStaticPlusNonnegative
        (u * c0) (u * c2) (u * c4)
        ((-v) * c1) ((-v) * c3) ((-v) * c5)
    have hMinusNonneg :=
      factorTwoIntrinsicSixUnbalancedStaticMinusNonnegative
        (v * c0) (v * c2) (v * c4)
        ((-u) * c1) ((-u) * c3) ((-u) * c5)
    have hSplit :
        0 < factorTwoIntrinsicSixUnbalancedStaticPlus
              (u * c0) (u * c2) (u * c4)
              ((-v) * c1) ((-v) * c3) ((-v) * c5) +
            factorTwoIntrinsicSixUnbalancedStaticMinus
              (v * c0) (v * c2) (v * c4)
              ((-u) * c1) ((-u) * c3) ((-u) * c5) := by
      rcases hscaledNegativeNE with hPlus | hMinus
      · exact add_pos_of_pos_of_nonneg
          (factorTwoIntrinsicSixUnbalancedStaticPlus_pos
            (u * c0) (u * c2) (u * c4)
            ((-v) * c1) ((-v) * c3) ((-v) * c5) hPlus)
          hMinusNonneg
      · exact add_pos_of_nonneg_of_pos hPlusNonneg
          (factorTwoIntrinsicSixUnbalancedStaticMinus_pos
            (v * c0) (v * c2) (v * c4)
            ((-u) * c1) ((-u) * c3) ((-u) * c5) hMinus)
    have hPlusScale :
        factorTwoIntrinsicSixUnbalancedStaticPlus
            (u * c0) (u * c2) (u * c4)
            ((-v) * c1) ((-v) * c3) ((-v) * c5) =
          u ^ 2 * EPlus + v ^ 2 * OMinus - u * v * (J - 2 * H) := by
      dsimp only [EPlus, OMinus, J, H]
      unfold factorTwoIntrinsicSixUnbalancedStaticPlus
        factorTwoIntrinsicSixStaticEven
        factorTwoIntrinsicSixStaticOdd
        factorTwoIntrinsicSixStaticAlternating
        factorTwoIntrinsicSixUnbalancedTransfer
        factorTwoIntrinsicOddPhaseQuadratic
      ring
    have hMinusScale :
        factorTwoIntrinsicSixUnbalancedStaticMinus
            (v * c0) (v * c2) (v * c4)
            ((-u) * c1) ((-u) * c3) ((-u) * c5) =
          v ^ 2 * EMinus + u ^ 2 * OPlus - v * u * (J + 2 * H) := by
      dsimp only [EMinus, OPlus, J, H]
      unfold factorTwoIntrinsicSixUnbalancedStaticMinus
        factorTwoIntrinsicSixStaticEven
        factorTwoIntrinsicSixStaticOdd
        factorTwoIntrinsicSixStaticAlternating
        factorTwoIntrinsicSixUnbalancedTransfer
        factorTwoIntrinsicOddPhaseQuadratic
      ring
    rw [hPlusScale, hMinusScale] at hSplit
    rw [huSq, hvSq] at hSplit
    dsimp only [D, c, QE, PE, QO, PO]
    nlinarith
  have hEvenAffine :
      (EPlus + EMinus) / 2 + a * ((EPlus - EMinus) / 2) =
        factorTwoIntrinsicSixStaticEven a c0 c2 c4 := by
    dsimp only [EPlus, EMinus]
    unfold factorTwoIntrinsicSixStaticEven
      factorTwoStructuralPhaseLow00
      factorTwoStructuralPhaseLow02
      factorTwoStructuralPhaseLow22
      factorTwoIntrinsicFourP45Cross04
      factorTwoIntrinsicFourP45Cross24
      factorTwoIntrinsicP4PhaseDiagonal
    ring
  have hOddAffine :
      (OMinus + OPlus) / 2 + a * ((OPlus - OMinus) / 2) =
        factorTwoIntrinsicSixStaticOdd (-a) c1 c3 c5 := by
    dsimp only [OMinus, OPlus]
    unfold factorTwoIntrinsicSixStaticOdd
      factorTwoIntrinsicOddPhaseQuadratic
      factorTwoIntrinsicOddPhaseLow11
      factorTwoIntrinsicOddPhaseLow13
      factorTwoIntrinsicOddPhaseLow33
      factorTwoIntrinsicFourP45Cross15
      factorTwoIntrinsicFourP45Cross35
      factorTwoIntrinsicP5PhaseDiagonal
    ring
  have hCoordinates :
      D + b * J =
        factorTwoIntrinsicSixStaticEven a c0 c2 c4 +
          factorTwoIntrinsicSixStaticOdd (-a) c1 c3 c5 +
          b * factorTwoIntrinsicSixStaticAlternating
            c0 c2 c4 c1 c3 c5 := by
    calc
      D + b * J =
          ((EPlus + EMinus) / 2 + a * ((EPlus - EMinus) / 2)) +
            ((OMinus + OPlus) / 2 + a * ((OPlus - OMinus) / 2)) +
            b * J := by
              dsimp only [D, QE, PE, QO, PO]
              ring
      _ = factorTwoIntrinsicSixStaticEven a c0 c2 c4 +
            factorTwoIntrinsicSixStaticOdd (-a) c1 c3 c5 +
            b * factorTwoIntrinsicSixStaticAlternating
              c0 c2 c4 c1 c3 c5 := by
              rw [hEvenAffine, hOddAffine]
  rw [← hCoordinates]
  by_cases hJ : 0 ≤ J
  · have hscaled := mul_le_mul_of_nonneg_right hbLower hJ
    nlinarith
  · have hJ' : J ≤ 0 := le_of_not_ge hJ
    have hscaled := mul_le_mul_of_nonpos_right hbUpper hJ'
    nlinarith

/-- Function-level form of strict intrinsic six-mode phase positivity. -/
theorem factorTwoEndpointChannelPhase_intrinsicSix_pos
    (c0 c2 c4 c1 c3 c5 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨
      c1 ≠ 0 ∨ c3 ≠ 0 ∨ c5 ≠ 0) :
    0 < factorTwoEndpointChannelPhase
      (factorTwoEvenStructuralLowProfile c0 c2 +
        factorTwoIntrinsicSixEvenTail c4)
      (factorTwoIntrinsicSixOddTail c1 c3 c5) a b := by
  rw [factorTwoEndpointChannelPhase_intrinsicSix_eq_static_coordinates]
  exact factorTwoIntrinsicSixPhaseCoordinates_pos
    c0 c2 c4 c1 c3 c5 a b hab hne

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixStrictDiskStructural
