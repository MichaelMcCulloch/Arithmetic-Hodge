import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineStaticFinalThreePositiveStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusMinorStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineRetunedMinusGatesPositive

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusPositive
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
open YoshidaFactorTwoPhaseIntrinsicNineStaticFinalThreePositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

/-!
# The first two retuned negative endpoint gates

The old negative five-mode certificate retains a quantitative diagonal
reserve after an exact rational congruence.  The retuned transfer changes
only the two low odd cross columns.  We keep that change as one exact
rational perturbation and absorb it in the retained reserve by a second
exact `LDLᵀ` decomposition.

No endpoint entry is bounded independently in this argument.
-/

/-! ## Exact low cross-column perturbation -/

private theorem retunedKMinus00_eq_old :
    factorTwoIntrinsicNineRetunedKMinus 0 0 =
      factorTwoIntrinsicSixUnbalancedKMinus01 - 639 / 100000 := by
  unfold factorTwoIntrinsicSixUnbalancedKMinus01
    factorTwoIntrinsicAlternating01
  simp [factorTwoIntrinsicNineRetunedKMinus,
    factorTwoIntrinsicNineRetunedEvenBasis,
    factorTwoIntrinsicNineRetunedOddBasis,
    factorTwoIntrinsicNineRetunedH]
  ring

private theorem retunedKMinus10_eq_old :
    factorTwoIntrinsicNineRetunedKMinus 1 0 =
      factorTwoIntrinsicSixUnbalancedKMinus21 - 333 / 100000 := by
  unfold factorTwoIntrinsicSixUnbalancedKMinus21
    factorTwoIntrinsicAlternating21
  simp [factorTwoIntrinsicNineRetunedKMinus,
    factorTwoIntrinsicNineRetunedEvenBasis,
    factorTwoIntrinsicNineRetunedOddBasis,
    factorTwoIntrinsicNineRetunedH]
  ring

private theorem retunedKMinus20_eq_old :
    factorTwoIntrinsicNineRetunedKMinus 2 0 =
      factorTwoIntrinsicSixUnbalancedKMinus41 + 874 / 100000 := by
  unfold factorTwoIntrinsicSixUnbalancedKMinus41
    factorTwoIntrinsicFourP45Cross41
  simp [factorTwoIntrinsicNineRetunedKMinus,
    factorTwoIntrinsicNineRetunedEvenBasis,
    factorTwoIntrinsicNineRetunedOddBasis,
    factorTwoIntrinsicNineRetunedH]
  ring

private theorem retunedKMinus01_eq_old :
    factorTwoIntrinsicNineRetunedKMinus 0 1 =
      factorTwoIntrinsicSixUnbalancedKMinus03 + 1533 / 100000 := by
  unfold factorTwoIntrinsicSixUnbalancedKMinus03
    factorTwoIntrinsicAlternating03
  simp [factorTwoIntrinsicNineRetunedKMinus,
    factorTwoIntrinsicNineRetunedEvenBasis,
    factorTwoIntrinsicNineRetunedOddBasis,
    factorTwoIntrinsicNineRetunedH]
  ring

private theorem retunedKMinus11_eq_old :
    factorTwoIntrinsicNineRetunedKMinus 1 1 =
      factorTwoIntrinsicSixUnbalancedKMinus23 + 1494 / 100000 := by
  unfold factorTwoIntrinsicSixUnbalancedKMinus23
    factorTwoIntrinsicAlternating23
  simp [factorTwoIntrinsicNineRetunedKMinus,
    factorTwoIntrinsicNineRetunedEvenBasis,
    factorTwoIntrinsicNineRetunedOddBasis,
    factorTwoIntrinsicNineRetunedH]
  ring

private theorem retunedKMinus21_eq_old :
    factorTwoIntrinsicNineRetunedKMinus 2 1 =
      factorTwoIntrinsicSixUnbalancedKMinus43 - 133 / 100000 := by
  unfold factorTwoIntrinsicSixUnbalancedKMinus43
    factorTwoIntrinsicFourP45Cross43
  simp [factorTwoIntrinsicNineRetunedKMinus,
    factorTwoIntrinsicNineRetunedEvenBasis,
    factorTwoIntrinsicNineRetunedOddBasis,
    factorTwoIntrinsicNineRetunedH]
  ring

/-- The exact retuned five-mode lower form, in aligned even coordinates and
the odd basis `(P₁, P₃-P₁)`. -/
private def retunedMinusLowerFiveQuadratic
    (s d p u v : ℝ) : ℝ :=
  factorTwoIntrinsicSixUnbalancedMinorMinusEvenLowerQuadratic
      (s + d) (s - d) p +
    2 * ((factorTwoIntrinsicNineRetunedKMinus 0 0 +
          factorTwoIntrinsicNineRetunedKMinus 1 0) * s +
      (factorTwoIntrinsicNineRetunedKMinus 0 0 -
          factorTwoIntrinsicNineRetunedKMinus 1 0) * d +
      factorTwoIntrinsicNineRetunedKMinus 2 0 * p) * u +
    2 * (((factorTwoIntrinsicNineRetunedKMinus 0 1 -
            factorTwoIntrinsicNineRetunedKMinus 0 0) +
          (factorTwoIntrinsicNineRetunedKMinus 1 1 -
            factorTwoIntrinsicNineRetunedKMinus 1 0)) * s +
      ((factorTwoIntrinsicNineRetunedKMinus 0 1 -
            factorTwoIntrinsicNineRetunedKMinus 0 0) -
          (factorTwoIntrinsicNineRetunedKMinus 1 1 -
            factorTwoIntrinsicNineRetunedKMinus 1 0)) * d +
      (factorTwoIntrinsicNineRetunedKMinus 2 1 -
          factorTwoIntrinsicNineRetunedKMinus 2 0) * p) * v +
    intrinsicStaticMinusOddLower (u - v) v

private def retunedMinusPerturbation
    (s d p u v : ℝ) : ℝ :=
  2 * ((-972 / 100000 : ℝ) * s - (306 / 100000 : ℝ) * d +
      (874 / 100000 : ℝ) * p) * u +
    2 * ((3999 / 100000 : ℝ) * s + (345 / 100000 : ℝ) * d -
      (1007 / 100000 : ℝ) * p) * v

private theorem retunedMinusLowerFive_eq_old_add_perturbation
    (s d p u v : ℝ) :
    retunedMinusLowerFiveQuadratic s d p u v =
      factorTwoIntrinsicSixUnbalancedMinorMinusLowerFiveQuadratic
        s d p u v +
      retunedMinusPerturbation s d p u v := by
  unfold retunedMinusLowerFiveQuadratic retunedMinusPerturbation
    factorTwoIntrinsicSixUnbalancedMinorMinusLowerFiveQuadratic
    factorTwoIntrinsicSixUnbalancedKMinusOneSum
    factorTwoIntrinsicSixUnbalancedKMinusOneDifference
    factorTwoIntrinsicSixUnbalancedKMinusShearSum
    factorTwoIntrinsicSixUnbalancedKMinusShearDifference
    factorTwoIntrinsicSixUnbalancedKMinusShearTail
  rw [retunedKMinus00_eq_old, retunedKMinus10_eq_old,
    retunedKMinus20_eq_old, retunedKMinus01_eq_old,
    retunedKMinus11_eq_old, retunedKMinus21_eq_old]
  ring

/-! ## The retained reserve absorbs the retuning -/

private def retunedMinusMapS (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  x0 - (2 / 15 : ℝ) * x1 - (1 / 6 : ℝ) * x2 -
    (1 / 20 : ℝ) * x3 + (4 / 25 : ℝ) * x4

private def retunedMinusMapD (x3 x4 : ℝ) : ℝ :=
  x3 - (11 / 4 : ℝ) * x4

private def retunedMinusMapP (x1 x2 x3 x4 : ℝ) : ℝ :=
  x1 - (4 / 35 : ℝ) * x2 + (9 / 50 : ℝ) * x3 -
    (3 / 8 : ℝ) * x4

private def retunedMinusMapU (x2 x3 x4 : ℝ) : ℝ :=
  x2 - (1 / 14 : ℝ) * x3 + (7 / 80 : ℝ) * x4

private def retunedMinusReserveQuadratic
    (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  (8653 / 6250 : ℝ) * x0 ^ 2 +
    (24687 / 80000 : ℝ) * x1 ^ 2 +
    (6447 / 80000 : ℝ) * x2 ^ 2 +
    (2153 / 1500000 : ℝ) * x3 ^ 2 +
    (517 / 800000 : ℝ) * x4 ^ 2 +
    retunedMinusPerturbation
      (retunedMinusMapS x0 x1 x2 x3 x4)
      (retunedMinusMapD x3 x4)
      (retunedMinusMapP x1 x2 x3 x4)
      (retunedMinusMapU x2 x3 x4) x4

private def retunedMinusLDLY0 (x0 x2 x3 x4 : ℝ) : ℝ :=
  x0 - (243 / 34612 : ℝ) * x2 + (243 / 484568 : ℝ) * x3 +
    (78279 / 2768960 : ℝ) * x4

private def retunedMinusLDLY1 (x1 x2 x3 x4 : ℝ) : ℝ :=
  x1 + (1544 / 47475 : ℝ) * x2 - (772 / 332325 : ℝ) * x3 -
    (290477 / 6171750 : ℝ) * x4

private def retunedMinusLDLY2 (x2 x3 x4 : ℝ) : ℝ :=
  x2 - (40942067863306 / 3278458221391829 : ℝ) * x3 -
    (130018501105729 / 9367023489690940 : ℝ) * x4

private def retunedMinusLDLY3 (x3 x4 : ℝ) : ℝ :=
  x3 - (29803976427064408585233 / 60283735595828315196520 : ℝ) * x4

private theorem retunedMinusReserveQuadratic_eq_ldl
    (x0 x1 x2 x3 x4 : ℝ) :
    retunedMinusReserveQuadratic x0 x1 x2 x3 x4 =
      (8653 / 6250 : ℝ) *
          retunedMinusLDLY0 x0 x2 x3 x4 ^ 2 +
        (24687 / 80000 : ℝ) *
          retunedMinusLDLY1 x1 x2 x3 x4 ^ 2 +
        (468351174484547 / 5751216450000000 : ℝ) *
          retunedMinusLDLY2 x2 x3 x4 ^ 2 +
        (1507093389895707879913 / 963866717089197726000000 : ℝ) *
          retunedMinusLDLY3 x3 x4 ^ 2 +
        (7202497960382709725652011199 /
            15673771254915361951095200000000 : ℝ) * x4 ^ 2 := by
  unfold retunedMinusReserveQuadratic retunedMinusPerturbation
    retunedMinusMapS retunedMinusMapD retunedMinusMapP retunedMinusMapU
    retunedMinusLDLY0 retunedMinusLDLY1 retunedMinusLDLY2
    retunedMinusLDLY3
  ring

set_option maxHeartbeats 800000 in
private theorem retunedMinusReserveQuadratic_pos
    (x0 x1 x2 x3 x4 : ℝ)
    (hne : x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0 ∨ x4 ≠ 0) :
    0 < retunedMinusReserveQuadratic x0 x1 x2 x3 x4 := by
  let y0 := retunedMinusLDLY0 x0 x2 x3 x4
  let y1 := retunedMinusLDLY1 x1 x2 x3 x4
  let y2 := retunedMinusLDLY2 x2 x3 x4
  let y3 := retunedMinusLDLY3 x3 x4
  have hneY : y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0 ∨ y3 ≠ 0 ∨ x4 ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    rcases hzero with ⟨hy0, hy1, hy2, hy3, hx4⟩
    have hx3 : x3 = 0 := by
      dsimp only [y3, retunedMinusLDLY3] at hy3
      rw [hx4] at hy3
      simpa using hy3
    have hx2 : x2 = 0 := by
      dsimp only [y2, retunedMinusLDLY2] at hy2
      rw [hx4, hx3] at hy2
      simpa using hy2
    have hx1 : x1 = 0 := by
      dsimp only [y1, retunedMinusLDLY1] at hy1
      rw [hx4, hx3, hx2] at hy1
      simpa using hy1
    have hx0 : x0 = 0 := by
      dsimp only [y0, retunedMinusLDLY0] at hy0
      rw [hx4, hx3, hx2] at hy0
      simpa using hy0
    rcases hne with h0 | h1 | h2 | h3 | h4
    · exact h0 hx0
    · exact h1 hx1
    · exact h2 hx2
    · exact h3 hx3
    · exact h4 hx4
  rw [retunedMinusReserveQuadratic_eq_ldl]
  dsimp only [y0, y1, y2, y3] at hneY
  rcases hneY with h0 | h1 | h2 | h3 | h4
  all_goals positivity

set_option maxHeartbeats 800000 in
private theorem retunedMinusLowerFive_pos
    (s d p u v : ℝ)
    (hne : s ≠ 0 ∨ d ≠ 0 ∨ p ≠ 0 ∨ u ≠ 0 ∨ v ≠ 0) :
    0 < retunedMinusLowerFiveQuadratic s d p u v := by
  let x4 : ℝ := v
  let x3 : ℝ := d + (11 / 4 : ℝ) * x4
  let x2 : ℝ := u + (1 / 14 : ℝ) * x3 - (7 / 80 : ℝ) * x4
  let x1 : ℝ := p + (4 / 35 : ℝ) * x2 - (9 / 50 : ℝ) * x3 +
    (3 / 8 : ℝ) * x4
  let x0 : ℝ := s + (2 / 15 : ℝ) * x1 + (1 / 6 : ℝ) * x2 +
    (1 / 20 : ℝ) * x3 - (4 / 25 : ℝ) * x4
  have hneX : x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0 ∨ x4 ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    rcases hzero with ⟨hx0, hx1, hx2, hx3, hx4⟩
    have hv : v = 0 := by simpa only [x4] using hx4
    have hd : d = 0 := by
      dsimp only [x3, x4] at hx3
      nlinarith
    have hu : u = 0 := by
      dsimp only [x2] at hx2
      nlinarith
    have hp : p = 0 := by
      dsimp only [x1] at hx1
      nlinarith
    have hs : s = 0 := by
      dsimp only [x0] at hx0
      nlinarith
    rcases hne with hs' | hd' | hp' | hu' | hv'
    · exact hs' hs
    · exact hd' hd
    · exact hp' hp
    · exact hu' hu
    · exact hv' hv
  have hreserve :=
    factorTwoIntrinsicSixUnbalancedMinorMinusLowerFive_transformed_reserve
      x0 x1 x2 x3 x4
  have hperturb := retunedMinusReserveQuadratic_pos x0 x1 x2 x3 x4 hneX
  have hsMap : retunedMinusMapS x0 x1 x2 x3 x4 = s := by
    dsimp only [retunedMinusMapS, x0]
    ring
  have hdMap : retunedMinusMapD x3 x4 = d := by
    dsimp only [retunedMinusMapD, x3]
    ring
  have hpMap : retunedMinusMapP x1 x2 x3 x4 = p := by
    dsimp only [retunedMinusMapP, x1]
    ring
  have huMap : retunedMinusMapU x2 x3 x4 = u := by
    dsimp only [retunedMinusMapU, x2]
    ring
  rw [retunedMinusLowerFive_eq_old_add_perturbation]
  unfold retunedMinusReserveQuadratic at hperturb
  rw [hsMap, hdMap, hpMap, huMap] at hperturb
  dsimp only [x4] at hperturb
  change
    (8653 / 6250 : ℝ) * x0 ^ 2 +
        (24687 / 80000 : ℝ) * x1 ^ 2 +
        (6447 / 80000 : ℝ) * x2 ^ 2 +
        (2153 / 1500000 : ℝ) * x3 ^ 2 +
        (517 / 800000 : ℝ) * x4 ^ 2 ≤
      factorTwoIntrinsicSixUnbalancedMinorMinusLowerFiveQuadratic
        (retunedMinusMapS x0 x1 x2 x3 x4)
        (retunedMinusMapD x3 x4)
        (retunedMinusMapP x1 x2 x3 x4)
        (retunedMinusMapU x2 x3 x4) x4 at hreserve
  rw [hsMap, hdMap, hpMap, huMap] at hreserve
  dsimp only [x4] at hreserve
  nlinarith

/-! ## Comparison with the exact endpoint form -/

private def retunedMinusExactFiveQuadratic
    (c0 c2 c4 c1 c3 : ℝ) : ℝ :=
  symmetricQuadratic
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus04
      factorTwoIntrinsicSixUnbalancedEMinus22
      factorTwoIntrinsicSixUnbalancedEMinus24
      factorTwoIntrinsicSixUnbalancedEMinus44 c0 c2 c4 +
    2 * (c0 * factorTwoIntrinsicNineRetunedKMinus 0 0 +
      c2 * factorTwoIntrinsicNineRetunedKMinus 1 0 +
      c4 * factorTwoIntrinsicNineRetunedKMinus 2 0) * c1 +
    2 * (c0 * factorTwoIntrinsicNineRetunedKMinus 0 1 +
      c2 * factorTwoIntrinsicNineRetunedKMinus 1 1 +
      c4 * factorTwoIntrinsicNineRetunedKMinus 2 1) * c3 +
    factorTwoIntrinsicSixUnbalancedOPlus11 * c1 ^ 2 +
    2 * factorTwoIntrinsicSixUnbalancedOPlus13 * c1 * c3 +
    factorTwoIntrinsicSixUnbalancedOPlus33 * c3 ^ 2

private theorem retunedMinusLowerFive_le_exact
    (s d p u v : ℝ) :
    retunedMinusLowerFiveQuadratic s d p u v ≤
      retunedMinusExactFiveQuadratic (s + d) (s - d) p (u - v) v := by
  have hEven :=
    factorTwoIntrinsicSixUnbalancedMinorMinusEvenLower_le_exact
      (s + d) (s - d) p
  have hOdd := intrinsicStaticMinusOddLower_le (u - v) v
  have hOdd' :
      intrinsicStaticMinusOddLower (u - v) v ≤
        factorTwoIntrinsicSixUnbalancedOPlus11 * (u - v) ^ 2 +
          2 * factorTwoIntrinsicSixUnbalancedOPlus13 * (u - v) * v +
          factorTwoIntrinsicSixUnbalancedOPlus33 * v ^ 2 := by
    simpa only [factorTwoIntrinsicStaticOddQuadratic,
      factorTwoIntrinsicOddPhaseQuadratic,
      factorTwoIntrinsicSixUnbalancedOPlus11,
      factorTwoIntrinsicSixUnbalancedOPlus13,
      factorTwoIntrinsicSixUnbalancedOPlus33, neg_neg, one_mul] using hOdd
  unfold retunedMinusLowerFiveQuadratic retunedMinusExactFiveQuadratic
  nlinarith

private theorem retunedMinusExactFive_pos
    (c0 c2 c4 c1 c3 : ℝ)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨ c1 ≠ 0 ∨ c3 ≠ 0) :
    0 < retunedMinusExactFiveQuadratic c0 c2 c4 c1 c3 := by
  let s : ℝ := (c0 + c2) / 2
  let d : ℝ := (c0 - c2) / 2
  let u : ℝ := c1 + c3
  have hneAligned : s ≠ 0 ∨ d ≠ 0 ∨ c4 ≠ 0 ∨ u ≠ 0 ∨ c3 ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    rcases hzero with ⟨hs, hd, hp, hu, hv⟩
    have hc0 : c0 = 0 := by
      dsimp only [s, d] at hs hd
      nlinarith
    have hc2 : c2 = 0 := by
      dsimp only [s, d] at hs hd
      nlinarith
    have hc1 : c1 = 0 := by
      dsimp only [u] at hu
      nlinarith
    rcases hne with h0 | h2 | h4 | h1 | h3
    · exact h0 hc0
    · exact h2 hc2
    · exact h4 hp
    · exact h1 hc1
    · exact h3 hv
  have hlow := retunedMinusLowerFive_pos s d c4 u c3 hneAligned
  have hle := retunedMinusLowerFive_le_exact s d c4 u c3
  have hsMap : s + d = c0 := by
    dsimp only [s, d]
    ring
  have hdMap : s - d = c2 := by
    dsimp only [s, d]
    ring
  have huMap : u - c3 = c1 := by
    dsimp only [u]
    ring
  rw [hsMap, hdMap, huMap] at hle
  exact hlow.trans_le hle

/-! ## Adjugate extraction of the first two Schur gates -/

private def retunedMinusEll0 (c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicNineRetunedKMinus 0 0 * c1 +
    factorTwoIntrinsicNineRetunedKMinus 0 1 * c3

private def retunedMinusEll2 (c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicNineRetunedKMinus 1 0 * c1 +
    factorTwoIntrinsicNineRetunedKMinus 1 1 * c3

private def retunedMinusEll4 (c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicNineRetunedKMinus 2 0 * c1 +
    factorTwoIntrinsicNineRetunedKMinus 2 1 * c3

private def retunedMinusT00 : ℝ :=
  factorTwoIntrinsicSixUnbalancedEMinusDet *
      factorTwoIntrinsicSixUnbalancedOPlus11 -
    unbalancedThreeAdjugatePair
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus04
      factorTwoIntrinsicSixUnbalancedEMinus22
      factorTwoIntrinsicSixUnbalancedEMinus24
      factorTwoIntrinsicSixUnbalancedEMinus44
      (factorTwoIntrinsicNineRetunedKMinus 0 0)
      (factorTwoIntrinsicNineRetunedKMinus 1 0)
      (factorTwoIntrinsicNineRetunedKMinus 2 0)
      (factorTwoIntrinsicNineRetunedKMinus 0 0)
      (factorTwoIntrinsicNineRetunedKMinus 1 0)
      (factorTwoIntrinsicNineRetunedKMinus 2 0)

private def retunedMinusT01 : ℝ :=
  factorTwoIntrinsicSixUnbalancedEMinusDet *
      factorTwoIntrinsicSixUnbalancedOPlus13 -
    unbalancedThreeAdjugatePair
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus04
      factorTwoIntrinsicSixUnbalancedEMinus22
      factorTwoIntrinsicSixUnbalancedEMinus24
      factorTwoIntrinsicSixUnbalancedEMinus44
      (factorTwoIntrinsicNineRetunedKMinus 0 0)
      (factorTwoIntrinsicNineRetunedKMinus 1 0)
      (factorTwoIntrinsicNineRetunedKMinus 2 0)
      (factorTwoIntrinsicNineRetunedKMinus 0 1)
      (factorTwoIntrinsicNineRetunedKMinus 1 1)
      (factorTwoIntrinsicNineRetunedKMinus 2 1)

private def retunedMinusT11 : ℝ :=
  factorTwoIntrinsicSixUnbalancedEMinusDet *
      factorTwoIntrinsicSixUnbalancedOPlus33 -
    unbalancedThreeAdjugatePair
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus04
      factorTwoIntrinsicSixUnbalancedEMinus22
      factorTwoIntrinsicSixUnbalancedEMinus24
      factorTwoIntrinsicSixUnbalancedEMinus44
      (factorTwoIntrinsicNineRetunedKMinus 0 1)
      (factorTwoIntrinsicNineRetunedKMinus 1 1)
      (factorTwoIntrinsicNineRetunedKMinus 2 1)
      (factorTwoIntrinsicNineRetunedKMinus 0 1)
      (factorTwoIntrinsicNineRetunedKMinus 1 1)
      (factorTwoIntrinsicNineRetunedKMinus 2 1)

private theorem retunedT00_eq_target :
    retunedMinusT00 = factorTwoIntrinsicNineRetunedTMinus 0 0 := by
  rfl

private theorem retunedT01_eq_target :
    retunedMinusT01 = factorTwoIntrinsicNineRetunedTMinus 0 1 := by
  rfl

private theorem retunedT11_eq_target :
    retunedMinusT11 = factorTwoIntrinsicNineRetunedTMinus 1 1 := by
  rfl

private theorem retunedMinusExactFive_adjugate_specialization
    (c1 c3 : ℝ) :
    retunedMinusExactFiveQuadratic
        (-adjugateVector
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44
          (retunedMinusEll0 c1 c3)
          (retunedMinusEll2 c1 c3)
          (retunedMinusEll4 c1 c3) 0)
        (-adjugateVector
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44
          (retunedMinusEll0 c1 c3)
          (retunedMinusEll2 c1 c3)
          (retunedMinusEll4 c1 c3) 1)
        (-adjugateVector
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44
          (retunedMinusEll0 c1 c3)
          (retunedMinusEll2 c1 c3)
          (retunedMinusEll4 c1 c3) 2)
        (factorTwoIntrinsicSixUnbalancedEMinusDet * c1)
        (factorTwoIntrinsicSixUnbalancedEMinusDet * c3) =
      factorTwoIntrinsicSixUnbalancedEMinusDet *
        (retunedMinusT00 * c1 ^ 2 +
          2 * retunedMinusT01 * c1 * c3 +
          retunedMinusT11 * c3 ^ 2) := by
  unfold retunedMinusExactFiveQuadratic retunedMinusEll0 retunedMinusEll2
    retunedMinusEll4 retunedMinusT00 retunedMinusT01 retunedMinusT11
    factorTwoIntrinsicSixUnbalancedEMinusDet
  simp only [adjugateVector]
  unfold symmetricQuadratic symmetricDeterminant unbalancedThreeAdjugatePair
  ring

private theorem retunedMinusTLowQuadratic_pos
    (c1 c3 : ℝ) (hne : c1 ≠ 0 ∨ c3 ≠ 0) :
    0 < retunedMinusT00 * c1 ^ 2 +
      2 * retunedMinusT01 * c1 * c3 + retunedMinusT11 * c3 ^ 2 := by
  have hd : 0 < factorTwoIntrinsicSixUnbalancedEMinusDet := by
    rcases factorTwoIntrinsicSixUnbalancedEMinus_positive with
      ⟨_he00, _heMinor, hdet⟩
    simpa only [factorTwoIntrinsicSixUnbalancedEMinusDet] using hdet
  let v0 := adjugateVector
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    (retunedMinusEll0 c1 c3) (retunedMinusEll2 c1 c3)
    (retunedMinusEll4 c1 c3) 0
  let v2 := adjugateVector
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    (retunedMinusEll0 c1 c3) (retunedMinusEll2 c1 c3)
    (retunedMinusEll4 c1 c3) 1
  let v4 := adjugateVector
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    (retunedMinusEll0 c1 c3) (retunedMinusEll2 c1 c3)
    (retunedMinusEll4 c1 c3) 2
  have hneExact :
      -v0 ≠ 0 ∨ -v2 ≠ 0 ∨ -v4 ≠ 0 ∨
        factorTwoIntrinsicSixUnbalancedEMinusDet * c1 ≠ 0 ∨
        factorTwoIntrinsicSixUnbalancedEMinusDet * c3 ≠ 0 := by
    rcases hne with h1 | h3
    · exact Or.inr (Or.inr (Or.inr (Or.inl (mul_ne_zero hd.ne' h1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (mul_ne_zero hd.ne' h3))))
  have hquad := retunedMinusExactFive_pos
    (-v0) (-v2) (-v4)
    (factorTwoIntrinsicSixUnbalancedEMinusDet * c1)
    (factorTwoIntrinsicSixUnbalancedEMinusDet * c3) hneExact
  have hid := retunedMinusExactFive_adjugate_specialization c1 c3
  dsimp only [v0, v2, v4] at hquad
  rw [hid] at hquad
  rcases mul_pos_iff.mp hquad with hpos | hneg
  · exact hpos.2
  · exact False.elim ((not_lt_of_ge hd.le) hneg.1)

/-- The first retuned negative fraction-free Schur gate is unconditional. -/
theorem factorTwoIntrinsicNineRetunedTMinus00_pos :
    0 < factorTwoIntrinsicNineRetunedTMinus 0 0 := by
  have h := retunedMinusTLowQuadratic_pos 1 0 (Or.inl (by norm_num))
  rw [retunedT00_eq_target] at h
  simpa using h

/-- The leading `2 × 2` retuned negative Schur minor is unconditional. -/
theorem factorTwoIntrinsicNineRetunedTMinusMinor_pos :
    0 < leadingMinorTwo
      (factorTwoIntrinsicNineRetunedTMinus 0 0)
      (factorTwoIntrinsicNineRetunedTMinus 0 1)
      (factorTwoIntrinsicNineRetunedTMinus 1 1) := by
  have h00 : 0 < retunedMinusT00 := by
    rw [retunedT00_eq_target]
    exact factorTwoIntrinsicNineRetunedTMinus00_pos
  have hquad := retunedMinusTLowQuadratic_pos
    (-retunedMinusT01) retunedMinusT00 (Or.inr h00.ne')
  have hid :
      retunedMinusT00 * (-retunedMinusT01) ^ 2 +
          2 * retunedMinusT01 * (-retunedMinusT01) * retunedMinusT00 +
          retunedMinusT11 * retunedMinusT00 ^ 2 =
        retunedMinusT00 *
          leadingMinorTwo retunedMinusT00 retunedMinusT01 retunedMinusT11 := by
    unfold leadingMinorTwo
    ring
  rw [hid] at hquad
  have hminor :
      0 < leadingMinorTwo retunedMinusT00 retunedMinusT01 retunedMinusT11 := by
    rcases mul_pos_iff.mp hquad with hpos | hneg
    · exact hpos.2
    · exact False.elim ((not_lt_of_ge h00.le) hneg.1)
  simpa only [retunedT00_eq_target, retunedT01_eq_target,
    retunedT11_eq_target] using hminor

/-- The low-mode portion of the retuned negative gate package. -/
theorem factorTwoIntrinsicNineRetunedMinus_firstTwoGates :
    0 < factorTwoIntrinsicNineRetunedTMinus 0 0 ∧
      0 < leadingMinorTwo
        (factorTwoIntrinsicNineRetunedTMinus 0 0)
        (factorTwoIntrinsicNineRetunedTMinus 0 1)
        (factorTwoIntrinsicNineRetunedTMinus 1 1) :=
  ⟨factorTwoIntrinsicNineRetunedTMinus00_pos,
    factorTwoIntrinsicNineRetunedTMinusMinor_pos⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineRetunedMinusGatesPositive
