import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineStaticFinalThreePositiveStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineRetunedPlusGatesPositive

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicNineStaticFinalThreePositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

/-!
# The first two retuned positive Schur gates

The first two gates only see the modes `P₀, ..., P₅`.  Changing the old
six-mode transfer to the first two columns of the cutoff-nine transfer adds
an exact rational quadratic to the public correlated five-variable lower
form.  We carry that correction through the existing congruence and prove
the resulting rational comparison positive by one weighted SOS.
-/

/-! ## The exact transfer correction -/

private def retunedPlusDeltaFive
    (c0 c2 c4 c1 c3 : ℝ) : ℝ :=
  2 * (c0 * ((639 / 100000 : ℝ) * c1 - (1533 / 100000) * c3) +
    c2 * ((333 / 100000 : ℝ) * c1 - (1494 / 100000) * c3) +
    c4 * (-(874 / 100000 : ℝ) * c1 + (133 / 100000) * c3))

private def retunedPlusExactFive
    (c0 c2 c4 c1 c3 : ℝ) : ℝ :=
  symmetricQuadratic
      (factorTwoIntrinsicNineRetunedEPlus 0 0)
      (factorTwoIntrinsicNineRetunedEPlus 0 1)
      (factorTwoIntrinsicNineRetunedEPlus 0 2)
      (factorTwoIntrinsicNineRetunedEPlus 1 1)
      (factorTwoIntrinsicNineRetunedEPlus 1 2)
      (factorTwoIntrinsicNineRetunedEPlus 2 2) c0 c2 c4 +
    2 * (c0 * (factorTwoIntrinsicNineRetunedBPlus 0 0 * c1 +
        factorTwoIntrinsicNineRetunedBPlus 1 0 * c3) +
      c2 * (factorTwoIntrinsicNineRetunedBPlus 0 1 * c1 +
        factorTwoIntrinsicNineRetunedBPlus 1 1 * c3) +
      c4 * (factorTwoIntrinsicNineRetunedBPlus 0 2 * c1 +
        factorTwoIntrinsicNineRetunedBPlus 1 2 * c3)) +
    factorTwoIntrinsicNineRetunedOPlus 0 0 * c1 ^ 2 +
    2 * factorTwoIntrinsicNineRetunedOPlus 0 1 * c1 * c3 +
    factorTwoIntrinsicNineRetunedOPlus 1 1 * c3 ^ 2

private theorem oldExactFive_eq_block
    (c0 c2 c4 c1 c3 : ℝ) :
    factorTwoIntrinsicSixUnbalancedMinorPlusExactFiveQuadratic
        c0 c2 c4 c1 c3 =
      symmetricQuadratic
          factorTwoIntrinsicSixUnbalancedEPlus00
          factorTwoIntrinsicSixUnbalancedEPlus02
          factorTwoIntrinsicSixUnbalancedEPlus04
          factorTwoIntrinsicSixUnbalancedEPlus22
          factorTwoIntrinsicSixUnbalancedEPlus24
          factorTwoIntrinsicSixUnbalancedEPlus44 c0 c2 c4 +
        2 * (c0 * factorTwoIntrinsicSixUnbalancedKPlus01 +
          c2 * factorTwoIntrinsicSixUnbalancedKPlus21 +
          c4 * factorTwoIntrinsicSixUnbalancedKPlus41) * c1 +
        2 * (c0 * factorTwoIntrinsicSixUnbalancedKPlus03 +
          c2 * factorTwoIntrinsicSixUnbalancedKPlus23 +
          c4 * factorTwoIntrinsicSixUnbalancedKPlus43) * c3 +
        factorTwoIntrinsicSixUnbalancedOMinus11 * c1 ^ 2 +
        2 * factorTwoIntrinsicSixUnbalancedOMinus13 * c1 * c3 +
        factorTwoIntrinsicSixUnbalancedOMinus33 * c3 ^ 2 := by
  have h :=
    factorTwoIntrinsicSixUnbalancedMinorPlusExactSixQuadratic_eq_staticPlus
      c0 c2 c4 c1 c3 0
  rw [factorTwoIntrinsicSixUnbalancedStaticPlus_eq_block] at h
  unfold factorTwoIntrinsicSixUnbalancedMinorPlusExactSixQuadratic at h
  simp only [mul_zero, add_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), symmetricQuadratic] at h
  rw [h]
  unfold symmetricQuadratic
  ring

private theorem retunedPlusExactFive_eq_old_add_delta
    (c0 c2 c4 c1 c3 : ℝ) :
    retunedPlusExactFive c0 c2 c4 c1 c3 =
      factorTwoIntrinsicSixUnbalancedMinorPlusExactFiveQuadratic
          c0 c2 c4 c1 c3 +
        retunedPlusDeltaFive c0 c2 c4 c1 c3 := by
  unfold retunedPlusExactFive retunedPlusDeltaFive
    factorTwoIntrinsicNineRetunedEPlus factorTwoIntrinsicNineRetunedOPlus
  rw [oldExactFive_eq_block]
  simp [factorTwoIntrinsicNineRetunedBPlus,
    factorTwoIntrinsicNineRetunedKPlus,
    factorTwoIntrinsicNineRetunedEvenBasis,
    factorTwoIntrinsicNineRetunedOddBasis,
    factorTwoIntrinsicNineRetunedH]
  unfold factorTwoIntrinsicSixUnbalancedKPlus01
    factorTwoIntrinsicSixUnbalancedKPlus03
    factorTwoIntrinsicSixUnbalancedKPlus21
    factorTwoIntrinsicSixUnbalancedKPlus23
    factorTwoIntrinsicSixUnbalancedKPlus41
    factorTwoIntrinsicSixUnbalancedKPlus43
  unfold factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating03
    factorTwoIntrinsicAlternating21 factorTwoIntrinsicAlternating23
    factorTwoIntrinsicFourP45Cross41 factorTwoIntrinsicFourP45Cross43
  ring

/-! ## Transport through the correlated five-variable congruence -/

private def retunedPlusTransformedDeltaFive
    (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  2 * (243 / 25000 : ℝ) * x0 * x3 -
    2 * (39963 / 1000000 : ℝ) * x0 * x4 +
    2 * (76257 / 25000000 : ℝ) * x1 * x3 -
    2 * (3401537 / 1000000000 : ℝ) * x1 * x4 -
    2 * (669 / 250000 : ℝ) * x2 * x3 +
    2 * (135479 / 10000000 : ℝ) * x2 * x4 -
    (35901 / 2500000 : ℝ) * x3 ^ 2 +
    2 * (245297819 / 32300000000 : ℝ) * x3 * x4 +
    (573840143 / 5472000000 : ℝ) * x4 ^ 2

private theorem retunedPlusDeltaFive_congruence
    (x0 x1 x2 x3 x4 : ℝ) :
    retunedPlusDeltaFive
        ((x0 - x1 / 1000 - (16 / 45 : ℝ) * x2 -
            (27 / 40 : ℝ) * x3 - x4) +
          (x1 + (28 / 9 : ℝ) * x2 + (49 / 17 : ℝ) * x3 +
            (75 / 19 : ℝ) * x4))
        ((x0 - x1 / 1000 - (16 / 45 : ℝ) * x2 -
            (27 / 40 : ℝ) * x3 - x4) -
          (x1 + (28 / 9 : ℝ) * x2 + (49 / 17 : ℝ) * x3 +
            (75 / 19 : ℝ) * x4))
        (x2 + (27 / 25 : ℝ) * x3 + (83 / 32 : ℝ) * x4)
        ((x3 + (2 / 45 : ℝ) * x4) - (25 / 24 : ℝ) * x4) x4 =
      retunedPlusTransformedDeltaFive x0 x1 x2 x3 x4 := by
  unfold retunedPlusDeltaFive retunedPlusTransformedDeltaFive
  ring

/-! ## A rational absolute comparison and its weighted SOS -/

private def oldPlusFiveComparison
    (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  (27 / 50 : ℝ) * x0 ^ 2 + (63 / 10000 : ℝ) * x1 ^ 2 +
    (397 / 50000 : ℝ) * x2 ^ 2 + (12 / 125 : ℝ) * x3 ^ 2 +
    (149 / 50000 : ℝ) * x4 ^ 2 -
    2 * (41 / 500000 : ℝ) * |x0 * x1| -
    2 * (51 / 100000 : ℝ) * |x0 * x2| -
    2 * (237 / 500000 : ℝ) * |x0 * x3| -
    2 * (5891 / 1000000 : ℝ) * |x0 * x4| -
    2 * (79 / 500000 : ℝ) * |x1 * x2| -
    2 * (41 / 250000 : ℝ) * |x1 * x3| -
    2 * (107 / 250000 : ℝ) * |x1 * x4| -
    2 * (1893 / 1000000 : ℝ) * |x2 * x3| -
    2 * (1813 / 500000 : ℝ) * |x2 * x4| -
    2 * (897 / 100000 : ℝ) * |x3 * x4|

private def retunedPlusFiveComparison
    (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  (27 / 50 : ℝ) * x0 ^ 2 + (63 / 10000 : ℝ) * x1 ^ 2 +
    (397 / 50000 : ℝ) * x2 ^ 2 +
    (204099 / 2500000 : ℝ) * x3 ^ 2 +
    (590146703 / 5472000000 : ℝ) * x4 ^ 2 -
    2 * (41 / 500000 : ℝ) * |x0 * x1| -
    2 * (51 / 100000 : ℝ) * |x0 * x2| -
    2 * (5097 / 500000 : ℝ) * |x0 * x3| -
    2 * (22927 / 500000 : ℝ) * |x0 * x4| -
    2 * (79 / 500000 : ℝ) * |x1 * x2| -
    2 * (80357 / 25000000 : ℝ) * |x1 * x3| -
    2 * (3829537 / 1000000000 : ℝ) * |x1 * x4| -
    2 * (4569 / 1000000 : ℝ) * |x2 * x3| -
    2 * (171739 / 10000000 : ℝ) * |x2 * x4| -
    2 * (535028819 / 32300000000 : ℝ) * |x3 * x4|

private theorem cross_lower_of_abs
    (a x y : ℝ) :
    -2 * |a| * |x * y| ≤ 2 * a * x * y := by
  have hneg := mul_le_mul_of_nonneg_left (neg_abs_le (a * x * y))
    (by norm_num : (0 : ℝ) ≤ 2)
  calc
    -2 * |a| * |x * y| = 2 * (-|a * x * y|) := by
      simp only [abs_mul]
      ring
    _ ≤ 2 * (a * x * y) := hneg
    _ = 2 * a * x * y := by ring

private theorem retunedPlusFiveComparison_le_old_add_delta
    (x0 x1 x2 x3 x4 : ℝ) :
    retunedPlusFiveComparison x0 x1 x2 x3 x4 ≤
      oldPlusFiveComparison x0 x1 x2 x3 x4 +
        retunedPlusTransformedDeltaFive x0 x1 x2 x3 x4 := by
  have h03 := cross_lower_of_abs (243 / 25000 : ℝ) x0 x3
  have h04 := cross_lower_of_abs (-39963 / 1000000 : ℝ) x0 x4
  have h13 := cross_lower_of_abs (76257 / 25000000 : ℝ) x1 x3
  have h14 := cross_lower_of_abs (-3401537 / 1000000000 : ℝ) x1 x4
  have h23 := cross_lower_of_abs (-669 / 250000 : ℝ) x2 x3
  have h24 := cross_lower_of_abs (135479 / 10000000 : ℝ) x2 x4
  have h34 := cross_lower_of_abs
    (245297819 / 32300000000 : ℝ) x3 x4
  unfold retunedPlusFiveComparison
    oldPlusFiveComparison
    retunedPlusTransformedDeltaFive
  norm_num at h03 h04 h13 h14 h23 h24 h34
  simp only [abs_mul] at *
  linarith

private def retunedPlusFiveComparisonSOS
    (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  (23421 / 500000 : ℝ) * x0 ^ 2 +
    (30664829 / 8000000000 : ℝ) * x1 ^ 2 +
    (836789 / 340000000 : ℝ) * x2 ^ 2 +
    (1055947751 / 64600000000 : ℝ) * x3 ^ 2 +
    (193250096819 / 11628000000000 : ℝ) * x4 ^ 2 +
    ((41 / 500000 : ℝ) / 24) * (24 * |x0| - |x1|) ^ 2 +
    ((51 / 100000 : ℝ) / 34) * (34 * |x0| - |x2|) ^ 2 +
    ((5097 / 500000 : ℝ) / 6) * (6 * |x0| - |x3|) ^ 2 +
    ((22927 / 500000 : ℝ) / 9) * (9 * |x0| - |x4|) ^ 2 +
    ((79 / 500000 : ℝ) / (24 * 34)) *
      (34 * |x1| - 24 * |x2|) ^ 2 +
    ((80357 / 25000000 : ℝ) / (24 * 6)) *
      (6 * |x1| - 24 * |x3|) ^ 2 +
    ((3829537 / 1000000000 : ℝ) / (24 * 9)) *
      (9 * |x1| - 24 * |x4|) ^ 2 +
    ((4569 / 1000000 : ℝ) / (34 * 6)) *
      (6 * |x2| - 34 * |x3|) ^ 2 +
    ((171739 / 10000000 : ℝ) / (34 * 9)) *
      (9 * |x2| - 34 * |x4|) ^ 2 +
    ((535028819 / 32300000000 : ℝ) / (6 * 9)) *
      (9 * |x3| - 6 * |x4|) ^ 2

set_option maxHeartbeats 800000 in
private theorem retunedPlusFiveComparison_eq_sos
    (x0 x1 x2 x3 x4 : ℝ) :
    retunedPlusFiveComparison x0 x1 x2 x3 x4 =
      retunedPlusFiveComparisonSOS x0 x1 x2 x3 x4 := by
  unfold retunedPlusFiveComparison retunedPlusFiveComparisonSOS
  simp only [abs_mul]
  ring_nf
  simp only [sq_abs]
  ring

private theorem retunedPlusFiveComparison_pos
    (x0 x1 x2 x3 x4 : ℝ)
    (hne : x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0 ∨ x4 ≠ 0) :
    0 < retunedPlusFiveComparison x0 x1 x2 x3 x4 := by
  rw [retunedPlusFiveComparison_eq_sos]
  unfold retunedPlusFiveComparisonSOS
  rcases hne with h0 | h1 | h2 | h3 | h4
  all_goals positivity

/-! ## Strict positivity of the retuned exact five-variable form -/

private theorem retunedPlusExactFive_pos
    (c0 c2 c4 c1 c3 : ℝ)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨ c1 ≠ 0 ∨ c3 ≠ 0) :
    0 < retunedPlusExactFive c0 c2 c4 c1 c3 := by
  let s : ℝ := (c0 + c2) / 2
  let d : ℝ := (c0 - c2) / 2
  let v : ℝ := c3
  let u : ℝ := c1 + (25 / 24 : ℝ) * v
  let x4 : ℝ := v
  let x3 : ℝ := u - (2 / 45 : ℝ) * x4
  let x2 : ℝ := c4 - (27 / 25 : ℝ) * x3 - (83 / 32 : ℝ) * x4
  let x1 : ℝ := d - (28 / 9 : ℝ) * x2 - (49 / 17 : ℝ) * x3 -
    (75 / 19 : ℝ) * x4
  let x0 : ℝ := s + x1 / 1000 + (16 / 45 : ℝ) * x2 +
    (27 / 40 : ℝ) * x3 + x4
  have hs :
      x0 - x1 / 1000 - (16 / 45 : ℝ) * x2 -
          (27 / 40 : ℝ) * x3 - x4 = s := by
    dsimp only [x0]
    ring
  have hd :
      x1 + (28 / 9 : ℝ) * x2 + (49 / 17 : ℝ) * x3 +
          (75 / 19 : ℝ) * x4 = d := by
    dsimp only [x1]
    ring
  have hp : x2 + (27 / 25 : ℝ) * x3 + (83 / 32 : ℝ) * x4 = c4 := by
    dsimp only [x2]
    ring
  have hu : x3 + (2 / 45 : ℝ) * x4 = u := by
    dsimp only [x3]
    ring
  have hv : x4 = v := by rfl
  have hc0 : s + d = c0 := by
    dsimp only [s, d]
    ring
  have hc2 : s - d = c2 := by
    dsimp only [s, d]
    ring
  have hc1 : u - (25 / 24 : ℝ) * v = c1 := by
    dsimp only [u]
    ring
  have hneX : x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0 ∨ x4 ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    rcases hzero with ⟨hx0, hx1, hx2, hx3, hx4⟩
    have hs0 : s = 0 := by rw [← hs, hx0, hx1, hx2, hx3, hx4]; norm_num
    have hd0 : d = 0 := by rw [← hd, hx1, hx2, hx3, hx4]; norm_num
    have hc40 : c4 = 0 := by rw [← hp, hx2, hx3, hx4]; norm_num
    have hu0 : u = 0 := by rw [← hu, hx3, hx4]; norm_num
    have hv0 : v = 0 := by simpa only [← hv] using hx4
    have hc00 : c0 = 0 := by rw [← hc0, hs0, hd0]; norm_num
    have hc20 : c2 = 0 := by rw [← hc2, hs0, hd0]; norm_num
    have hc10 : c1 = 0 := by rw [← hc1, hu0, hv0]; norm_num
    rcases hne with h0 | h2 | h4 | h1 | h3
    · exact h0 hc00
    · exact h2 hc20
    · exact h4 hc40
    · exact h1 hc10
    · exact h3 (by simpa only [v] using hv0)
  have hbase := retunedPlusFiveComparison_pos x0 x1 x2 x3 x4 hneX
  have hdelta := retunedPlusFiveComparison_le_old_add_delta
    x0 x1 x2 x3 x4
  have hold :=
    factorTwoIntrinsicSixUnbalancedMinorPlusAbsoluteComparison_le_exact_congruence
      x0 x1 x2 x3 x4
  change oldPlusFiveComparison x0 x1 x2 x3 x4 ≤ _ at hold
  rw [hs, hd, hp, hu, hv] at hold
  have hdeltaEq := retunedPlusDeltaFive_congruence x0 x1 x2 x3 x4
  rw [hs, hd, hp, hu, hv] at hdeltaEq
  have hdelta' :
      retunedPlusFiveComparison x0 x1 x2 x3 x4 ≤
        oldPlusFiveComparison x0 x1 x2 x3 x4 +
          retunedPlusDeltaFive (s + d) (s - d) c4
            (u - (25 / 24 : ℝ) * v) v := by
    rw [hdeltaEq]
    exact hdelta
  have hadd :
      oldPlusFiveComparison x0 x1 x2 x3 x4 +
          retunedPlusDeltaFive (s + d) (s - d) c4
            (u - (25 / 24 : ℝ) * v) v ≤
        factorTwoIntrinsicSixUnbalancedMinorPlusExactFiveQuadratic
            (s + d) (s - d) c4 (u - (25 / 24 : ℝ) * v) v +
          retunedPlusDeltaFive (s + d) (s - d) c4
            (u - (25 / 24 : ℝ) * v) v := by
    simpa only [add_comm] using add_le_add_right hold
      (retunedPlusDeltaFive (s + d) (s - d) c4
        (u - (25 / 24 : ℝ) * v) v)
  have hretuned := hbase.trans_le (hdelta'.trans hadd)
  rw [hc0, hc2, hc1] at hretuned
  dsimp only [v] at hretuned
  rw [retunedPlusExactFive_eq_old_add_delta]
  exact hretuned

/-! ## Adjugate specialization and the first two Sylvester gates -/

private def retunedPlusEll0 (y1 y3 : ℝ) : ℝ :=
  factorTwoIntrinsicNineRetunedBPlus 0 0 * y1 +
    factorTwoIntrinsicNineRetunedBPlus 1 0 * y3

private def retunedPlusEll2 (y1 y3 : ℝ) : ℝ :=
  factorTwoIntrinsicNineRetunedBPlus 0 1 * y1 +
    factorTwoIntrinsicNineRetunedBPlus 1 1 * y3

private def retunedPlusEll4 (y1 y3 : ℝ) : ℝ :=
  factorTwoIntrinsicNineRetunedBPlus 0 2 * y1 +
    factorTwoIntrinsicNineRetunedBPlus 1 2 * y3

private def retunedPlusAdjugateVector (y1 y3 : ℝ) : Fin 3 → ℝ :=
  adjugateVector
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    (retunedPlusEll0 y1 y3) (retunedPlusEll2 y1 y3)
    (retunedPlusEll4 y1 y3)

private def retunedTPlusTwoQuadratic (y1 y3 : ℝ) : ℝ :=
  factorTwoIntrinsicNineRetunedTPlus 0 0 * y1 ^ 2 +
    2 * factorTwoIntrinsicNineRetunedTPlus 0 1 * y1 * y3 +
    factorTwoIntrinsicNineRetunedTPlus 1 1 * y3 ^ 2

private def retunedOPlusTwoQuadratic (y1 y3 : ℝ) : ℝ :=
  factorTwoIntrinsicNineRetunedOPlus 0 0 * y1 ^ 2 +
    2 * factorTwoIntrinsicNineRetunedOPlus 0 1 * y1 * y3 +
    factorTwoIntrinsicNineRetunedOPlus 1 1 * y3 ^ 2

private theorem retunedTPlusTwoQuadratic_eq_fractionFree
    (y1 y3 : ℝ) :
    factorTwoIntrinsicSixUnbalancedEPlusDet *
          retunedOPlusTwoQuadratic y1 y3 -
        adjugateQuadratic
          factorTwoIntrinsicSixUnbalancedEPlus00
          factorTwoIntrinsicSixUnbalancedEPlus02
          factorTwoIntrinsicSixUnbalancedEPlus04
          factorTwoIntrinsicSixUnbalancedEPlus22
          factorTwoIntrinsicSixUnbalancedEPlus24
          factorTwoIntrinsicSixUnbalancedEPlus44
          (retunedPlusEll0 y1 y3) (retunedPlusEll2 y1 y3)
          (retunedPlusEll4 y1 y3) =
      retunedTPlusTwoQuadratic y1 y3 := by
  simpa only [retunedOPlusTwoQuadratic, retunedPlusEll0,
    retunedPlusEll2, retunedPlusEll4, retunedTPlusTwoQuadratic] using
    factorTwoIntrinsicNineRetunedTPlusTwoQuadratic_eq_fractionFree y1 y3

set_option maxHeartbeats 800000 in
private theorem retunedPlusExactFive_adjugate_specialization
    (y1 y3 : ℝ) :
    retunedPlusExactFive
        (-retunedPlusAdjugateVector y1 y3 0)
        (-retunedPlusAdjugateVector y1 y3 1)
        (-retunedPlusAdjugateVector y1 y3 2)
        (factorTwoIntrinsicSixUnbalancedEPlusDet * y1)
        (factorTwoIntrinsicSixUnbalancedEPlusDet * y3) =
      factorTwoIntrinsicSixUnbalancedEPlusDet *
        retunedTPlusTwoQuadratic y1 y3 := by
  rw [← retunedTPlusTwoQuadratic_eq_fractionFree]
  unfold retunedPlusExactFive retunedPlusAdjugateVector
    retunedPlusEll0 retunedPlusEll2 retunedPlusEll4
    retunedOPlusTwoQuadratic
    factorTwoIntrinsicNineRetunedEPlus factorTwoIntrinsicNineRetunedOPlus
    factorTwoIntrinsicSixUnbalancedEPlusDet
  simp only [adjugateVector]
  unfold adjugateQuadratic symmetricQuadratic symmetricDeterminant
  ring

/-- The first retuned positive Schur gate is unconditional. -/
theorem factorTwoIntrinsicNineRetunedTPlus00_pos :
    0 < factorTwoIntrinsicNineRetunedTPlus 0 0 := by
  let d : ℝ := factorTwoIntrinsicSixUnbalancedEPlusDet
  have hd : 0 < d := by
    simpa only [d] using factorTwoIntrinsicSixUnbalancedEPlus_positive.2.2
  have hform := retunedPlusExactFive_pos
    (-retunedPlusAdjugateVector 1 0 0)
    (-retunedPlusAdjugateVector 1 0 1)
    (-retunedPlusAdjugateVector 1 0 2) d 0
    (Or.inr (Or.inr (Or.inr (Or.inl hd.ne'))))
  have hspecial := retunedPlusExactFive_adjugate_specialization 1 0
  dsimp only [d] at hform hspecial
  norm_num at hspecial
  rw [hspecial] at hform
  unfold retunedTPlusTwoQuadratic at hform
  norm_num at hform
  have hcomm :
      0 < factorTwoIntrinsicNineRetunedTPlus 0 0 * d := by
    simpa only [mul_comm] using hform
  exact pos_of_mul_pos_left hcomm hd.le

/-- The second retuned positive Schur gate is unconditional. -/
theorem factorTwoIntrinsicNineRetunedTPlusMinor_pos :
    0 < leadingMinorTwo
      (factorTwoIntrinsicNineRetunedTPlus 0 0)
      (factorTwoIntrinsicNineRetunedTPlus 0 1)
      (factorTwoIntrinsicNineRetunedTPlus 1 1) := by
  let d : ℝ := factorTwoIntrinsicSixUnbalancedEPlusDet
  let a : ℝ := factorTwoIntrinsicNineRetunedTPlus 0 0
  let b : ℝ := factorTwoIntrinsicNineRetunedTPlus 0 1
  have hd : 0 < d := by
    simpa only [d] using factorTwoIntrinsicSixUnbalancedEPlus_positive.2.2
  have ha : 0 < a := by
    simpa only [a] using factorTwoIntrinsicNineRetunedTPlus00_pos
  have hform := retunedPlusExactFive_pos
    (-retunedPlusAdjugateVector (-b) a 0)
    (-retunedPlusAdjugateVector (-b) a 1)
    (-retunedPlusAdjugateVector (-b) a 2)
    (d * (-b)) (d * a)
    (Or.inr (Or.inr (Or.inr (Or.inr (mul_ne_zero hd.ne' ha.ne')))))
  have hspecial := retunedPlusExactFive_adjugate_specialization (-b) a
  dsimp only [d, a, b] at hform hspecial
  rw [hspecial] at hform
  have hidentity :
      retunedTPlusTwoQuadratic
          (-factorTwoIntrinsicNineRetunedTPlus 0 1)
          (factorTwoIntrinsicNineRetunedTPlus 0 0) =
        factorTwoIntrinsicNineRetunedTPlus 0 0 *
          leadingMinorTwo
            (factorTwoIntrinsicNineRetunedTPlus 0 0)
            (factorTwoIntrinsicNineRetunedTPlus 0 1)
            (factorTwoIntrinsicNineRetunedTPlus 1 1) := by
    unfold retunedTPlusTwoQuadratic leadingMinorTwo
    ring
  rw [hidentity] at hform
  have hda : 0 < d * factorTwoIntrinsicNineRetunedTPlus 0 0 :=
    mul_pos hd factorTwoIntrinsicNineRetunedTPlus00_pos
  have hproduct :
      0 < (d * factorTwoIntrinsicNineRetunedTPlus 0 0) *
        leadingMinorTwo
          (factorTwoIntrinsicNineRetunedTPlus 0 0)
          (factorTwoIntrinsicNineRetunedTPlus 0 1)
          (factorTwoIntrinsicNineRetunedTPlus 1 1) := by
    nlinarith
  have hcomm :
      0 < leadingMinorTwo
          (factorTwoIntrinsicNineRetunedTPlus 0 0)
          (factorTwoIntrinsicNineRetunedTPlus 0 1)
          (factorTwoIntrinsicNineRetunedTPlus 1 1) *
        (d * factorTwoIntrinsicNineRetunedTPlus 0 0) := by
    simpa only [mul_comm] using hproduct
  exact pos_of_mul_pos_left hcomm hda.le

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineRetunedPlusGatesPositive
