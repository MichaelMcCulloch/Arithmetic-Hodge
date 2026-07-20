import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
import ArithmeticHodge.Analysis.SparseEntriesRobustCertificate

set_option autoImplicit false

open MeasureTheory Real Set Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualLowerBoundStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaConstantBounds
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationDiagonalStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP11GalerkinFiniteSolveStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP11GalerkinRieszStructural
open YoshidaFourCellOddP11GalerkinSolutionBoxStructural
open YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityOperatorStructural
open SparseEntriesCertificate
open SparseEntriesRobustCertificate

/-!
# A structural lower bound for the old odd Galerkin residual

The five-mode lower matrix remains positive definite after subtracting
`1 / 4000` from its `P₁` diagonal.  This is certified by the same rational
lower-triangular congruence as the unshifted block.  Consequently every
five-mode profile has core energy strictly above `c² / 4000`, where `c` is
its `P₁` coefficient.  The exact old Galerkin residual has `c = 1`.

No determinant or finite case enumeration enters the proof: the only finite
certificate is robust diagonal dominance after an exact congruence.
-/

private theorem two_mul_fourCellOperatorHalfWidth_fine_bounds_local :
    (8664 / 10000 : ℝ) < 2 * fourCellOperatorHalfWidth ∧
      2 * fourCellOperatorHalfWidth < (8665 / 10000 : ℝ) := by
  have hL := strict_log_two_fine_bounds
  unfold fourCellOperatorHalfWidth
  constructor <;> nlinarith

private theorem fourCell_sqrt_two_fine_bounds_local :
    (1414213562 / 1000000000 : ℝ) < Real.sqrt 2 ∧
      Real.sqrt 2 < (1414213563 / 1000000000 : ℝ) := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := by
    simpa only using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  constructor
  · have hrat : (1414213562 / 1000000000 : ℝ) ^ 2 < 2 := by
      norm_num
    nlinarith
  · have hrat : (2 : ℝ) <
        (1414213563 / 1000000000 : ℝ) ^ 2 := by
      norm_num
    nlinarith

private theorem fourCell_sqrt_two_mul_log_two_fine_bounds_local :
    (1414213562 / 1000000000 : ℝ) *
        (69314718055 / 100000000000 : ℝ) <
          Real.sqrt 2 * Real.log 2 ∧
      Real.sqrt 2 * Real.log 2 <
        (1414213563 / 1000000000 : ℝ) *
          (69314718057 / 100000000000 : ℝ) := by
  have hs := fourCell_sqrt_two_fine_bounds_local
  have hL := strict_log_two_fine_bounds
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · calc
      (1414213562 / 1000000000 : ℝ) *
          (69314718055 / 100000000000 : ℝ) <
          Real.sqrt 2 * (69314718055 / 100000000000 : ℝ) :=
        mul_lt_mul_of_pos_right hs.1 (by norm_num)
      _ < Real.sqrt 2 * Real.log 2 :=
        mul_lt_mul_of_pos_left hL.1 hs0
  · calc
      Real.sqrt 2 * Real.log 2 <
          (1414213563 / 1000000000 : ℝ) * Real.log 2 :=
        mul_lt_mul_of_pos_right hs.2 hL0
      _ < (1414213563 / 1000000000 : ℝ) *
          (69314718057 / 100000000000 : ℝ) :=
        mul_lt_mul_of_pos_left hL.2 (by norm_num)

private theorem abs_fourCellWideRegularEnvelopeError11_tight_le_local :
    |fourCellWideRegularEnvelopeError oddStructuralCorrelation11| ≤
      (1 / 120000 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddStructuralCorrelation11
      (by unfold oddStructuralCorrelation11; fun_prop)
  have hmass := integral_abs_oddStructuralCorrelation11_le
  nlinarith

private theorem abs_fourCellWideRegularEnvelopeError13_tight_lt_local :
    |fourCellWideRegularEnvelopeError oddStructuralCorrelation13| <
      (1 / 480000 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddStructuralCorrelation13
      (by unfold oddStructuralCorrelation13; fun_prop)
  have hmass := integral_abs_oddStructuralCorrelation13_lt
  nlinarith

private theorem abs_fourCellWideRegularEnvelopeError33_tight_le_local :
    |fourCellWideRegularEnvelopeError oddStructuralCorrelation33| ≤
      (1 / 280000 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddStructuralCorrelation33
      (by unfold oddStructuralCorrelation33; fun_prop)
  have hmass := integral_abs_oddStructuralCorrelation33_le
  nlinarith

private theorem abs_fourCellWideRegularEnvelopeError15_tight_lt_local :
    |fourCellWideRegularEnvelopeError oddP5Correlation15| <
      (1 / 1000000 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddP5Correlation15 (by unfold oddP5Correlation15; fun_prop)
  have hmass := integral_abs_oddP5Correlation15_lt
  nlinarith

private theorem abs_fourCellWideRegularEnvelopeError35_tight_lt_local :
    |fourCellWideRegularEnvelopeError oddP5Correlation35| <
      (11 / 10000000 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddP5Correlation35 (by unfold oddP5Correlation35; fun_prop)
  have hmass := integral_abs_oddP5Correlation35_lt
  nlinarith

private theorem abs_fourCellWideRegularEnvelopeError55_tight_le_local :
    |fourCellWideRegularEnvelopeError oddP5Correlation55| ≤
      (1 / 440000 : ℝ) := by
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddP5Correlation55 continuous_oddP5Correlation55
  have hmass := integral_abs_oddP5Correlation55_le
  nlinarith

set_option maxHeartbeats 1000000 in
private theorem fourCellOddOneThreeFiveRegular_entry_tight_bounds_local :
    (4855 / 1000000 : ℝ) < fourCellOddOneThreeFiveRegular11 ∧
    fourCellOddOneThreeFiveRegular11 < (4873 / 1000000 : ℝ) ∧
    (-193 / 1000000 : ℝ) < fourCellOddOneThreeFiveRegular13 ∧
    fourCellOddOneThreeFiveRegular13 < (-188 / 1000000 : ℝ) ∧
    (111 / 1000000 : ℝ) < fourCellOddOneThreeFiveRegular33 ∧
    fourCellOddOneThreeFiveRegular33 < (120 / 1000000 : ℝ) ∧
    (-1 / 1000000 : ℝ) < fourCellOddOneThreeFiveRegular15 ∧
    fourCellOddOneThreeFiveRegular15 < (2 / 1000000 : ℝ) ∧
    (-28 / 1000000 : ℝ) < fourCellOddOneThreeFiveRegular35 ∧
    fourCellOddOneThreeFiveRegular35 < (-24 / 1000000 : ℝ) ∧
    (25 / 1000000 : ℝ) < fourCellOddOneThreeFiveRegular55 ∧
    fourCellOddOneThreeFiveRegular55 < (31 / 1000000 : ℝ) := by
  rcases fourCellWideRegularPolynomial_entry_bounds with
    ⟨hP11lo, hP11hi, hP13lo, hP13hi, hP33lo, hP33hi,
      hP15lo, hP15hi, hP35lo, hP35hi, hP55lo, hP55hi⟩
  rcases fourCellOddOneThreeFiveRegular_entries_eq with
    ⟨h11, h13, h33, h15, h35, h55⟩
  have he11 := abs_le.mp abs_fourCellWideRegularEnvelopeError11_tight_le_local
  have he13 := abs_lt.mp abs_fourCellWideRegularEnvelopeError13_tight_lt_local
  have he33 := abs_le.mp abs_fourCellWideRegularEnvelopeError33_tight_le_local
  have he15 := abs_lt.mp abs_fourCellWideRegularEnvelopeError15_tight_lt_local
  have he35 := abs_lt.mp abs_fourCellWideRegularEnvelopeError35_tight_lt_local
  have he55 := abs_le.mp abs_fourCellWideRegularEnvelopeError55_tight_le_local
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
private theorem fourCellOddOneThreeFiveCombined_entry_certificate_bounds_local :
    (251905 / 1000000 : ℝ) < fourCellOddLowCombined11 ∧
    fourCellOddLowCombined11 < (251925 / 1000000 : ℝ) ∧
    (218622 / 1000000 : ℝ) < fourCellOddLowCombined13 ∧
    fourCellOddLowCombined13 < (218624 / 1000000 : ℝ) ∧
    (205150 / 1000000 : ℝ) < fourCellOddLowCombined33 ∧
    fourCellOddLowCombined33 < (205156 / 1000000 : ℝ) ∧
    (135290 / 10000000 : ℝ) < fourCellOddOneThreeFiveCombined15 ∧
    fourCellOddOneThreeFiveCombined15 < (135293 / 10000000 : ℝ) ∧
    (629389 / 10000000 : ℝ) < fourCellOddOneThreeFiveCombined35 ∧
    fourCellOddOneThreeFiveCombined35 < (629392 / 10000000 : ℝ) ∧
    (245090 / 1000000 : ℝ) < fourCellOddOneThreeFiveCombined55 ∧
    fourCellOddOneThreeFiveCombined55 < (245094 / 1000000 : ℝ) := by
  have hL := strict_log_two_fine_bounds
  have hP := fourCell_sqrt_two_mul_log_two_fine_bounds_local
  have hT := fourCellScalar_fine_bounds
  have h11 : fourCellOddLowCombined11 =
      893 / 600 - (31 / 50 : ℝ) * Real.log 2 +
        (94 / 375 : ℝ) * (Real.sqrt 2 * Real.log 2) -
          (2 / 3 : ℝ) *
            (Real.log (2 * fourCellOperatorHalfWidth) +
              Real.eulerMascheroniConstant + Real.log Real.pi) := by
    unfold fourCellOddLowCombined11 fourCellOddLowLocalAlgebraic11
    ring
  have h13 : fourCellOddLowCombined13 =
      93 / 500 + (104 / 3125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) := by
    unfold fourCellOddLowCombined13 fourCellOddLowLocalAlgebraic13
    ring
  have h33 : fourCellOddLowCombined33 =
      5434921 / 6125000 - (5242 / 109375 : ℝ) *
          (Real.sqrt 2 * Real.log 2) -
        (93 / 350 : ℝ) * Real.log 2 -
        (2 / 7 : ℝ) *
          (Real.log (2 * fourCellOperatorHalfWidth) +
            Real.eulerMascheroniConstant + Real.log Real.pi) := by
    unfold fourCellOddLowCombined33 fourCellOddLowLocalAlgebraic33
    ring
  have h15 : fourCellOddOneThreeFiveCombined15 =
      93 / 1400 - (4216 / 78125 : ℝ) *
        (Real.sqrt 2 * Real.log 2) := by
    unfold fourCellOddOneThreeFiveCombined15
      fourCellOddOneThreeFiveLocalAlgebraic15
    ring
  have h35 : fourCellOddOneThreeFiveCombined35 =
      96779 / 937500 - (16056 / 390625 : ℝ) *
        (Real.sqrt 2 * Real.log 2) := by
    unfold fourCellOddOneThreeFiveCombined35
      fourCellOddOneThreeFiveLocalAlgebraic35
    ring
  have h55 : fourCellOddOneThreeFiveCombined55 =
      1602471330659 / 2481445312500 +
        (1933534 / 537109375 : ℝ) *
          (Real.sqrt 2 * Real.log 2) -
        (93 / 550 : ℝ) * Real.log 2 -
        (2 / 11 : ℝ) *
          (Real.log (2 * fourCellOperatorHalfWidth) +
            Real.eulerMascheroniConstant + Real.log Real.pi) := by
    unfold fourCellOddOneThreeFiveCombined55
      fourCellOddOneThreeFiveLocalAlgebraic55
    ring
  rw [h11, h13, h33, h15, h35, h55]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
private theorem fourCellOddOneThreeFivePerturbed_entry_certificate_bounds_local :
    (247682 / 1000000 : ℝ) < fourCellOddOneThreeFivePerturbed11 ∧
    fourCellOddOneThreeFivePerturbed11 < (247719 / 1000000 : ℝ) ∧
    (218784 / 1000000 : ℝ) < fourCellOddOneThreeFivePerturbed13 ∧
    fourCellOddOneThreeFivePerturbed13 < (218792 / 1000000 : ℝ) ∧
    (205046 / 1000000 : ℝ) < fourCellOddOneThreeFivePerturbed33 ∧
    fourCellOddOneThreeFivePerturbed33 < (205060 / 1000000 : ℝ) ∧
    (13527 / 1000000 : ℝ) < fourCellOddOneThreeFivePerturbed15 ∧
    fourCellOddOneThreeFivePerturbed15 < (13531 / 1000000 : ℝ) ∧
    (62959 / 1000000 : ℝ) < fourCellOddOneThreeFivePerturbed35 ∧
    fourCellOddOneThreeFivePerturbed35 < (62964 / 1000000 : ℝ) ∧
    (245063 / 1000000 : ℝ) < fourCellOddOneThreeFivePerturbed55 ∧
    fourCellOddOneThreeFivePerturbed55 < (245073 / 1000000 : ℝ) := by
  let W : ℝ := 2 * fourCellOperatorHalfWidth
  rcases two_mul_fourCellOperatorHalfWidth_fine_bounds_local with ⟨hWlo, hWhi⟩
  change (8664 / 10000 : ℝ) < W at hWlo
  change W < (8665 / 10000 : ℝ) at hWhi
  have hW0 : 0 < W := hWlo.trans' (by norm_num)
  rcases fourCellOddOneThreeFiveCombined_entry_certificate_bounds_local with
    ⟨hAlo, hAhi, hBlo, hBhi, hDlo, hDhi,
      hElo, hEhi, hFlo, hFhi, hGlo, hGhi⟩
  rcases fourCellOddOneThreeFiveRegular_entry_tight_bounds_local with
    ⟨h11lo, h11hi, h13lo, h13hi, h33lo, h33hi,
      h15lo, h15hi, h35lo, h35hi, h55lo, h55hi⟩
  have hpositiveProduct {R lo hi : ℝ}
      (hlo : lo < R) (hhi : R < hi) (hlo0 : 0 < lo) :
      (8664 / 10000 : ℝ) * lo < W * R ∧
        W * R < (8665 / 10000 : ℝ) * hi := by
    have hR0 : 0 < R := hlo0.trans hlo
    constructor
    · exact (mul_lt_mul_of_pos_right hWlo hlo0).trans
        (mul_lt_mul_of_pos_left hlo hW0)
    · exact (mul_lt_mul_of_pos_left hhi hW0).trans
        (mul_lt_mul_of_pos_right hWhi (by linarith))
  have hnegativeProduct {R lo hi : ℝ}
      (hlo : lo < R) (hhi : R < hi) (hhi0 : hi < 0) :
      (8665 / 10000 : ℝ) * lo < W * R ∧
        W * R < (8664 / 10000 : ℝ) * hi := by
    constructor
    · exact (mul_lt_mul_of_neg_right hWhi (by linarith)).trans
        (mul_lt_mul_of_pos_left hlo hW0)
    · exact (mul_lt_mul_of_pos_left hhi hW0).trans
        (mul_lt_mul_of_neg_right hWlo hhi0)
  have hcrossProduct {R lo hi : ℝ}
      (hlo : lo < R) (hhi : R < hi) (hlo0 : lo < 0) (hhi0 : 0 < hi) :
      (8665 / 10000 : ℝ) * lo < W * R ∧
        W * R < (8665 / 10000 : ℝ) * hi := by
    constructor
    · exact (mul_lt_mul_of_neg_right hWhi hlo0).trans
        (mul_lt_mul_of_pos_left hlo hW0)
    · exact (mul_lt_mul_of_pos_left hhi hW0).trans
        (mul_lt_mul_of_pos_right hWhi hhi0)
  have hW11 := hpositiveProduct h11lo h11hi (by norm_num)
  have hW13 := hnegativeProduct h13lo h13hi (by norm_num)
  have hW33 := hpositiveProduct h33lo h33hi (by norm_num)
  have hW15 := hcrossProduct h15lo h15hi (by norm_num) (by norm_num)
  have hW35 := hnegativeProduct h35lo h35hi (by norm_num)
  have hW55 := hpositiveProduct h55lo h55hi (by norm_num)
  unfold fourCellOddOneThreeFivePerturbed11
    fourCellOddOneThreeFivePerturbed13
    fourCellOddOneThreeFivePerturbed33
    fourCellOddOneThreeFivePerturbed15
    fourCellOddOneThreeFivePerturbed35
    fourCellOddOneThreeFivePerturbed55
  change
    (247682 / 1000000 : ℝ) <
        fourCellOddLowCombined11 - W * fourCellOddOneThreeFiveRegular11 ∧ _
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-! ## The shifted five-mode congruence -/

/-- The old five-mode lower matrix after reserving `P₁² / 4000`.
Positive definiteness of this matrix is exactly the required quotient
coercivity statement. -/
def fourCellOddFiveModeP1ShiftedLowerMatrix : Matrix (Fin 5) (Fin 5) ℝ :=
  !![fourCellOddOneThreeFivePerturbed11 - 1 / 4000,
      fourCellOddOneThreeFivePerturbed13,
      fourCellOddOneThreeFivePerturbed15,
      fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP7,
      fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP9;
    fourCellOddOneThreeFivePerturbed13,
      fourCellOddOneThreeFivePerturbed33,
      fourCellOddOneThreeFivePerturbed35,
      fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP7,
      fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP9;
    fourCellOddOneThreeFivePerturbed15,
      fourCellOddOneThreeFivePerturbed35,
      fourCellOddOneThreeFivePerturbed55,
      fourCellOddCoreLocalBilinear factorTwoCenteredP5 factorTwoCenteredP7,
      fourCellOddCoreLocalBilinear factorTwoCenteredP5 factorTwoCenteredP9;
    fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP7,
      fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP7,
      fourCellOddCoreLocalBilinear factorTwoCenteredP5 factorTwoCenteredP7,
      (1 / 5 : ℝ),
      fourCellOddCoreLocalBilinear factorTwoCenteredP7 factorTwoCenteredP9;
    fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP9,
      fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP9,
      fourCellOddCoreLocalBilinear factorTwoCenteredP5 factorTwoCenteredP9,
      fourCellOddCoreLocalBilinear factorTwoCenteredP7 factorTwoCenteredP9,
      (29 / 200 : ℝ)]

private def shiftedCertificateCenter : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(494901 / 2000000 : ℚ), 218788 / 1000000, 13529 / 1000000,
      35621 / 1000000, 88027 / 2000000;
    218788 / 1000000, 205053 / 1000000, 125923 / 2000000,
      59255 / 1000000, 40815 / 1000000;
    13529 / 1000000, 125923 / 2000000, 245068 / 1000000,
      187123 / 2000000, 26254 / 1000000;
    35621 / 1000000, 59255 / 1000000, 187123 / 2000000,
      1 / 5, 15331 / 1000000;
    88027 / 2000000, 40815 / 1000000, 26254 / 1000000,
      15331 / 1000000, 29 / 200]

private def shiftedCertificateEpsilon : ℚ := 1 / 50000

private def shiftedCertificateWeights : Fin 5 → ℚ :=
  ![1, 1, 1, 1, 1]

private def shiftedCertificateCongruenceEntries :
    Fin 5 → SparseEntries (Fin 5) :=
  ![[(0, 1)],
    [(0, -8833 / 10000), (1, 1)],
    [(0, 37629 / 10000), (1, -2161 / 500), (2, 1)],
    [(0, 64317 / 10000), (1, -75183 / 10000),
      (2, 11947 / 10000), (3, 1)],
    [(0, -20091 / 5000), (1, 44449 / 10000),
      (2, -1871 / 2000), (3, -2403 / 10000), (4, 1)]]

private theorem shiftedCertificateCenter_isSymm :
    shiftedCertificateCenter.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shiftedCertificateCenter, Matrix.transpose_apply]

private theorem shiftedCertificateCongruence_lower :
    ∀ i j,
      entriesValue (shiftedCertificateCongruenceEntries i) j ≠ 0 →
        j ≤ i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shiftedCertificateCongruenceEntries, entriesValue,
      Fin.ext_iff, Fin.le_iff_val_le_val]

private theorem shiftedCertificateCongruence_diagonal :
    ∀ i,
      entriesValue (shiftedCertificateCongruenceEntries i) i ≠ 0 := by
  intro i
  fin_cases i <;>
    norm_num [shiftedCertificateCongruenceEntries, entriesValue, Fin.ext_iff]

private theorem shiftedCertificateWeights_pos :
    ∀ i, 0 < shiftedCertificateWeights i := by
  intro i
  fin_cases i <;> norm_num [shiftedCertificateWeights]

set_option maxHeartbeats 5000000 in
private theorem shiftedCertificateDominance :
    ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius
              shiftedCertificateCongruenceEntries
              shiftedCertificateCenter
              shiftedCertificateEpsilon i j *
            shiftedCertificateWeights j) <
        entriesRobustDiagonalLower
            shiftedCertificateCongruenceEntries
            shiftedCertificateCenter
            shiftedCertificateEpsilon i *
          shiftedCertificateWeights i := by
  intro i
  fin_cases i <;>
    norm_num [entriesRobustRadius, entriesRobustDiagonalLower,
      entriesCongruence, entriesL1,
      shiftedCertificateCongruenceEntries, shiftedCertificateCenter,
      shiftedCertificateEpsilon, shiftedCertificateWeights,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.vecHead,
      Matrix.vecTail, Fin.ext_iff]

private theorem fourCellOddFiveModeP1ShiftedLowerMatrix_isHermitian :
    fourCellOddFiveModeP1ShiftedLowerMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fourCellOddFiveModeP1ShiftedLowerMatrix]

set_option maxHeartbeats 2000000 in
private theorem fourCellOddFiveModeP1ShiftedLowerMatrix_entrywise_close :
    ∀ i j,
      |fourCellOddFiveModeP1ShiftedLowerMatrix i j -
          (shiftedCertificateCenter i j : ℝ)| ≤
        (shiftedCertificateEpsilon : ℝ) := by
  rcases fourCellOddOneThreeFivePerturbed_entry_certificate_bounds_local with
    ⟨h11lo, h11hi, h13lo, h13hi, h33lo, h33hi,
      h15lo, h15hi, h35lo, h35hi, h55lo, h55hi⟩
  rcases fourCellOddCoreLocalBilinear_P1_high_certificate_bounds with
    ⟨h17lo, h17hi, h19lo, h19hi⟩
  rcases fourCellOddCoreLocalBilinear_P3_P7_bounds with ⟨h37lo, h37hi⟩
  rcases fourCellOddCoreLocalBilinear_P3_P9_bounds with ⟨h39lo, h39hi⟩
  rcases fourCellOddCoreLocal_highCross_certificate_bounds with
    ⟨h57lo, h57hi, h59lo, h59hi, h79lo, h79hi⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fourCellOddFiveModeP1ShiftedLowerMatrix,
      shiftedCertificateCenter, shiftedCertificateEpsilon,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Fin.ext_iff,
      abs_le] at * <;>
    constructor <;> nlinarith

/-- Structural quotient coercivity: the certified lower matrix remains
positive definite after reserving `P₁² / 4000`. -/
theorem fourCellOddFiveModeP1ShiftedLowerMatrix_posDef :
    fourCellOddFiveModeP1ShiftedLowerMatrix.PosDef := by
  exact posDef_of_sparseEntries_robust_congruence
    fourCellOddFiveModeP1ShiftedLowerMatrix
    shiftedCertificateCongruenceEntries
    shiftedCertificateCenter
    shiftedCertificateEpsilon
    shiftedCertificateWeights
    fourCellOddFiveModeP1ShiftedLowerMatrix_isHermitian
    shiftedCertificateCenter_isSymm
    shiftedCertificateCongruence_lower
    shiftedCertificateCongruence_diagonal
    (by norm_num [shiftedCertificateEpsilon])
    fourCellOddFiveModeP1ShiftedLowerMatrix_entrywise_close
    shiftedCertificateWeights_pos
    shiftedCertificateDominance

set_option maxHeartbeats 2000000 in
/-- Every retained five-mode profile with nonzero `P₁` coefficient has
strictly more than `P₁² / 4000` complete core energy. -/
theorem one_div_four_thousand_mul_P1_sq_lt_fourCellOddFiveModeCoreExpression
    (c d e f g : ℝ) (hc : c ≠ 0) :
    (1 / 4000 : ℝ) * c ^ 2 <
      fourCellOddFiveModeCoreExpression c d e f g := by
  let x : Fin 5 → ℝ := ![c, d, e, f, g]
  have hx : x ≠ 0 := by
    intro hzero
    have hfirst := congrFun hzero 0
    simp only [x, Matrix.vecCons] at hfirst
    exact hc hfirst
  have hmatrix :=
    fourCellOddFiveModeP1ShiftedLowerMatrix_posDef.dotProduct_mulVec_pos hx
  simp only [star_trivial] at hmatrix
  have hlower : (1 / 4000 : ℝ) * c ^ 2 <
      fourCellOddOneThreeFivePerturbedQuadratic c d e +
        2 * fourCellOddCoreLocalBilinear
            centeredP1 factorTwoCenteredP7 * c * f +
        2 * fourCellOddCoreLocalBilinear
            centeredP3 factorTwoCenteredP7 * d * f +
        2 * fourCellOddCoreLocalBilinear
            factorTwoCenteredP5 factorTwoCenteredP7 * e * f +
        (1 / 5 : ℝ) * f ^ 2 +
        2 * fourCellOddCoreLocalBilinear
            centeredP1 factorTwoCenteredP9 * c * g +
        2 * fourCellOddCoreLocalBilinear
            centeredP3 factorTwoCenteredP9 * d * g +
        2 * fourCellOddCoreLocalBilinear
            factorTwoCenteredP5 factorTwoCenteredP9 * e * g +
        2 * fourCellOddCoreLocalBilinear
            factorTwoCenteredP7 factorTwoCenteredP9 * f * g +
        (29 / 200 : ℝ) * g ^ 2 := by
    simp [x, fourCellOddFiveModeP1ShiftedLowerMatrix, dotProduct,
      Matrix.mulVec, Fin.sum_univ_succ] at hmatrix
    unfold fourCellOddOneThreeFivePerturbedQuadratic
    nlinarith
  have h7 := one_fifth_lt_fourCellOddCoreLocalQuadratic_P7
  have h9 := twenty_nine_two_hundredths_lt_fourCellOddCoreLocalQuadratic_P9
  unfold fourCellOddFiveModeCoreExpression
  nlinarith [mul_le_mul_of_nonneg_right h7.le (sq_nonneg f),
    mul_le_mul_of_nonneg_right h9.le (sq_nonneg g)]

/-- The old four-mode Galerkin residual has a quantitative rational pivot.
This is the reusable lower half of the subsequent rank-one `P₁₁` Schur
update. -/
theorem one_div_four_thousand_lt_fourCellOddCoreLocalQuadratic_exactGalerkinResidual :
    (1 / 4000 : ℝ) <
      fourCellOddCoreLocalQuadratic
        fourCellOddP11GalerkinRetainedResidualProfile := by
  unfold fourCellOddP11GalerkinRetainedResidualProfile
  rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode,
    fourCellOddCoreLocalQuadratic_fiveMode_eq_coreExpression]
  simpa using
    one_div_four_thousand_mul_P1_sq_lt_fourCellOddFiveModeCoreExpression
      1 (-fourCellOddP11GalerkinRetainedSolution 0)
        (-fourCellOddP11GalerkinRetainedSolution 1)
        (-fourCellOddP11GalerkinRetainedSolution 2)
        (-fourCellOddP11GalerkinRetainedSolution 3) (by norm_num)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualLowerBoundStructural
