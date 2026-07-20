import ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreDiagonalBoundsStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreEntryBoundsStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedRankOneSchurStructural

set_option autoImplicit false

open Matrix Real
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedSchurPivotFloorStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaConstantBounds
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP11CoreDiagonalBoundsStructural
open YoshidaFourCellOddP11CoreEntryBoundsStructural
open YoshidaFourCellOddP11GalerkinFiniteSolveStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
open YoshidaFourCellOddP13AugmentedRankOneSchurStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open SparseEntriesCertificate
open SparseEntriesRobustCertificate

/-!
# Structural floor for the `P11` rank-one Schur pivot

The proof reserves `1/10` of the coefficient square on the old
`P3/P5/P7/P9` block by a rational congruence.  Four structural mixed-row
bounds then complete squares against `P11`.  No finite search or evaluation
of the inverse-defined projection is used.
-/

/-! ## Quantitative coercivity of the old retained block -/

/-- The rational lower old-block matrix after reserving `1/10` of every
coefficient square. -/
def fourCellOddOldBlockOneTenthShiftedLowerMatrix :
    Matrix (Fin 4) (Fin 4) ℝ :=
  !![fourCellOddOneThreeFivePerturbed33 - 1 / 10,
      fourCellOddOneThreeFivePerturbed35,
      fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP7,
      fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP9;
    fourCellOddOneThreeFivePerturbed35,
      fourCellOddOneThreeFivePerturbed55 - 1 / 10,
      fourCellOddCoreLocalBilinear factorTwoCenteredP5 factorTwoCenteredP7,
      fourCellOddCoreLocalBilinear factorTwoCenteredP5 factorTwoCenteredP9;
    fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP7,
      fourCellOddCoreLocalBilinear factorTwoCenteredP5 factorTwoCenteredP7,
      (1 / 10 : ℝ),
      fourCellOddCoreLocalBilinear factorTwoCenteredP7 factorTwoCenteredP9;
    fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP9,
      fourCellOddCoreLocalBilinear factorTwoCenteredP5 factorTwoCenteredP9,
      fourCellOddCoreLocalBilinear factorTwoCenteredP7 factorTwoCenteredP9,
      (9 / 200 : ℝ)]

private def oldBlockShiftedCenter : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(105053 / 1000000 : ℚ), 125923 / 2000000,
      59255 / 1000000, 40815 / 1000000;
    125923 / 2000000, 145068 / 1000000,
      187123 / 2000000, 26254 / 1000000;
    59255 / 1000000, 187123 / 2000000,
      1 / 10, 15331 / 1000000;
    40815 / 1000000, 26254 / 1000000,
      15331 / 1000000, 9 / 200]

private def oldBlockShiftedEpsilon : ℚ := 1 / 5000

private def oldBlockShiftedWeights : Fin 4 → ℚ := ![1, 1, 1, 1]

private def oldBlockShiftedCongruenceEntries :
    Fin 4 → SparseEntries (Fin 4) :=
  ![[(0, 1)],
    [(0, -5993 / 10000), (1, 1)],
    [(0, -2399 / 10000), (1, -5408 / 10000), (2, 1)],
    [(0, -4376 / 10000), (1, -1498 / 10000),
      (2, 2461 / 10000), (3, 1)]]

private theorem oldBlockShiftedCenter_isSymm :
    oldBlockShiftedCenter.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [oldBlockShiftedCenter, Matrix.transpose_apply]

private theorem oldBlockShiftedCongruence_lower :
    ∀ i j,
      entriesValue (oldBlockShiftedCongruenceEntries i) j ≠ 0 → j ≤ i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [oldBlockShiftedCongruenceEntries, entriesValue,
      Fin.ext_iff, Fin.le_iff_val_le_val]

private theorem oldBlockShiftedCongruence_diagonal :
    ∀ i, entriesValue (oldBlockShiftedCongruenceEntries i) i ≠ 0 := by
  intro i
  fin_cases i <;>
    norm_num [oldBlockShiftedCongruenceEntries, entriesValue, Fin.ext_iff]

private theorem oldBlockShiftedWeights_pos :
    ∀ i, 0 < oldBlockShiftedWeights i := by
  intro i
  fin_cases i <;> norm_num [oldBlockShiftedWeights]

set_option maxHeartbeats 3000000 in
private theorem oldBlockShiftedDominance :
    ∀ i,
      (∑ j ∈ Finset.univ.erase i,
          entriesRobustRadius oldBlockShiftedCongruenceEntries
              oldBlockShiftedCenter oldBlockShiftedEpsilon i j *
            oldBlockShiftedWeights j) <
        entriesRobustDiagonalLower oldBlockShiftedCongruenceEntries
            oldBlockShiftedCenter oldBlockShiftedEpsilon i *
          oldBlockShiftedWeights i := by
  intro i
  fin_cases i <;>
    norm_num [entriesRobustRadius, entriesRobustDiagonalLower,
      entriesCongruence, entriesL1, oldBlockShiftedCongruenceEntries,
      oldBlockShiftedCenter, oldBlockShiftedEpsilon, oldBlockShiftedWeights,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Fin.ext_iff]

private theorem fourCellOddOldBlockOneTenthShiftedLowerMatrix_isHermitian :
    fourCellOddOldBlockOneTenthShiftedLowerMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fourCellOddOldBlockOneTenthShiftedLowerMatrix]

set_option maxHeartbeats 2000000 in
private theorem fourCellOddOldBlockOneTenthShiftedLowerMatrix_entrywise_close :
    ∀ i j,
      |fourCellOddOldBlockOneTenthShiftedLowerMatrix i j -
          (oldBlockShiftedCenter i j : ℝ)| ≤
        (oldBlockShiftedEpsilon : ℝ) := by
  rcases fourCellOddOneThreeFivePerturbed_entry_bounds with
    ⟨_h11lo, _h11hi, _h13lo, _h13hi, h33lo, h33hi,
      _h15lo, _h15hi, h35lo, h35hi, h55lo, h55hi⟩
  rcases fourCellOddCoreLocalBilinear_P3_P7_bounds with ⟨h37lo, h37hi⟩
  rcases fourCellOddCoreLocalBilinear_P3_P9_bounds with ⟨h39lo, h39hi⟩
  rcases fourCellOddCoreLocal_highCross_certificate_bounds with
    ⟨h57lo, h57hi, h59lo, h59hi, h79lo, h79hi⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fourCellOddOldBlockOneTenthShiftedLowerMatrix,
      oldBlockShiftedCenter, oldBlockShiftedEpsilon,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ,
      Matrix.vecHead, Matrix.vecTail, Fin.ext_iff, abs_le] at * <;>
    constructor <;> nlinarith

/-- The old retained core still has a positive-definite rational lower
matrix after reserving `1/10` of every coefficient square. -/
theorem fourCellOddOldBlockOneTenthShiftedLowerMatrix_posDef :
    fourCellOddOldBlockOneTenthShiftedLowerMatrix.PosDef := by
  exact posDef_of_sparseEntries_robust_congruence
    fourCellOddOldBlockOneTenthShiftedLowerMatrix
    oldBlockShiftedCongruenceEntries oldBlockShiftedCenter
    oldBlockShiftedEpsilon oldBlockShiftedWeights
    fourCellOddOldBlockOneTenthShiftedLowerMatrix_isHermitian
    oldBlockShiftedCenter_isSymm oldBlockShiftedCongruence_lower
    oldBlockShiftedCongruence_diagonal
    (by norm_num [oldBlockShiftedEpsilon])
    fourCellOddOldBlockOneTenthShiftedLowerMatrix_entrywise_close
    oldBlockShiftedWeights_pos oldBlockShiftedDominance

private theorem oldBlockShiftedLowerQuadratic_nonneg
    (d e f g : ℝ) :
    0 ≤
      (fourCellOddOneThreeFivePerturbed33 - 1 / 10) * d ^ 2 +
      2 * fourCellOddOneThreeFivePerturbed35 * d * e +
      (fourCellOddOneThreeFivePerturbed55 - 1 / 10) * e ^ 2 +
      2 * fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP7 * d * f +
      2 * fourCellOddCoreLocalBilinear factorTwoCenteredP5
          factorTwoCenteredP7 * e * f +
      (1 / 10 : ℝ) * f ^ 2 +
      2 * fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP9 * d * g +
      2 * fourCellOddCoreLocalBilinear factorTwoCenteredP5
          factorTwoCenteredP9 * e * g +
      2 * fourCellOddCoreLocalBilinear factorTwoCenteredP7
          factorTwoCenteredP9 * f * g +
      (9 / 200 : ℝ) * g ^ 2 := by
  let x : Fin 4 → ℝ := ![d, e, f, g]
  have h := fourCellOddOldBlockOneTenthShiftedLowerMatrix_posDef.posSemidef
    |>.dotProduct_mulVec_nonneg x
  simp only [star_trivial] at h
  simp [x, fourCellOddOldBlockOneTenthShiftedLowerMatrix, dotProduct,
    Matrix.mulVec, Fin.sum_univ_succ] at h
  convert h using 1
  ring

/-- Quantitative coefficient coercivity on the exact old retained block. -/
theorem one_tenth_coeff_sq_le_fourCellOddOldRetainedQuadratic
    (d e f g : ℝ) :
    (1 / 10 : ℝ) * (d ^ 2 + e ^ 2 + f ^ 2 + g ^ 2) ≤
      fourCellOddCoreLocalQuadratic
        (fourCellOddP11GalerkinRetainedProfile ![d, e, f, g]) := by
  have hlower := oldBlockShiftedLowerQuadratic_nonneg d e f g
  have h7 := one_fifth_lt_fourCellOddCoreLocalQuadratic_P7
  have h9 := twenty_nine_two_hundredths_lt_fourCellOddCoreLocalQuadratic_P9
  change (1 / 10 : ℝ) * (d ^ 2 + e ^ 2 + f ^ 2 + g ^ 2) ≤
    fourCellOddCoreLocalQuadratic
      (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g)
  rw [fourCellOddCoreLocalQuadratic_fiveMode_eq_coreExpression]
  unfold fourCellOddFiveModeCoreExpression
    fourCellOddOneThreeFivePerturbedQuadratic
  nlinarith [mul_le_mul_of_nonneg_right h7.le (sq_nonneg f),
    mul_le_mul_of_nonneg_right h9.le (sq_nonneg g)]

/-! ## Structural bounds for the `P11` mixed row -/

private theorem sqrt_two_mul_log_two_bounds_local :
    (141421 / 100000 : ℝ) * (6931 / 10000 : ℝ) <
        Real.sqrt 2 * Real.log 2 ∧
      Real.sqrt 2 * Real.log 2 <
        (70711 / 50000 : ℝ) * (6932 / 10000 : ℝ) := by
  rcases sqrt_two_kernel_bounds with ⟨hslo, hshi⟩
  rcases strict_log_two_bounds with ⟨hllo, hlhi⟩
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hlpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · calc
      (141421 / 100000 : ℝ) * (6931 / 10000 : ℝ) <
          Real.sqrt 2 * (6931 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_right hslo (by norm_num)
      _ < Real.sqrt 2 * Real.log 2 :=
        mul_lt_mul_of_pos_left hllo hspos
  · calc
      Real.sqrt 2 * Real.log 2 <
          (70711 / 50000 : ℝ) * Real.log 2 :=
        mul_lt_mul_of_pos_right hshi hlpos
      _ < (70711 / 50000 : ℝ) * (6932 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_left hlhi (by norm_num)

private theorem fourCellOperatorHalfWidth_bounds_local :
    0 < fourCellOperatorHalfWidth ∧
      fourCellOperatorHalfWidth < (1733 / 4000 : ℝ) := by
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloghi := strict_log_two_bounds.2
  unfold fourCellOperatorHalfWidth
  constructor <;> nlinarith

private theorem abs_lt_of_sq_lt_sq_local
    (x c : ℝ) (hc : 0 < c) (h : x ^ 2 < c ^ 2) :
    |x| < c := by
  rw [abs_lt]
  constructor <;> nlinarith [sq_nonneg (x - c), sq_nonneg (x + c)]

private theorem abs_regularCorrection_P3_lt :
    |2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreRegularMoment centeredP3| < (7 / 1000 : ℝ) := by
  have hsq := fourCellOddP11CoreRegularMoment_P3_sq_le
  rcases fourCellOperatorHalfWidth_bounds_local with ⟨hwlo, hwhi⟩
  have hbound :
      (fourCellOperatorHalfWidth / 10) ^ 2 * (4 / 161 : ℝ) <
        (7 / 1000 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (fourCellOperatorHalfWidth - 1733 / 4000)]
  exact abs_lt_of_sq_lt_sq_local _ _ (by norm_num) (hsq.trans_lt hbound)

private theorem abs_regularCorrection_P5_lt :
    |2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreRegularMoment factorTwoCenteredP5| <
      (11 / 2000 : ℝ) := by
  have hsq := fourCellOddP11CoreRegularMoment_P5_sq_le
  rcases fourCellOperatorHalfWidth_bounds_local with ⟨hwlo, hwhi⟩
  have hbound :
      (fourCellOperatorHalfWidth / 10) ^ 2 * (4 / 253 : ℝ) <
        (11 / 2000 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (fourCellOperatorHalfWidth - 1733 / 4000)]
  exact abs_lt_of_sq_lt_sq_local _ _ (by norm_num) (hsq.trans_lt hbound)

private theorem abs_regularCorrection_P7_lt :
    |2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreRegularMoment factorTwoCenteredP7| <
      (1 / 200 : ℝ) := by
  have hsq := fourCellOddP11CoreRegularMoment_P7_sq_le
  rcases fourCellOperatorHalfWidth_bounds_local with ⟨hwlo, hwhi⟩
  have hbound :
      (fourCellOperatorHalfWidth / 10) ^ 2 * (4 / 345 : ℝ) <
        (1 / 200 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (fourCellOperatorHalfWidth - 1733 / 4000)]
  exact abs_lt_of_sq_lt_sq_local _ _ (by norm_num) (hsq.trans_lt hbound)

private theorem abs_regularCorrection_P9_lt :
    |2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreRegularMoment factorTwoCenteredP9| <
      (21 / 5000 : ℝ) := by
  have hsq := fourCellOddP11CoreRegularMoment_P9_sq_le
  rcases fourCellOperatorHalfWidth_bounds_local with ⟨hwlo, hwhi⟩
  have hbound :
      (fourCellOperatorHalfWidth / 10) ^ 2 * (4 / 437 : ℝ) <
        (21 / 5000 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (fourCellOperatorHalfWidth - 1733 / 4000)]
  exact abs_lt_of_sq_lt_sq_local _ _ (by norm_num) (hsq.trans_lt hbound)

/-- Mixed `P3/P11` entry at the scale needed by the Schur completion. -/
theorem abs_fourCellOddCoreLocalBilinear_P3_P11_lt :
    |fourCellOddCoreLocalBilinear centeredP3 fourCellOddP11DirectTail| <
      (1 / 100 : ℝ) := by
  rw [fourCellOddCoreLocalBilinear_P3_P11_eq, abs_lt]
  rcases sqrt_two_mul_log_two_bounds_local with ⟨halphaLo, halphaHi⟩
  rcases abs_lt.mp abs_regularCorrection_P3_lt with ⟨hregLo, hregHi⟩
  constructor <;> nlinarith

/-- Mixed `P5/P11` entry at the scale needed by the Schur completion. -/
theorem abs_fourCellOddCoreLocalBilinear_P5_P11_lt :
    |fourCellOddCoreLocalBilinear factorTwoCenteredP5
        fourCellOddP11DirectTail| < (1 / 100 : ℝ) := by
  rw [fourCellOddCoreLocalBilinear_P5_P11_eq, abs_lt]
  rcases sqrt_two_mul_log_two_bounds_local with ⟨halphaLo, halphaHi⟩
  rcases abs_lt.mp abs_regularCorrection_P5_lt with ⟨hregLo, hregHi⟩
  constructor <;> nlinarith

/-- Mixed `P7/P11` entry at the scale needed by the Schur completion. -/
theorem abs_fourCellOddCoreLocalBilinear_P7_P11_lt :
    |fourCellOddCoreLocalBilinear factorTwoCenteredP7
        fourCellOddP11DirectTail| < (3 / 250 : ℝ) := by
  rw [fourCellOddCoreLocalBilinear_P7_P11_eq, abs_lt]
  rcases sqrt_two_mul_log_two_bounds_local with ⟨halphaLo, halphaHi⟩
  rcases abs_lt.mp abs_regularCorrection_P7_lt with ⟨hregLo, hregHi⟩
  constructor <;> nlinarith

/-- Mixed `P9/P11` entry at the scale needed by the Schur completion. -/
theorem abs_fourCellOddCoreLocalBilinear_P9_P11_lt :
    |fourCellOddCoreLocalBilinear factorTwoCenteredP9
        fourCellOddP11DirectTail| < (1 / 25 : ℝ) := by
  rw [fourCellOddCoreLocalBilinear_P9_P11_eq, abs_lt]
  rcases sqrt_two_mul_log_two_bounds_local with ⟨halphaLo, halphaHi⟩
  rcases abs_lt.mp abs_regularCorrection_P9_lt with ⟨hregLo, hregHi⟩
  constructor <;> nlinarith

/-- The four mixed-row squares cost strictly less than `1/500`. -/
theorem fourCellOddP11OldBlockTailRow_sq_sum_lt_one_div_500 :
    fourCellOddCoreLocalBilinear centeredP3 fourCellOddP11DirectTail ^ 2 +
        fourCellOddCoreLocalBilinear factorTwoCenteredP5
          fourCellOddP11DirectTail ^ 2 +
        fourCellOddCoreLocalBilinear factorTwoCenteredP7
          fourCellOddP11DirectTail ^ 2 +
        fourCellOddCoreLocalBilinear factorTwoCenteredP9
          fourCellOddP11DirectTail ^ 2 <
      (1 / 500 : ℝ) := by
  rcases abs_lt.mp abs_fourCellOddCoreLocalBilinear_P3_P11_lt with
    ⟨h3lo, h3hi⟩
  rcases abs_lt.mp abs_fourCellOddCoreLocalBilinear_P5_P11_lt with
    ⟨h5lo, h5hi⟩
  rcases abs_lt.mp abs_fourCellOddCoreLocalBilinear_P7_P11_lt with
    ⟨h7lo, h7hi⟩
  rcases abs_lt.mp abs_fourCellOddCoreLocalBilinear_P9_P11_lt with
    ⟨h9lo, h9hi⟩
  nlinarith

/-! ## Completion of squares -/

private theorem contDiff_centeredP3_local : ContDiff ℝ 1 centeredP3 := by
  unfold centeredP3
  fun_prop

private theorem odd_centeredP3_local : Function.Odd centeredP3 := by
  intro x
  unfold centeredP3
  ring

private theorem contDiff_factorTwoCenteredP5_local :
    ContDiff ℝ 1 factorTwoCenteredP5 := by
  unfold factorTwoCenteredP5
  fun_prop

private theorem contDiff_factorTwoCenteredP7_local :
    ContDiff ℝ 1 factorTwoCenteredP7 := by
  rw [show factorTwoCenteredP7 = fun x ↦
      (429 * x ^ 7 - 693 * x ^ 5 + 315 * x ^ 3 - 35 * x) / 16 by
    funext x
    exact factorTwoCenteredP7_eq x]
  fun_prop

private theorem contDiff_factorTwoCenteredP9_local :
    ContDiff ℝ 1 factorTwoCenteredP9 := by
  rw [show factorTwoCenteredP9 = fun x ↦
      (12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
        4620 * x ^ 3 + 315 * x) / 128 by
    funext x
    exact factorTwoCenteredP9_eq x]
  fun_prop

private theorem odd_const_mul_local
    {v : ℝ → ℝ} (hv : Function.Odd v) (a : ℝ) :
    Function.Odd (fun x ↦ a * v x) := by
  intro x
  change a * v (-x) = -(a * v x)
  rw [hv]
  ring

private theorem oldRetainedProfile_decompose (d e f g : ℝ) :
    fourCellOddP11GalerkinRetainedProfile ![d, e, f, g] =
      (((fun x ↦ d * centeredP3 x) +
          (fun x ↦ e * factorTwoCenteredP5 x)) +
        (fun x ↦ f * factorTwoCenteredP7 x)) +
      (fun x ↦ g * factorTwoCenteredP9 x) := by
  funext x
  unfold fourCellOddP11GalerkinRetainedProfile
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp

private theorem oldRetainedProfile_tail_row_expansion (d e f g : ℝ) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP11GalerkinRetainedProfile ![d, e, f, g])
        fourCellOddP11DirectTail =
      d * fourCellOddCoreLocalBilinear centeredP3 fourCellOddP11DirectTail +
      e * fourCellOddCoreLocalBilinear factorTwoCenteredP5
        fourCellOddP11DirectTail +
      f * fourCellOddCoreLocalBilinear factorTwoCenteredP7
        fourCellOddP11DirectTail +
      g * fourCellOddCoreLocalBilinear factorTwoCenteredP9
        fourCellOddP11DirectTail := by
  let p3 : ℝ → ℝ := fun x ↦ d * centeredP3 x
  let p5 : ℝ → ℝ := fun x ↦ e * factorTwoCenteredP5 x
  let p7 : ℝ → ℝ := fun x ↦ f * factorTwoCenteredP7 x
  let p9 : ℝ → ℝ := fun x ↦ g * factorTwoCenteredP9 x
  have hp3 : ContDiff ℝ 1 p3 := contDiff_const.mul contDiff_centeredP3_local
  have hp5 : ContDiff ℝ 1 p5 :=
    contDiff_const.mul contDiff_factorTwoCenteredP5_local
  have hp7 : ContDiff ℝ 1 p7 :=
    contDiff_const.mul contDiff_factorTwoCenteredP7_local
  have hp9 : ContDiff ℝ 1 p9 :=
    contDiff_const.mul contDiff_factorTwoCenteredP9_local
  have hp3odd : Function.Odd p3 := odd_const_mul_local odd_centeredP3_local d
  have hp5odd : Function.Odd p5 := odd_const_mul_local odd_factorTwoCenteredP5 e
  have hp7odd : Function.Odd p7 := odd_const_mul_local odd_factorTwoCenteredP7 f
  have hp9odd : Function.Odd p9 := odd_const_mul_local odd_factorTwoCenteredP9 g
  rw [oldRetainedProfile_decompose]
  change fourCellOddCoreLocalBilinear (((p3 + p5) + p7) + p9)
      fourCellOddP11DirectTail = _
  rw [fourCellOddCoreLocalBilinear_add_left ((p3 + p5) + p7) p9
      fourCellOddP11DirectTail ((hp3.add hp5).add hp7) hp9
      contDiff_fourCellOddP11DirectTail
      ((hp3odd.add hp5odd).add hp7odd) hp9odd odd_fourCellOddP11DirectTail,
    fourCellOddCoreLocalBilinear_add_left (p3 + p5) p7
      fourCellOddP11DirectTail (hp3.add hp5) hp7
      contDiff_fourCellOddP11DirectTail (hp3odd.add hp5odd) hp7odd
      odd_fourCellOddP11DirectTail,
    fourCellOddCoreLocalBilinear_add_left p3 p5 fourCellOddP11DirectTail
      hp3 hp5 contDiff_fourCellOddP11DirectTail hp3odd hp5odd
      odd_fourCellOddP11DirectTail]
  dsimp only [p3, p5, p7, p9]
  rw [fourCellOddCoreLocalBilinear_const_mul_left centeredP3
      fourCellOddP11DirectTail contDiff_centeredP3_local
      contDiff_fourCellOddP11DirectTail odd_centeredP3_local
      odd_fourCellOddP11DirectTail d,
    fourCellOddCoreLocalBilinear_const_mul_left factorTwoCenteredP5
      fourCellOddP11DirectTail contDiff_factorTwoCenteredP5_local
      contDiff_fourCellOddP11DirectTail odd_factorTwoCenteredP5
      odd_fourCellOddP11DirectTail e,
    fourCellOddCoreLocalBilinear_const_mul_left factorTwoCenteredP7
      fourCellOddP11DirectTail contDiff_factorTwoCenteredP7_local
      contDiff_fourCellOddP11DirectTail odd_factorTwoCenteredP7
      odd_fourCellOddP11DirectTail f,
    fourCellOddCoreLocalBilinear_const_mul_left factorTwoCenteredP9
      fourCellOddP11DirectTail contDiff_factorTwoCenteredP9_local
      contDiff_fourCellOddP11DirectTail odd_factorTwoCenteredP9
      odd_fourCellOddP11DirectTail g]

private theorem oldBlockProjection_tail_row_expansion :
    fourCellOddCoreLocalBilinear fourCellOddP11OldBlockProjection
        fourCellOddP11DirectTail =
      fourCellOddP11OldBlockProjectionCoefficients 0 *
          fourCellOddCoreLocalBilinear centeredP3 fourCellOddP11DirectTail +
      fourCellOddP11OldBlockProjectionCoefficients 1 *
          fourCellOddCoreLocalBilinear factorTwoCenteredP5
            fourCellOddP11DirectTail +
      fourCellOddP11OldBlockProjectionCoefficients 2 *
          fourCellOddCoreLocalBilinear factorTwoCenteredP7
            fourCellOddP11DirectTail +
      fourCellOddP11OldBlockProjectionCoefficients 3 *
          fourCellOddCoreLocalBilinear factorTwoCenteredP9
            fourCellOddP11DirectTail := by
  let z := fourCellOddP11OldBlockProjectionCoefficients
  have hz : (![z 0, z 1, z 2, z 3] : Fin 4 → ℝ) = z := by
    funext i
    fin_cases i <;> simp
  have h := oldRetainedProfile_tail_row_expansion (z 0) (z 1) (z 2) (z 3)
  rw [hz] at h
  simpa only [z, fourCellOddP11OldBlockProjection] using h

private theorem fourCellOddP11OldBlockSchurPivot_expansion :
    fourCellOddP11OldBlockSchurPivot =
      fourCellOddCoreLocalQuadratic fourCellOddP11DirectTail +
        fourCellOddCoreLocalQuadratic fourCellOddP11OldBlockProjection -
        2 *
          (fourCellOddP11OldBlockProjectionCoefficients 0 *
              fourCellOddCoreLocalBilinear centeredP3
                fourCellOddP11DirectTail +
            fourCellOddP11OldBlockProjectionCoefficients 1 *
              fourCellOddCoreLocalBilinear factorTwoCenteredP5
                fourCellOddP11DirectTail +
            fourCellOddP11OldBlockProjectionCoefficients 2 *
              fourCellOddCoreLocalBilinear factorTwoCenteredP7
                fourCellOddP11DirectTail +
            fourCellOddP11OldBlockProjectionCoefficients 3 *
              fourCellOddCoreLocalBilinear factorTwoCenteredP9
                fourCellOddP11DirectTail) := by
  let negProj : ℝ → ℝ := fun x ↦ (-1 : ℝ) *
    fourCellOddP11OldBlockProjection x
  have hneg : ContDiff ℝ 1 negProj :=
    contDiff_const.mul contDiff_fourCellOddP11OldBlockProjection
  have hres : fourCellOddP11OldBlockResidual =
      fourCellOddP11DirectTail + negProj := by
    funext x
    unfold fourCellOddP11OldBlockResidual
    dsimp only [negProj]
    simp only [Pi.add_apply]
    ring
  unfold fourCellOddP11OldBlockSchurPivot
  rw [hres, fourCellOddCoreLocalQuadratic_add fourCellOddP11DirectTail
      negProj contDiff_fourCellOddP11DirectTail.continuous hneg.continuous]
  dsimp only [negProj]
  rw [fourCellOddCoreLocalBilinear_const_mul_right
      fourCellOddP11DirectTail fourCellOddP11OldBlockProjection
      contDiff_fourCellOddP11DirectTail
      contDiff_fourCellOddP11OldBlockProjection odd_fourCellOddP11DirectTail
      odd_fourCellOddP11OldBlockProjection (-1),
    fourCellOddCoreLocalQuadratic_const_mul fourCellOddP11OldBlockProjection
      contDiff_fourCellOddP11OldBlockProjection
      odd_fourCellOddP11OldBlockProjection (-1),
    fourCellOddCoreLocalBilinear_comm fourCellOddP11DirectTail
      fourCellOddP11OldBlockProjection
      contDiff_fourCellOddP11DirectTail.continuous
      contDiff_fourCellOddP11OldBlockProjection.continuous,
    oldBlockProjection_tail_row_expansion]
  ring

private theorem oldBlockProjection_one_tenth_coercive :
    (1 / 10 : ℝ) *
        (fourCellOddP11OldBlockProjectionCoefficients 0 ^ 2 +
          fourCellOddP11OldBlockProjectionCoefficients 1 ^ 2 +
          fourCellOddP11OldBlockProjectionCoefficients 2 ^ 2 +
          fourCellOddP11OldBlockProjectionCoefficients 3 ^ 2) ≤
      fourCellOddCoreLocalQuadratic fourCellOddP11OldBlockProjection := by
  let z := fourCellOddP11OldBlockProjectionCoefficients
  have h := one_tenth_coeff_sq_le_fourCellOddOldRetainedQuadratic
    (z 0) (z 1) (z 2) (z 3)
  have hz : (![z 0, z 1, z 2, z 3] : Fin 4 → ℝ) = z := by
    funext i
    fin_cases i <;> simp
  rw [hz] at h
  simpa only [z, fourCellOddP11OldBlockProjection] using h

/-- The analytic Schur pivot retains the structural floor `3/20`. -/
theorem three_div_twenty_lt_fourCellOddP11OldBlockSchurPivot :
    (3 / 20 : ℝ) < fourCellOddP11OldBlockSchurPivot := by
  have hexp := fourCellOddP11OldBlockSchurPivot_expansion
  have hcoercive := oldBlockProjection_one_tenth_coercive
  have hrow := fourCellOddP11OldBlockTailRow_sq_sum_lt_one_div_500
  have hdiag :=
    seventeen_div_oneHundred_lt_fourCellOddCoreLocalQuadratic_P11
  nlinarith [sq_nonneg
      (fourCellOddP11OldBlockProjectionCoefficients 0 - 10 *
        fourCellOddCoreLocalBilinear centeredP3 fourCellOddP11DirectTail),
    sq_nonneg
      (fourCellOddP11OldBlockProjectionCoefficients 1 - 10 *
        fourCellOddCoreLocalBilinear factorTwoCenteredP5
          fourCellOddP11DirectTail),
    sq_nonneg
      (fourCellOddP11OldBlockProjectionCoefficients 2 - 10 *
        fourCellOddCoreLocalBilinear factorTwoCenteredP7
          fourCellOddP11DirectTail),
    sq_nonneg
      (fourCellOddP11OldBlockProjectionCoefficients 3 - 10 *
        fourCellOddCoreLocalBilinear factorTwoCenteredP9
          fourCellOddP11DirectTail)]

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedSchurPivotFloorStructural
