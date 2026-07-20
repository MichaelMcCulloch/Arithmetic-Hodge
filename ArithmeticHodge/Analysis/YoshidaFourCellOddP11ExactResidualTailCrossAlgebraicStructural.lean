import ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreEntryBoundsStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedRankOneSchurStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11ExactResidualTailCrossAlgebraicStructural

noncomputable section

open YoshidaConstantBounds
open YoshidaFourCellOddP11CoreEntryBoundsStructural
open YoshidaFourCellOddP11GalerkinFiniteSolveStructural
open YoshidaFourCellOddP11GalerkinRieszStructural
open YoshidaFourCellOddP11GalerkinSolutionBoxStructural
open YoshidaFourCellOddP13AugmentedRankOneSchurStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityOperatorStructural

/-!
# Algebraic part of the exact old-residual--`P11` row

The exact mixed core row is an algebraic endpoint contribution minus one
wide-regular kernel moment.  Here the algebraic contribution is isolated at
the inverse-defined old Galerkin residual and bounded using only the public
coordinate box and a rational enclosure of `sqrt 2 * log 2`.
-/

/-- The rational and `sqrt 2 * log 2` part of the exact five-mode/`P11`
row, before subtracting the wide-regular moment. -/
def fourCellOddP11FiveModeAlgebraicRow
    (c d e f g : ℝ) : ℝ :=
  (93 / 6500 : ℝ) * c +
    (4502146249 / 292968750000 : ℝ) * d +
    (12448527116141 / 778198242187500 : ℝ) * e +
    (1683915269078387 / 101470947265625000 : ℝ) * f +
    (905665116028339 / 28610229492187500 : ℝ) * g +
    (Real.sqrt 2 * Real.log 2) *
      ((-(11639832 / 1220703125 : ℝ)) * c -
        (426354232 / 30517578125 : ℝ) * d -
        (12942923992 / 762939453125 : ℝ) * e -
        (209841256952 / 19073486328125 : ℝ) * f +
        (1843324002408 / 476837158203125 : ℝ) * g)

/-- Specialization of the algebraic row to
`q0 = P1 - projection_{P3,P5,P7,P9} P1`. -/
def fourCellOddP11ExactResidualTailCrossAlgebraicPart : ℝ :=
  fourCellOddP11FiveModeAlgebraicRow
    1 (-fourCellOddP11GalerkinRetainedSolution 0)
      (-fourCellOddP11GalerkinRetainedSolution 1)
      (-fourCellOddP11GalerkinRetainedSolution 2)
      (-fourCellOddP11GalerkinRetainedSolution 3)

/-- Exact separation of the mixed Schur scalar into its algebraic part and
the sole regular-kernel moment. -/
theorem fourCellOddP11ExactResidualTailCross_eq_algebraicPart_sub_regular :
    fourCellOddP11ExactResidualTailCross =
      fourCellOddP11ExactResidualTailCrossAlgebraicPart -
        2 * fourCellOperatorHalfWidth *
          fourCellOddP11CoreRegularMoment
            fourCellOddP11OldGalerkinResidual := by
  unfold fourCellOddP11ExactResidualTailCross
    fourCellOddP11OldGalerkinResidual
    fourCellOddP11GalerkinRetainedResidualProfile
  rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode,
    fourCellOddCoreLocalBilinear_fiveMode_P11_eq]
  unfold fourCellOddP11ExactResidualTailCrossAlgebraicPart
    fourCellOddP11FiveModeAlgebraicRow
  ring

private theorem sqrt_two_fine_bounds_local :
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

/-- A local rational enclosure tuned to the algebraic row. -/
private theorem sqrt_two_mul_log_two_bounds_local :
    (98025 / 100000 : ℝ) < Real.sqrt 2 * Real.log 2 ∧
      Real.sqrt 2 * Real.log 2 < (98027 / 100000 : ℝ) := by
  have hs := sqrt_two_fine_bounds_local
  have hlog := strict_log_two_fine_bounds
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfineLo :
      (1414213562 / 1000000000 : ℝ) *
          (69314718055 / 100000000000 : ℝ) <
        Real.sqrt 2 * Real.log 2 := by
    calc
      (1414213562 / 1000000000 : ℝ) *
          (69314718055 / 100000000000 : ℝ) <
          Real.sqrt 2 * (69314718055 / 100000000000 : ℝ) :=
        mul_lt_mul_of_pos_right hs.1 (by norm_num)
      _ < Real.sqrt 2 * Real.log 2 :=
        mul_lt_mul_of_pos_left hlog.1 hs0
  have hfineHi :
      Real.sqrt 2 * Real.log 2 <
        (1414213563 / 1000000000 : ℝ) *
          (69314718057 / 100000000000 : ℝ) := by
    calc
      Real.sqrt 2 * Real.log 2 <
          (1414213563 / 1000000000 : ℝ) * Real.log 2 :=
        mul_lt_mul_of_pos_right hs.2 hlog0
      _ < (1414213563 / 1000000000 : ℝ) *
          (69314718057 / 100000000000 : ℝ) :=
        mul_lt_mul_of_pos_left hlog.2 (by norm_num)
  constructor
  · exact (by norm_num : (98025 / 100000 : ℝ) <
        (1414213562 / 1000000000 : ℝ) *
          (69314718055 / 100000000000 : ℝ)).trans hfineLo
  · exact hfineHi.trans (by norm_num :
      (1414213563 / 1000000000 : ℝ) *
          (69314718057 / 100000000000 : ℝ) < 98027 / 100000)

set_option maxHeartbeats 2000000 in
/-- The nonregular contribution is positive and already below `7 / 2000`.
Thus only the single explicit regular moment remains in the proof of the
desired bound on `b`. -/
theorem fourCellOddP11ExactResidualTailCrossAlgebraicPart_bounds :
    0 < fourCellOddP11ExactResidualTailCrossAlgebraicPart ∧
      fourCellOddP11ExactResidualTailCrossAlgebraicPart < (7 / 2000 : ℝ) := by
  rcases fourCellOddP11GalerkinRetainedSolution_coordinate_bounds with
    ⟨hs0lo, hs0hi, hs1lo, hs1hi, hs2lo, hs2hi, hs3lo, hs3hi⟩
  rcases sqrt_two_mul_log_two_bounds_local with ⟨halphaLo, halphaHi⟩
  have halphaPos : 0 < Real.sqrt 2 * Real.log 2 := by
    linarith
  have hp0lo :
      (98025 / 100000 : ℝ) * (114 / 100) <
        (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 0 := by
    calc
      (98025 / 100000 : ℝ) * (114 / 100) <
          (Real.sqrt 2 * Real.log 2) * (114 / 100) :=
        mul_lt_mul_of_pos_right halphaLo (by norm_num)
      _ < (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 0 :=
        mul_lt_mul_of_pos_left hs0lo halphaPos
  have hp0hi :
      (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 0 <
        (98027 / 100000 : ℝ) * (115 / 100) := by
    calc
      (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 0 <
          (Real.sqrt 2 * Real.log 2) * (115 / 100) :=
        mul_lt_mul_of_pos_left hs0hi halphaPos
      _ < (98027 / 100000 : ℝ) * (115 / 100) :=
        mul_lt_mul_of_pos_right halphaHi (by norm_num)
  have hp1lo :
      (98027 / 100000 : ℝ) * (-(23 / 100 : ℝ)) <
        (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 1 := by
    calc
      (98027 / 100000 : ℝ) * (-(23 / 100 : ℝ)) <
          (Real.sqrt 2 * Real.log 2) * (-(23 / 100 : ℝ)) :=
        mul_lt_mul_of_neg_right halphaHi (by norm_num)
      _ < (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 1 :=
        mul_lt_mul_of_pos_left hs1lo halphaPos
  have hp1hi :
      (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 1 <
        (98025 / 100000 : ℝ) * (-(21 / 100 : ℝ)) := by
    calc
      (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 1 <
          (Real.sqrt 2 * Real.log 2) * (-(21 / 100 : ℝ)) :=
        mul_lt_mul_of_pos_left hs1hi halphaPos
      _ < (98025 / 100000 : ℝ) * (-(21 / 100 : ℝ)) :=
        mul_lt_mul_of_neg_right halphaLo (by norm_num)
  have hp2lo :
      (98027 / 100000 : ℝ) * (-(7 / 100 : ℝ)) <
        (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 2 := by
    calc
      (98027 / 100000 : ℝ) * (-(7 / 100 : ℝ)) <
          (Real.sqrt 2 * Real.log 2) * (-(7 / 100 : ℝ)) :=
        mul_lt_mul_of_neg_right halphaHi (by norm_num)
      _ < (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 2 :=
        mul_lt_mul_of_pos_left hs2lo halphaPos
  have hp2hi :
      (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 2 <
        (98025 / 100000 : ℝ) * (-(4 / 100 : ℝ)) := by
    calc
      (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 2 <
          (Real.sqrt 2 * Real.log 2) * (-(4 / 100 : ℝ)) :=
        mul_lt_mul_of_pos_left hs2hi halphaPos
      _ < (98025 / 100000 : ℝ) * (-(4 / 100 : ℝ)) :=
        mul_lt_mul_of_neg_right halphaLo (by norm_num)
  have hp3lo :
      (98025 / 100000 : ℝ) * (2 / 100) <
        (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 3 := by
    calc
      (98025 / 100000 : ℝ) * (2 / 100) <
          (Real.sqrt 2 * Real.log 2) * (2 / 100) :=
        mul_lt_mul_of_pos_right halphaLo (by norm_num)
      _ < (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 3 :=
        mul_lt_mul_of_pos_left hs3lo halphaPos
  have hp3hi :
      (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 3 <
        (98027 / 100000 : ℝ) * (3 / 100) := by
    calc
      (Real.sqrt 2 * Real.log 2) *
          fourCellOddP11GalerkinRetainedSolution 3 <
          (Real.sqrt 2 * Real.log 2) * (3 / 100) :=
        mul_lt_mul_of_pos_left hs3hi halphaPos
      _ < (98027 / 100000 : ℝ) * (3 / 100) :=
        mul_lt_mul_of_pos_right halphaHi (by norm_num)
  unfold fourCellOddP11ExactResidualTailCrossAlgebraicPart
    fourCellOddP11FiveModeAlgebraicRow
  constructor <;> nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11ExactResidualTailCrossAlgebraicStructural
