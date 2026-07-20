import ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP11AnchorRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualRegularMomentSmallStructural

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP11AnchorCertificateStructural

noncomputable section

open YoshidaConstantBounds
open YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddP11ExactResidualTailCrossAlgebraicStructural
open YoshidaFourCellOddP11GalerkinFiniteSolveStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP11GalerkinResidualDualObstructionStructural
open YoshidaFourCellOddP11GalerkinResidualRegularMomentSmallStructural
open YoshidaFourCellOddP11GalerkinRieszStructural
open YoshidaFourCellOddP11GalerkinSolutionBoxStructural
open YoshidaFourCellOddP13AugmentedRankOneSchurStructural
open YoshidaFourCellOddP51SparseP11AnchorMassStructural
open YoshidaFourCellOddP51SparseP11AnchorRepresenterStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# The first-mode obstruction to the sparse `P11` anchor certificate

The common five-mode selector is invisible to every `P11+` mode.  In
particular, its distance from the exact old Galerkin row is bounded below by
the single `P11` coefficient.  That coefficient is already too large for the
proposed `7 / 10000` pivot budget, even before the other twenty high modes are
added.  Thus no choice of the five selector coefficients can discharge the
sparse-anchor premise.

This is a structural one-mode obstruction.  The proof uses the all-degree
Legendre/Bessel reduction, the exact algebraic-minus-regular formula for the
`P11` row, and rational enclosures of its four Galerkin coordinates.  It does
not enumerate the twenty-one high rows.
-/

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

/-- The exact algebraic part of the old-residual--`P11` row has a rational
lower margin. -/
theorem eightyOne_div_fortyThousand_lt_sparseP11_algebraicPart :
    (81 / 40000 : ℝ) <
      fourCellOddP11ExactResidualTailCrossAlgebraicPart := by
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
  nlinarith

/-- The first high normal row is bounded away from zero. -/
theorem nineteen_div_tenThousand_lt_sparseP11_P11_row :
    (19 / 10000 : ℝ) < fourCellOddP11ExactResidualTailCross := by
  rw [fourCellOddP11ExactResidualTailCross_eq_algebraicPart_sub_regular]
  have hregular :=
    abs_two_mul_halfWidth_mul_exactResidualRegularMoment_lt_one_eightThousand
  rw [abs_lt] at hregular
  unfold fourCellOddP11OldGalerkinResidual at ⊢
  nlinarith [eightyOne_div_fortyThousand_lt_sparseP11_algebraicPart]

private theorem sparseP11_first_high_row_eq_cross :
    fourCellOddCoreLocalBilinear
        fourCellOddP11GalerkinRetainedResidualProfile
        (fourCellOddFiniteRetainedBasis
          (Fin.natAdd 4 (0 : Fin 21) : Fin 25)) =
      fourCellOddP11ExactResidualTailCross := by
  unfold fourCellOddP11ExactResidualTailCross
    fourCellOddP11OldGalerkinResidual
  congr 1

/-- The complete sparse high-normal energy already exceeds the proposed
budget scale on its first (`P11`) summand. -/
theorem twentyThree_mul_nineteen_div_tenThousand_sq_lt_sparseP11HighEnergy :
    (23 : ℝ) * (19 / 10000 : ℝ) ^ 2 <
      fourCellOddP51SparseP11HighNormalResidualEnergy := by
  have hrow := nineteen_div_tenThousand_lt_sparseP11_P11_row
  have hrowSq : (19 / 10000 : ℝ) ^ 2 <
      fourCellOddP11ExactResidualTailCross ^ 2 := by
    nlinarith
  have hterm_nonneg (i : Fin 21) : 0 ≤
      (2 * (@fourCellOddFiniteRetainedDegree 24
          (Fin.natAdd 4 i : Fin 25) : ℝ) + 1) *
        fourCellOddCoreLocalBilinear
          fourCellOddP11GalerkinRetainedResidualProfile
          (fourCellOddFiniteRetainedBasis
            (Fin.natAdd 4 i : Fin 25)) ^ 2 := by
    positivity
  have hfirst := Finset.single_le_sum
    (fun i _hi ↦ hterm_nonneg i) (Finset.mem_univ (0 : Fin 21))
  change
    (2 * (@fourCellOddFiniteRetainedDegree 24
          (Fin.natAdd 4 (0 : Fin 21) : Fin 25) : ℝ) + 1) *
        fourCellOddCoreLocalBilinear
          fourCellOddP11GalerkinRetainedResidualProfile
          (fourCellOddFiniteRetainedBasis
            (Fin.natAdd 4 (0 : Fin 21) : Fin 25)) ^ 2 ≤
      fourCellOddP51SparseP11HighNormalResidualEnergy at hfirst
  rw [sparseP11_first_high_row_eq_cross] at hfirst
  norm_num [fourCellOddFiniteRetainedDegree] at hfirst
  nlinarith

private theorem coercivityConstant_lt_seven_div_twoHundredFifty :
    fourCellOddNineteenTwentiethsCoercivityConstant < (7 / 250 : ℝ) := by
  have hscalar := fourCellScalar_fine_bounds.1
  unfold fourCellOddNineteenTwentiethsCoercivityConstant
    fourCellOddLocalScalarMassCoefficient
  nlinarith

/-- Every common five-mode selector misses the proposed sparse-anchor
budget.  The strict reversal is independent of all five coefficients. -/
theorem sparseP11Anchor_budget_lt_selector_l2
    (b₁ b₃ b₅ b₇ b₉ : ℝ) :
    fourCellOddNineteenTwentiethsCoercivityConstant *
        (fourCellOddCoreLocalQuadratic
            fourCellOddP11GalerkinRetainedResidualProfile -
          (7 / 10000 : ℝ)) <
      ∫ x : ℝ in 0..1,
        fourCellOddP51SparseP11HighSelectorRepresenter
          b₁ b₃ b₅ b₇ b₉ x ^ 2 := by
  let d : ℝ := fourCellOddCoreLocalQuadratic
      fourCellOddP11GalerkinRetainedResidualProfile - (7 / 10000 : ℝ)
  have henergy :=
    twentyThree_mul_nineteen_div_tenThousand_sq_lt_sparseP11HighEnergy
  have hselector :=
    fourCellOddP51SparseP11HighNormalResidualEnergy_le_selector_l2
      b₁ b₃ b₅ b₇ b₉
  have hlower :
      (23 : ℝ) * (19 / 10000 : ℝ) ^ 2 <
        ∫ x : ℝ in 0..1,
          fourCellOddP51SparseP11HighSelectorRepresenter
            b₁ b₃ b₅ b₇ b₉ x ^ 2 :=
    henergy.trans_le hselector
  have hkappaPos := fourCellOddNineteenTwentiethsCoercivityConstant_pos
  by_cases hd : 0 < d
  · have hdUpper : d < (29 / 10000 : ℝ) := by
      dsimp only [d]
      have hQ :=
        fourCellOddCoreLocalQuadratic_exactGalerkinResidual_lt_nine_div_2500
      linarith
    have hbudgetUpper :
        fourCellOddNineteenTwentiethsCoercivityConstant * d <
          (7 / 250 : ℝ) * (29 / 10000 : ℝ) := by
      calc
        fourCellOddNineteenTwentiethsCoercivityConstant * d <
            (7 / 250 : ℝ) * d :=
          mul_lt_mul_of_pos_right
            coercivityConstant_lt_seven_div_twoHundredFifty hd
        _ < (7 / 250 : ℝ) * (29 / 10000 : ℝ) :=
          mul_lt_mul_of_pos_left hdUpper (by norm_num)
    change fourCellOddNineteenTwentiethsCoercivityConstant * d < _
    calc
      fourCellOddNineteenTwentiethsCoercivityConstant * d <
          (7 / 250 : ℝ) * (29 / 10000 : ℝ) := hbudgetUpper
      _ < (23 : ℝ) * (19 / 10000 : ℝ) ^ 2 := by norm_num
      _ < _ := hlower
  · have hdNonpos : d ≤ 0 := le_of_not_gt hd
    have hbudgetNonpos :
        fourCellOddNineteenTwentiethsCoercivityConstant * d ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hkappaPos.le hdNonpos
    change fourCellOddNineteenTwentiethsCoercivityConstant * d < _
    have hzeroLower : (0 : ℝ) <
        (23 : ℝ) * (19 / 10000 : ℝ) ^ 2 := by norm_num
    exact hbudgetNonpos.trans_lt (hzeroLower.trans hlower)

/-- Exact obstruction theorem: no concrete selector can prove the sparse
`P11` high-energy premise used by the final `P51` certificate assembly. -/
theorem not_exists_sparseP11Anchor_selector_certificate :
    ¬ ∃ b₁ b₃ b₅ b₇ b₉ : ℝ,
      (∫ x : ℝ in 0..1,
          fourCellOddP51SparseP11HighSelectorRepresenter
            b₁ b₃ b₅ b₇ b₉ x ^ 2) ≤
        fourCellOddNineteenTwentiethsCoercivityConstant *
          (fourCellOddCoreLocalQuadratic
              fourCellOddP11GalerkinRetainedResidualProfile -
            (7 / 10000 : ℝ)) := by
  rintro ⟨b₁, b₃, b₅, b₇, b₉, h⟩
  exact (not_lt_of_ge h)
    (sparseP11Anchor_budget_lt_selector_l2 b₁ b₃ b₅ b₇ b₉)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP11AnchorCertificateStructural
