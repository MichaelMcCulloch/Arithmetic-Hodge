import ArithmeticHodge.Analysis.YoshidaFourCellOddP11ExplicitSelectorCauchyStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11LowerMassRegionStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailReserveThreeHalvesStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11JointFiniteTailStructural

noncomputable section

open CenteredOddOneThreeEnergy
open UnitIntervalLogEnergyAffine
open YoshidaEndpointOcticPotential
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
open YoshidaFourCellOddP11ConcreteWeightedDualClosureStructural
open YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
open YoshidaFourCellOddP11ExplicitSelectorCauchyStructural
open YoshidaFourCellOddP11LowerMassRegionStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddP11TailReserveThreeHalvesStructural
open YoshidaFourCellOddP11ThreeHalvesClosureStructural
open YoshidaFourCellOddP11WeightedDualSelectorStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFactorTwoPhaseIntrinsicResidual

/-!
# Joint finite--tail constants for the odd `P₁₁+` closure

The explicit adversarial selector pair determines an exact lower threshold
for any matched-factor five-mode Cauchy theorem: the factor must be strictly
larger than `45 / 44`.  In particular it kills factor one but does not kill
the proposed factor `3 / 2`.

There is also no way to spend the prospective `17 / 1000` pivot slack on the
corrected-cross row independently.  Together with a `23 / 100` pure `P₁`
row estimate, such a bound would reconstruct the already-disproved factor-one
joint Loewner certificate.  Any successful proof must therefore retain
finite--tail correlation, or spend genuine tail reserve through a matched
factor greater than one.
-/

/-- The public rational bounds for the adversarial pair meet exactly at the
factor `45 / 44`.  This is the strongest factor reversal certified by those
three bounds alone. -/
theorem cauchyWitness_strictly_reverses_fiveModeCauchy_at_45_div_44 :
    fourCellOddCoreLocalQuadratic fourCellOddP11CauchyLowWitness *
        ((45 / 44 : ℝ) *
          fourCellOddP1ExactTailWeight fourCellOddP11CauchyTailWitness) <
      fourCellOddCoreLocalBilinear fourCellOddP11CauchyLowWitness
          fourCellOddP11CauchyTailWitness ^ 2 := by
  have hQ := fourCellOddCoreLocalQuadratic_cauchyLow_lt
  have hW := fourCellOddP1ExactTailWeight_cauchyTail_lt
  have hB := fourCellOddCoreLocalBilinear_cauchyLow_tail_gt
  have hQ0 : 0 ≤ fourCellOddCoreLocalQuadratic
      fourCellOddP11CauchyLowWitness := by
    unfold fourCellOddP11CauchyLowWitness
    rw [fourCellOddCoreLocalQuadratic_fiveMode_eq_coreExpression]
    exact fourCellOddFiveModeCoreExpression_nonneg _ _ _ _ _
  have hW0 : 0 ≤ fourCellOddP1ExactTailWeight
      fourCellOddP11CauchyTailWitness :=
    fourCellOddP1ExactTailWeight_nonneg
      fourCellOddP11CauchyTailWitness
      contDiff_fourCellOddP11CauchyTailWitness.continuous
  have hproduct :
      fourCellOddCoreLocalQuadratic fourCellOddP11CauchyLowWitness *
          fourCellOddP1ExactTailWeight fourCellOddP11CauchyTailWitness <
        (11 / 5000 : ℝ) * (2 / 125 : ℝ) := by
    calc
      fourCellOddCoreLocalQuadratic fourCellOddP11CauchyLowWitness *
          fourCellOddP1ExactTailWeight fourCellOddP11CauchyTailWitness ≤
        (11 / 5000 : ℝ) *
          fourCellOddP1ExactTailWeight fourCellOddP11CauchyTailWitness :=
        mul_le_mul_of_nonneg_right hQ.le hW0
      _ < (11 / 5000 : ℝ) * (2 / 125 : ℝ) :=
        mul_lt_mul_of_pos_left hW (by norm_num)
  have hscaled := mul_lt_mul_of_pos_left hproduct (show (0 : ℝ) < 45 / 44 by norm_num)
  calc
    fourCellOddCoreLocalQuadratic fourCellOddP11CauchyLowWitness *
        ((45 / 44 : ℝ) *
          fourCellOddP1ExactTailWeight fourCellOddP11CauchyTailWitness) =
      (45 / 44 : ℝ) *
        (fourCellOddCoreLocalQuadratic fourCellOddP11CauchyLowWitness *
          fourCellOddP1ExactTailWeight fourCellOddP11CauchyTailWitness) := by ring
    _ < (45 / 44 : ℝ) * ((11 / 5000 : ℝ) * (2 / 125 : ℝ)) :=
      hscaled
    _ = (3 / 500 : ℝ) ^ 2 := by norm_num
    _ < fourCellOddCoreLocalBilinear fourCellOddP11CauchyLowWitness
          fourCellOddP11CauchyTailWitness ^ 2 := by nlinarith

/-- Consequently every universal matched five-mode factor lies strictly
above `45 / 44`.  This is an operator-norm obstruction, not a truncation of
the tail: the witness itself is an exact `P₁₁+` polynomial. -/
theorem factor_gt_45_div_44_of_fiveModeCauchy
    (kappa : ℝ) (hcauchy : FourCellOddP11FiveModeCauchyAtFactor kappa) :
    (45 / 44 : ℝ) < kappa := by
  rcases fourCellOddP11CauchyTailWitness_moments with
    ⟨hone, hthree, hfive, hseven, hnine⟩
  have hc := hcauchy
    (-(9 / 10 : ℝ)) 1 (-(1 / 5 : ℝ)) 0 (1 / 10 : ℝ)
    fourCellOddP11CauchyTailWitness
    contDiff_fourCellOddP11CauchyTailWitness
    odd_fourCellOddP11CauchyTailWitness
    hone hthree hfive hseven hnine
  change
    fourCellOddCoreLocalBilinear fourCellOddP11CauchyLowWitness
          fourCellOddP11CauchyTailWitness ^ 2 ≤
      fourCellOddCoreLocalQuadratic fourCellOddP11CauchyLowWitness *
        (kappa * fourCellOddP1ExactTailWeight
          fourCellOddP11CauchyTailWitness) at hc
  have hreverse :=
    cauchyWitness_strictly_reverses_fiveModeCauchy_at_45_div_44
  have hQ0 : 0 ≤ fourCellOddCoreLocalQuadratic
      fourCellOddP11CauchyLowWitness := by
    unfold fourCellOddP11CauchyLowWitness
    rw [fourCellOddCoreLocalQuadratic_fiveMode_eq_coreExpression]
    exact fourCellOddFiveModeCoreExpression_nonneg _ _ _ _ _
  have hW0 : 0 ≤ fourCellOddP1ExactTailWeight
      fourCellOddP11CauchyTailWitness :=
    fourCellOddP1ExactTailWeight_nonneg
      fourCellOddP11CauchyTailWitness
      contDiff_fourCellOddP11CauchyTailWitness.continuous
  have hQWpos : 0 <
      fourCellOddCoreLocalQuadratic fourCellOddP11CauchyLowWitness *
        fourCellOddP1ExactTailWeight fourCellOddP11CauchyTailWitness := by
    have hQW0 := mul_nonneg hQ0 hW0
    by_contra hnot
    have hzero :
        fourCellOddCoreLocalQuadratic fourCellOddP11CauchyLowWitness *
          fourCellOddP1ExactTailWeight fourCellOddP11CauchyTailWitness = 0 :=
      le_antisymm (not_lt.mp hnot) hQW0
    have hright :
        fourCellOddCoreLocalQuadratic fourCellOddP11CauchyLowWitness *
          (kappa * fourCellOddP1ExactTailWeight
            fourCellOddP11CauchyTailWitness) = 0 := by
      calc
        _ = kappa *
            (fourCellOddCoreLocalQuadratic fourCellOddP11CauchyLowWitness *
              fourCellOddP1ExactTailWeight fourCellOddP11CauchyTailWitness) := by
                ring
        _ = 0 := by rw [hzero]; ring
    rw [hright] at hc
    nlinarith
  have hstrict := hreverse.trans_le hc
  nlinarith

/-- The known witness threshold is strictly below the proposed matched
factor.  This does not assert the `3 / 2` theorem; it records that the sharp
current obstruction is compatible with it. -/
theorem fortyFive_div_fortyFour_lt_threeHalves :
    (45 / 44 : ℝ) < 3 / 2 := by
  norm_num

/-- The exact harmonic-eleven gap already contributes more than three full
copies of intrinsic `L²` energy to the global raw reserve.  Thus the global
spectral part is not the numerical obstruction to a `3 / 2` matched tail
reserve; the remaining issue is retaining that surplus through the strip and
potential decomposition. -/
theorem three_mul_intrinsicEnergy_le_raw_div_four_of_P11Plus
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    3 * factorTwoIntrinsicEnergy r ≤ centeredRawLogEnergy r / 4 := by
  have hgap := harmonic_eleven_mul_intrinsicEnergy_le_raw_div_four_of_P11Plus
    r hr hodd h1 h3 h5 h7 h9
  have hh : (3 : ℝ) ≤ harmonic 11 := by
    norm_num [harmonic, Finset.sum_range_succ]
  exact (mul_le_mul_of_nonneg_right hh
    (factorTwoIntrinsicEnergy_nonneg r)).trans hgap

/-- Prospective pure `P₁` selector estimate supplied by the reciprocal
majorant calculation.  It is isolated as a proposition so the finite--tail
algebra can be audited independently of that analytic proof. -/
def FourCellOddP11PureP1RowAtTwentyThreeHundredths : Prop :=
  ∀ (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    fourCellOddCoreLocalBilinear centeredP1 r ^ 2 ≤
      (23 / 100 : ℝ) * fourCellOddP1ExactTailWeight r

/-- The tempting independent allocation of the remaining pivot slack to the
corrected-cross row. -/
def FourCellOddP11CorrectedCrossAtSeventeenThousandths : Prop :=
  ∀ (d e f g : ℝ) (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    fourCellOddP11FiniteTailCorrectedCross d e f g r ^ 2 ≤
      (17 / 1000 : ℝ) *
        fourCellOddP11FiniteCorrectedReserve d e f g *
          fourCellOddP1ExactTailWeight r

/-- Spending `23 / 100 + 17 / 1000 = 247 / 1000` independently lies below
the true `P₁` pivot, and therefore recreates the factor-one joint weighted
dual certificate. -/
theorem jointWeightedDual_of_pure23_and_cross17
    (hpure : FourCellOddP11PureP1RowAtTwentyThreeHundredths)
    (hcross : FourCellOddP11CorrectedCrossAtSeventeenThousandths) :
    FourCellOddP11CoupledJointWeightedDualCertificate := by
  intro d e f g r hr hodd h1 h3 h5 h7 h9
  have hP := hpure r hr hodd h1 h3 h5 h7 h9
  have hX := hcross d e f g r hr hodd h1 h3 h5 h7 h9
  have hF : 0 ≤ fourCellOddP11FiniteCorrectedReserve d e f g :=
    fourCellOddP11FiniteCorrectedReserve_nonnegative d e f g
  have hW : 0 ≤ fourCellOddP1ExactTailWeight r :=
    fourCellOddP1ExactTailWeight_nonneg r hr.continuous
  have hA : (247 / 1000 : ℝ) <
      fourCellOddCoreLocalQuadratic centeredP1 := by
    rw [fourCellOddCoreLocalQuadratic_centeredP1_eq_perturbed11]
    rcases fourCellOddOneThreeFivePerturbed_entry_bounds with ⟨hAlo, _⟩
    linarith
  constructor
  · exact hP.trans (mul_le_mul_of_nonneg_right (by linarith) hW)
  · have hFP := mul_le_mul_of_nonneg_left hP hF
    have hFA :
        fourCellOddP11FiniteCorrectedReserve d e f g *
              (247 / 1000 : ℝ) * fourCellOddP1ExactTailWeight r ≤
          fourCellOddP11FiniteCorrectedReserve d e f g *
            fourCellOddCoreLocalQuadratic centeredP1 *
              fourCellOddP1ExactTailWeight r := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hA.le hF) hW
    calc
      fourCellOddP11FiniteCorrectedReserve d e f g *
            fourCellOddCoreLocalBilinear centeredP1 r ^ 2 +
          fourCellOddP11FiniteTailCorrectedCross d e f g r ^ 2 ≤
        fourCellOddP11FiniteCorrectedReserve d e f g *
              ((23 / 100 : ℝ) * fourCellOddP1ExactTailWeight r) +
            (17 / 1000 : ℝ) *
              fourCellOddP11FiniteCorrectedReserve d e f g *
                fourCellOddP1ExactTailWeight r := add_le_add hFP hX
      _ = fourCellOddP11FiniteCorrectedReserve d e f g *
            (247 / 1000 : ℝ) * fourCellOddP1ExactTailWeight r := by ring
      _ ≤ fourCellOddP11FiniteCorrectedReserve d e f g *
            fourCellOddCoreLocalQuadratic centeredP1 *
              fourCellOddP1ExactTailWeight r := hFA

/-- Sharp obstruction to the independent `17 / 1000` allocation: it cannot
coexist with the prospective `23 / 100` pure-row estimate. -/
theorem not_pure23_and_independent_cross17 :
    ¬ (FourCellOddP11PureP1RowAtTwentyThreeHundredths ∧
      FourCellOddP11CorrectedCrossAtSeventeenThousandths) := by
  rintro ⟨hpure, hcross⟩
  apply not_fourCellOddP11CoupledSelectorLoewnerCertificate
  exact fourCellOddP11CoupledSelectorLoewnerCertificate_iff_joint.mpr
    (jointWeightedDual_of_pure23_and_cross17 hpure hcross)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11JointFiniteTailStructural
