import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotCombinedReserveStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusPositiveStructural

noncomputable section

open ThreeByThreeRankOneSchur
open ThreeByThreeConvexPencil
open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Positivity of the corrected positive static block

The first Schur pivot is treated without separately boxing the nearly
parallel `P0/P2` entries.  A fixed rational lower Gram retains the exact two
`P4` crosses.  Its Loewner remainder is proved from the shared clean and
perturbation forms before any scalar estimate is taken.  The corrected first
alternating column is then controlled in the sum/difference coordinates used
by the sharp structural alternating bounds.
-/

/-! ## A cancellation-preserving rational lower even Gram -/

private def plusLower00 : ℝ := 13836 / 100000
private def plusLower02 : ℝ := 13544 / 100000
private def plusLower22 : ℝ := 13817 / 100000
private def plusP4Lower : ℝ := 3439 / 25000

private def plusModelDefect00 : ℝ :=
  yoshidaEndpointEvenLowGram00 + evenPositivePerturbationTaylor00 - plusLower00

private def plusModelDefect02 : ℝ :=
  yoshidaEndpointEvenLowGram02 + evenPositivePerturbationTaylor02 - plusLower02

private def plusModelDefect22 : ℝ :=
  yoshidaEndpointEvenLowGram22 + evenPositivePerturbationTaylor22 - plusLower22

private theorem plusModelDefect_bounds :
    (57 / 1000000 : ℝ) < plusModelDefect00 ∧
      |plusModelDefect02| < (51 / 1000000 : ℝ) ∧
      (53 / 1000000 : ℝ) < plusModelDefect22 := by
  have hc00 := intrinsicEven_cleanGram00_gt
  have hc02 := intrinsicEven_cleanGram02_bounds
  have hc22 := intrinsicEven_cleanGram22_gt
  have ht := evenPositivePerturbationTaylor_ultra_bounds
  unfold plusModelDefect00 plusModelDefect02 plusModelDefect22
    plusLower00 plusLower02 plusLower22
  constructor
  · nlinarith
  constructor
  · rw [abs_lt]
    constructor <;> nlinarith
  · nlinarith

private theorem plusModelDefect_det_pos :
    0 < plusModelDefect00 * plusModelDefect22 - plusModelDefect02 ^ 2 := by
  rcases plusModelDefect_bounds with ⟨h00, h02, h22⟩
  have h00pos : 0 < plusModelDefect00 :=
    (by norm_num : (0 : ℝ) < 57 / 1000000).trans h00
  have hprod :
      (57 / 1000000 : ℝ) * (53 / 1000000) <
        plusModelDefect00 * plusModelDefect22 :=
    mul_lt_mul h00 h22.le (by norm_num) h00pos.le
  have h02' := abs_lt.mp h02
  have hsq : plusModelDefect02 ^ 2 < (51 / 1000000 : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h02'.2)
      (by linarith : 0 < plusModelDefect02 + 51 / 1000000)]
  have hrat :
      (51 / 1000000 : ℝ) ^ 2 <
        (57 / 1000000) * (53 / 1000000) := by
    norm_num
  nlinarith

private theorem plusModelDefect_quadratic_pos
    (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
    0 < plusModelDefect00 * c ^ 2 +
      2 * plusModelDefect02 * c * d + plusModelDefect22 * d ^ 2 := by
  exact real_twoByTwo_quadratic_pos _ _ _ c d
    ((by norm_num : (0 : ℝ) < 57 / 1000000).trans plusModelDefect_bounds.1)
    plusModelDefect_det_pos hne

private theorem plusCombinedModel_quadratic_le_exact (c d : ℝ) :
    (yoshidaEndpointEvenLowGram00 + evenPositivePerturbationTaylor00) * c ^ 2 +
        2 * (yoshidaEndpointEvenLowGram02 + evenPositivePerturbationTaylor02) *
          c * d +
        (yoshidaEndpointEvenLowGram22 + evenPositivePerturbationTaylor22) *
          d ^ 2 ≤
      factorTwoStructuralPhaseLow00 1 * c ^ 2 +
        2 * factorTwoStructuralPhaseLow02 1 * c * d +
        factorTwoStructuralPhaseLow22 1 * d ^ 2 := by
  have hpert := evenPositivePerturbationTaylor_quadratic_le c d
  have hclean :
      yoshidaEndpointOddCleanQuadratic (factorTwoEvenStructuralLowProfile c d) =
        yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * d +
          yoshidaEndpointEvenLowGram22 * d ^ 2 := by
    simpa only [factorTwoEvenStructuralLowProfile] using
      yoshidaEndpointEvenLowGram_quadratic_eq_clean c d
  rw [factorTwoStructuralPhaseLow_endpoint_quadratic, hclean]
  nlinarith

private theorem plusLowRemainder_quadratic_nonneg (c d : ℝ) :
    0 ≤ (factorTwoStructuralPhaseLow00 1 - plusLower00) * c ^ 2 +
      2 * (factorTwoStructuralPhaseLow02 1 - plusLower02) * c * d +
      (factorTwoStructuralPhaseLow22 1 - plusLower22) * d ^ 2 := by
  by_cases hne : c ≠ 0 ∨ d ≠ 0
  · have hstrict := plusModelDefect_quadratic_pos c d hne
    have hmodel := plusCombinedModel_quadratic_le_exact c d
    unfold plusModelDefect00 plusModelDefect02 plusModelDefect22 at hstrict
    nlinarith
  · push_neg at hne
    rcases hne with ⟨rfl, rfl⟩
    norm_num

private theorem plusP4Lower_lt_exact :
    plusP4Lower < factorTwoIntrinsicSixUnbalancedEPlus44 := by
  have hclean :=
    one_thousand_five_hundred_seventy_one_five_thousandths_lt_clean_p4
  have hpert := factorTwoCenteredSymmetricPerturbation_p4_lower
  unfold factorTwoIntrinsicSixUnbalancedEPlus44 plusP4Lower
    factorTwoIntrinsicP4PhaseDiagonal
  norm_num at hclean hpert ⊢
  nlinarith

private theorem plusEvenRemainder_quadratic_nonneg (c0 c2 c4 : ℝ) :
    0 ≤
      (factorTwoIntrinsicSixUnbalancedEPlus00 - plusLower00) * c0 ^ 2 +
        2 * (factorTwoIntrinsicSixUnbalancedEPlus02 - plusLower02) * c0 * c2 +
        (factorTwoIntrinsicSixUnbalancedEPlus22 - plusLower22) * c2 ^ 2 +
        (factorTwoIntrinsicSixUnbalancedEPlus44 - plusP4Lower) * c4 ^ 2 := by
  have hlow := plusLowRemainder_quadratic_nonneg c0 c2
  have htail :
      0 ≤ (factorTwoIntrinsicSixUnbalancedEPlus44 - plusP4Lower) * c4 ^ 2 :=
    mul_nonneg (sub_nonneg.mpr plusP4Lower_lt_exact.le) (sq_nonneg c4)
  simpa only [factorTwoIntrinsicSixUnbalancedEPlus00,
    factorTwoIntrinsicSixUnbalancedEPlus02,
    factorTwoIntrinsicSixUnbalancedEPlus22] using add_nonneg hlow htail

/-! ## The first corrected lower Schur reserve -/

/-- The lower determinant and its first corrected adjugate reserve are kept
in sum/difference coordinates.  This is the coordinate system in which all
six inputs have short, structurally proved intervals. -/
private def plusLowerT11Reserve
    (S D s d a o : ℝ) : ℝ :=
  let r := (S - D) / 2
  let q := (S + D) / 2
  let k0 := (s + d) / 4 - 63 / 1000
  let k2 := (s - d) / 4 - 577 / 10000
  let k4 := a / 2 - 169 / 5000
  symmetricDeterminant plusLower00 plusLower02 r plusLower22 q plusP4Lower * o -
    adjugateQuadratic plusLower00 plusLower02 r plusLower22 q plusP4Lower
      k0 k2 k4

private theorem plusLowerT11Reserve_corner_pos :
    0 < plusLowerT11Reserve
      (193081 / 1000000) (19581 / 1000000)
      (56173 / 100000) (1687 / 100000)
      (141 / 1000) (1578 / 10000) := by
  norm_num [plusLowerT11Reserve, plusLower00, plusLower02,
    plusLower22, plusP4Lower, symmetricDeterminant, adjugateQuadratic]

private def plusLowerT11ReserveASlope
    (S D s d a : ℝ) : ℝ :=
  -56057551 / 50000000000000 - 1933019 / 10000000000 * a +
    143917 / 200000000 * D - 170237 / 1000000000 * S -
    54741 / 800000 * D * d + 19 / 800000 * D * s -
    19 / 800000 * S * d + 113 / 160000 * S * s

private def plusLowerT11ReserveDStepSlope
    (S D s d : ℝ) : ℝ :=
  78359447987 / 4000000000000000 -
    188254299 / 40000000000 * d + 65341 / 20000000000 * s -
    20089947 / 4000000000 * D - 6973 / 4000000000 * S -
    1207 / 40000 * S * D - 433 / 1600000 * S ^ 2 +
    (1 / 8 : ℝ) * S * D * s + (1 / 16 : ℝ) * S ^ 2 * d

private def plusLowerT11ReserveSStepSlope
    (S D s : ℝ) : ℝ :=
  -15254437641 / 4000000000000000 -
    388607 / 8000000000 * s + 6973 / 4000000000 * D +
    41471 / 800000000 * S + 7893 / 1600000 * D ^ 2 +
    627 / 800000 * S * D + (1 / 16 : ℝ) * D ^ 2 * s

private def plusLowerT11ReserveCapitalDStepSlope
    (S D : ℝ) : ℝ :=
  -52514179713811 / 160000000000000000 -
    2429138831 / 160000000000 * D + 18885411 / 80000000000 * S

private def plusLowerT11ReserveCapitalSStepSlope (S : ℝ) : ℝ :=
  -3415180623169 / 160000000000000000 -
    35269671 / 160000000000 * S

private theorem plusLowerT11Reserve_a_difference
    (S D s d a : ℝ) :
    plusLowerT11Reserve S D s d a (1578 / 10000) -
        plusLowerT11Reserve S D s d (141 / 1000) (1578 / 10000) =
      (a - 141 / 1000) * plusLowerT11ReserveASlope S D s d a := by
  unfold plusLowerT11Reserve plusLowerT11ReserveASlope
    plusLower00 plusLower02 plusLower22 plusP4Lower
    symmetricDeterminant adjugateQuadratic
  ring

private theorem plusLowerT11Reserve_d_difference
    (S D s d : ℝ) :
    plusLowerT11Reserve S D s d (141 / 1000) (1578 / 10000) -
        plusLowerT11Reserve S D s (1687 / 100000)
          (141 / 1000) (1578 / 10000) =
      (d - 1687 / 100000) * plusLowerT11ReserveDStepSlope S D s d := by
  unfold plusLowerT11Reserve plusLowerT11ReserveDStepSlope
    plusLower00 plusLower02 plusLower22 plusP4Lower
    symmetricDeterminant adjugateQuadratic
  ring

private theorem plusLowerT11Reserve_s_difference
    (S D s : ℝ) :
    plusLowerT11Reserve S D s (1687 / 100000)
          (141 / 1000) (1578 / 10000) -
        plusLowerT11Reserve S D (56173 / 100000) (1687 / 100000)
          (141 / 1000) (1578 / 10000) =
      (s - 56173 / 100000) * plusLowerT11ReserveSStepSlope S D s := by
  unfold plusLowerT11Reserve plusLowerT11ReserveSStepSlope
    plusLower00 plusLower02 plusLower22 plusP4Lower
    symmetricDeterminant adjugateQuadratic
  ring

private theorem plusLowerT11Reserve_capitalD_difference
    (S D : ℝ) :
    plusLowerT11Reserve S D (56173 / 100000) (1687 / 100000)
          (141 / 1000) (1578 / 10000) -
        plusLowerT11Reserve S (19581 / 1000000)
          (56173 / 100000) (1687 / 100000)
          (141 / 1000) (1578 / 10000) =
      (D - 19581 / 1000000) *
        plusLowerT11ReserveCapitalDStepSlope S D := by
  unfold plusLowerT11Reserve plusLowerT11ReserveCapitalDStepSlope
    plusLower00 plusLower02 plusLower22 plusP4Lower
    symmetricDeterminant adjugateQuadratic
  ring

private theorem plusLowerT11Reserve_capitalS_difference
    (S : ℝ) :
    plusLowerT11Reserve S (19581 / 1000000)
          (56173 / 100000) (1687 / 100000)
          (141 / 1000) (1578 / 10000) -
        plusLowerT11Reserve (193081 / 1000000) (19581 / 1000000)
          (56173 / 100000) (1687 / 100000)
          (141 / 1000) (1578 / 10000) =
      (S - 193081 / 1000000) * plusLowerT11ReserveCapitalSStepSlope S := by
  unfold plusLowerT11Reserve plusLowerT11ReserveCapitalSStepSlope
    plusLower00 plusLower02 plusLower22 plusP4Lower
    symmetricDeterminant adjugateQuadratic
  ring

private theorem plusLowerT11ReserveASlope_pos
    (S D s d a : ℝ)
    (hS : (185634 / 1000000 : ℝ) < S ∧ S < 193081 / 1000000)
    (hD : (15634 / 1000000 : ℝ) < D ∧ D < 19581 / 1000000)
    (hs : (56168 / 100000 : ℝ) < s ∧ s < 56173 / 100000)
    (hd : (1687 / 100000 : ℝ) < d ∧ d < 1692 / 100000)
    (ha : a < (144 / 1000 : ℝ)) :
    0 < plusLowerT11ReserveASlope S D s d a := by
  let cD : ℝ :=
    143917 / 200000000 - 54741 / 800000 * d + 19 / 800000 * s
  let cS : ℝ :=
    -170237 / 1000000000 - 19 / 800000 * d + 113 / 160000 * s
  have hcDL :
      (143917 / 200000000 : ℝ) -
          54741 / 800000 * (1692 / 100000) +
          19 / 800000 * (56168 / 100000) < cD := by
    dsimp only [cD]
    nlinarith
  have hcD0 : cD < 0 := by
    dsimp only [cD]
    nlinarith
  have hcSL :
      (-170237 / 1000000000 : ℝ) -
          19 / 800000 * (1692 / 100000) +
          113 / 160000 * (56168 / 100000) < cS := by
    dsimp only [cS]
    nlinarith
  have hcS0 : 0 < cS := by
    dsimp only [cS]
    nlinarith
  have hDterm :
      (19581 / 1000000 : ℝ) *
          ((143917 / 200000000 : ℝ) -
            54741 / 800000 * (1692 / 100000) +
            19 / 800000 * (56168 / 100000)) < D * cD := by
    calc
      _ < (19581 / 1000000 : ℝ) * cD :=
        mul_lt_mul_of_pos_left hcDL (by norm_num)
      _ < D * cD := mul_lt_mul_of_neg_right hD.2 hcD0
  have hSterm :
      (185634 / 1000000 : ℝ) *
          ((-170237 / 1000000000 : ℝ) -
            19 / 800000 * (1692 / 100000) +
            113 / 160000 * (56168 / 100000)) < S * cS := by
    calc
      _ < (185634 / 1000000 : ℝ) * cS :=
        mul_lt_mul_of_pos_left hcSL (by norm_num)
      _ < S * cS := mul_lt_mul_of_pos_right hS.1 hcS0
  have haTerm :
      -(1933019 / 10000000000 : ℝ) * a >
        -(1933019 / 10000000000 : ℝ) * (144 / 1000) := by
    exact mul_lt_mul_of_neg_left ha (by norm_num)
  have heq :
      plusLowerT11ReserveASlope S D s d a =
        -56057551 / 50000000000000 - 1933019 / 10000000000 * a +
          D * cD + S * cS := by
    unfold plusLowerT11ReserveASlope
    dsimp only [cD, cS]
    ring_nf
  rw [heq]
  norm_num at hDterm hSterm haTerm ⊢
  linarith

private theorem plusLowerT11ReserveDStepSlope_pos
    (S D s d : ℝ)
    (hS : (185634 / 1000000 : ℝ) < S ∧ S < 193081 / 1000000)
    (hD : (15634 / 1000000 : ℝ) < D ∧ D < 19581 / 1000000)
    (hs : (56168 / 100000 : ℝ) < s ∧ s < 56173 / 100000)
    (hd : (1687 / 100000 : ℝ) < d ∧ d < 1692 / 100000) :
    0 < plusLowerT11ReserveDStepSlope S D s d := by
  let cs : ℝ := s / 8 - 1207 / 40000
  let cd : ℝ := d / 16 - 433 / 1600000
  have hcsL :
      (56168 / 100000 : ℝ) / 8 - 1207 / 40000 < cs := by
    dsimp only [cs]
    linarith
  have hcs0 : 0 < cs := by
    dsimp only [cs]
    nlinarith
  have hcdL :
      (1687 / 100000 : ℝ) / 16 - 433 / 1600000 < cd := by
    dsimp only [cd]
    linarith
  have hcd0 : 0 < cd := by
    dsimp only [cd]
    nlinarith
  have hqD :
      0 < -20089947 / 4000000000 + S * cs := by
    have hmul :
        (185634 / 1000000 : ℝ) *
            ((56168 / 100000 : ℝ) / 8 - 1207 / 40000) < S * cs := by
      calc
        _ < (185634 / 1000000 : ℝ) * cs :=
          mul_lt_mul_of_pos_left hcsL (by norm_num)
        _ < S * cs := mul_lt_mul_of_pos_right hS.1 hcs0
    norm_num at hmul ⊢
    linarith
  have hDmono :
      plusLowerT11ReserveDStepSlope S (15634 / 1000000) s d <
        plusLowerT11ReserveDStepSlope S D s d := by
    have heq :
        plusLowerT11ReserveDStepSlope S D s d -
            plusLowerT11ReserveDStepSlope S (15634 / 1000000) s d =
          (D - 15634 / 1000000) *
            (-20089947 / 4000000000 + S * cs) := by
      unfold plusLowerT11ReserveDStepSlope
      dsimp only [cs]
      ring
    have hprod :
        0 < (D - 15634 / 1000000) *
          (-20089947 / 4000000000 + S * cs) :=
      mul_pos (sub_pos.mpr hD.1) hqD
    nlinarith
  have hqS :
      0 < -6973 / 4000000000 +
        (15634 / 1000000 : ℝ) * cs +
        (S + 185634 / 1000000) * cd := by
    have hcsTerm :
        (15634 / 1000000 : ℝ) *
            ((56168 / 100000 : ℝ) / 8 - 1207 / 40000) <
          (15634 / 1000000) * cs :=
      mul_lt_mul_of_pos_left hcsL (by norm_num)
    have hsum : (2 * (185634 / 1000000 : ℝ)) <
        S + 185634 / 1000000 := by
      linarith [hS.1]
    have hcdTerm :
        (2 * (185634 / 1000000 : ℝ)) *
            ((1687 / 100000 : ℝ) / 16 - 433 / 1600000) <
          (S + 185634 / 1000000) * cd := by
      calc
        _ < (2 * (185634 / 1000000 : ℝ)) * cd :=
          mul_lt_mul_of_pos_left hcdL (by norm_num)
        _ < (S + 185634 / 1000000) * cd :=
          mul_lt_mul_of_pos_right hsum hcd0
    norm_num at hcsTerm hcdTerm ⊢
    linarith
  have hSmono :
      plusLowerT11ReserveDStepSlope
          (185634 / 1000000) (15634 / 1000000) s d <
        plusLowerT11ReserveDStepSlope S (15634 / 1000000) s d := by
    have heq :
        plusLowerT11ReserveDStepSlope S (15634 / 1000000) s d -
            plusLowerT11ReserveDStepSlope
              (185634 / 1000000) (15634 / 1000000) s d =
          (S - 185634 / 1000000) *
            (-6973 / 4000000000 +
              (15634 / 1000000 : ℝ) * cs +
              (S + 185634 / 1000000) * cd) := by
      unfold plusLowerT11ReserveDStepSlope
      dsimp only [cs, cd]
      ring
    have hprod :
        0 < (S - 185634 / 1000000) *
          (-6973 / 4000000000 +
            (15634 / 1000000 : ℝ) * cs +
            (S + 185634 / 1000000) * cd) :=
      mul_pos (sub_pos.mpr hS.1) hqS
    nlinarith
  have hbase :
      0 < plusLowerT11ReserveDStepSlope
        (185634 / 1000000) (15634 / 1000000) s d := by
    let qd : ℝ :=
      -188254299 / 40000000000 +
        (1 / 16 : ℝ) * (185634 / 1000000) ^ 2
    let qs : ℝ :=
      65341 / 20000000000 +
        (1 / 8 : ℝ) * (185634 / 1000000) * (15634 / 1000000)
    have hqd : qd < 0 := by
      norm_num [qd]
    have hqs : 0 < qs := by
      norm_num [qs]
    have hdTerm : qd * (1692 / 100000 : ℝ) < qd * d :=
      mul_lt_mul_of_neg_left hd.2 hqd
    have hsTerm : qs * (56168 / 100000 : ℝ) < qs * s :=
      mul_lt_mul_of_pos_left hs.1 hqs
    have heq :
        plusLowerT11ReserveDStepSlope
            (185634 / 1000000) (15634 / 1000000) s d =
          78359447987 / 4000000000000000 -
            20089947 / 4000000000 * (15634 / 1000000) -
            6973 / 4000000000 * (185634 / 1000000) -
            1207 / 40000 * (185634 / 1000000) * (15634 / 1000000) -
            433 / 1600000 * (185634 / 1000000) ^ 2 + qd * d + qs * s := by
      unfold plusLowerT11ReserveDStepSlope
      dsimp only [qd, qs]
      ring
    rw [heq]
    norm_num at hdTerm hsTerm ⊢
    linarith
  exact hbase.trans (hSmono.trans hDmono)

private theorem plusLowerT11ReserveSStepSlope_neg
    (S D s : ℝ)
    (hS : (185634 / 1000000 : ℝ) < S ∧ S < 193081 / 1000000)
    (hD : (15634 / 1000000 : ℝ) < D ∧ D < 19581 / 1000000)
    (hs : (56168 / 100000 : ℝ) < s ∧ s < 56173 / 100000) :
    plusLowerT11ReserveSStepSlope S D s < 0 := by
  have hDbase : (0 : ℝ) < 15634 / 1000000 := by norm_num
  have hD0 : 0 < D := hDbase.trans hD.1
  have hSbase : (0 : ℝ) < 185634 / 1000000 := by norm_num
  have hS0 : 0 < S := hSbase.trans hS.1
  have hDsq : D ^ 2 < (19581 / 1000000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hD.2 hD0.le (by norm_num)
  have hsCoeff :
      -388607 / 8000000000 + (1 / 16 : ℝ) * D ^ 2 < 0 := by
    norm_num at hDsq ⊢
    nlinarith
  have hsStep :
      plusLowerT11ReserveSStepSlope S D s ≤
        plusLowerT11ReserveSStepSlope S D (56168 / 100000) := by
    have heq :
        plusLowerT11ReserveSStepSlope S D s -
            plusLowerT11ReserveSStepSlope S D (56168 / 100000) =
          (s - 56168 / 100000) *
            (-388607 / 8000000000 + (1 / 16 : ℝ) * D ^ 2) := by
      unfold plusLowerT11ReserveSStepSlope
      ring
    have hprod :
        (s - 56168 / 100000) *
            (-388607 / 8000000000 + (1 / 16 : ℝ) * D ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs.1.le) hsCoeff.le
    nlinarith
  have hDStep :
      plusLowerT11ReserveSStepSlope S D (56168 / 100000) ≤
        plusLowerT11ReserveSStepSlope
          S (19581 / 1000000) (56168 / 100000) := by
    let q : ℝ :=
      6973 / 4000000000 +
        7893 / 1600000 * ((19581 / 1000000 : ℝ) + D) +
        627 / 800000 * S +
        (1 / 16 : ℝ) * ((19581 / 1000000 : ℝ) + D) *
          (56168 / 100000)
    have hq : 0 < q := by
      dsimp only [q]
      have hsumD : 0 < (19581 / 1000000 : ℝ) + D := by positivity
      positivity
    have heq :
        plusLowerT11ReserveSStepSlope
              S (19581 / 1000000) (56168 / 100000) -
            plusLowerT11ReserveSStepSlope S D (56168 / 100000) =
          ((19581 / 1000000 : ℝ) - D) * q := by
      unfold plusLowerT11ReserveSStepSlope
      dsimp only [q]
      ring
    have hprod : 0 ≤ ((19581 / 1000000 : ℝ) - D) * q :=
      mul_nonneg (sub_nonneg.mpr hD.2.le) hq.le
    nlinarith
  have hSStep :
      plusLowerT11ReserveSStepSlope
          S (19581 / 1000000) (56168 / 100000) ≤
        plusLowerT11ReserveSStepSlope
          (193081 / 1000000) (19581 / 1000000) (56168 / 100000) := by
    let q : ℝ :=
      41471 / 800000000 + 627 / 800000 * (19581 / 1000000 : ℝ)
    have hq : 0 < q := by norm_num [q]
    have heq :
        plusLowerT11ReserveSStepSlope
              (193081 / 1000000) (19581 / 1000000) (56168 / 100000) -
            plusLowerT11ReserveSStepSlope
              S (19581 / 1000000) (56168 / 100000) =
          ((193081 / 1000000 : ℝ) - S) * q := by
      unfold plusLowerT11ReserveSStepSlope
      dsimp only [q]
      ring
    have hprod : 0 ≤ ((193081 / 1000000 : ℝ) - S) * q :=
      mul_nonneg (sub_nonneg.mpr hS.2.le) hq.le
    nlinarith
  have hcorner :
      plusLowerT11ReserveSStepSlope
        (193081 / 1000000) (19581 / 1000000) (56168 / 100000) < 0 := by
    norm_num [plusLowerT11ReserveSStepSlope]
  exact lt_of_le_of_lt (hsStep.trans (hDStep.trans hSStep)) hcorner

private theorem plusLowerT11ReserveCapitalDStepSlope_neg
    (S D : ℝ)
    (hS : S < (193081 / 1000000 : ℝ))
    (hD : (15634 / 1000000 : ℝ) < D) :
    plusLowerT11ReserveCapitalDStepSlope S D < 0 := by
  unfold plusLowerT11ReserveCapitalDStepSlope
  have hDterm :
      -(2429138831 / 160000000000 : ℝ) * D <
        -(2429138831 / 160000000000 : ℝ) * (15634 / 1000000) :=
    mul_lt_mul_of_neg_left hD (by norm_num)
  have hSterm :
      (18885411 / 80000000000 : ℝ) * S <
        (18885411 / 80000000000 : ℝ) * (193081 / 1000000) :=
    mul_lt_mul_of_pos_left hS (by norm_num)
  norm_num at hDterm hSterm ⊢
  linarith

private theorem plusLowerT11ReserveCapitalSStepSlope_neg
    (S : ℝ) (hS : (185634 / 1000000 : ℝ) < S) :
    plusLowerT11ReserveCapitalSStepSlope S < 0 := by
  unfold plusLowerT11ReserveCapitalSStepSlope
  have hterm :
      -(35269671 / 160000000000 : ℝ) * S <
        -(35269671 / 160000000000 : ℝ) * (185634 / 1000000) :=
    mul_lt_mul_of_neg_left hS (by norm_num)
  norm_num at hterm ⊢
  linarith

private theorem plusLowerDet_pos
    (S D : ℝ)
    (hS : (185634 / 1000000 : ℝ) < S ∧ S < 193081 / 1000000)
    (hD : (15634 / 1000000 : ℝ) < D ∧ D < 19581 / 1000000) :
    0 < symmetricDeterminant
      plusLower00 plusLower02 ((S - D) / 2)
      plusLower22 ((S + D) / 2) plusP4Lower := by
  have hSbase : (0 : ℝ) < 185634 / 1000000 := by norm_num
  have hDbase : (0 : ℝ) < 15634 / 1000000 := by norm_num
  have hS0 : 0 < S := hSbase.trans hS.1
  have hD0 : 0 < D := hDbase.trans hD.1
  have hSsq : S ^ 2 < (193081 / 1000000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hS.2 hS0.le (by norm_num)
  have hDsq : D ^ 2 < (19581 / 1000000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hD.2 hD0.le (by norm_num)
  have hSD :
      S * D < (193081 / 1000000 : ℝ) * (19581 / 1000000) := by
    calc
      S * D < (193081 / 1000000 : ℝ) * D :=
        mul_lt_mul_of_pos_right hS.2 hD0
      _ < (193081 / 1000000 : ℝ) * (19581 / 1000000) :=
        mul_lt_mul_of_pos_left hD.2 (by norm_num)
  unfold symmetricDeterminant plusLower00 plusLower02 plusLower22 plusP4Lower
  nlinarith

private theorem plusLowerT11Reserve_pos
    (S D s d a o : ℝ)
    (hS : (185634 / 1000000 : ℝ) < S ∧ S < 193081 / 1000000)
    (hD : (15634 / 1000000 : ℝ) < D ∧ D < 19581 / 1000000)
    (hs : (56168 / 100000 : ℝ) < s ∧ s < 56173 / 100000)
    (hd : (1687 / 100000 : ℝ) < d ∧ d < 1692 / 100000)
    (ha : (141 / 1000 : ℝ) < a ∧ a < 144 / 1000)
    (ho : (1578 / 10000 : ℝ) < o) :
    0 < plusLowerT11Reserve S D s d a o := by
  have hdet := plusLowerDet_pos S D hS hD
  have hoStep :
      plusLowerT11Reserve S D s d a (1578 / 10000) <
        plusLowerT11Reserve S D s d a o := by
    have heq :
        plusLowerT11Reserve S D s d a o -
            plusLowerT11Reserve S D s d a (1578 / 10000) =
          (o - 1578 / 10000) *
            symmetricDeterminant
              plusLower00 plusLower02 ((S - D) / 2)
              plusLower22 ((S + D) / 2) plusP4Lower := by
      unfold plusLowerT11Reserve
      ring
    have hprod :
        0 < (o - 1578 / 10000) *
          symmetricDeterminant
            plusLower00 plusLower02 ((S - D) / 2)
            plusLower22 ((S + D) / 2) plusP4Lower :=
      mul_pos (sub_pos.mpr ho) hdet
    nlinarith
  have haSlope := plusLowerT11ReserveASlope_pos S D s d a hS hD hs hd ha.2
  have haStep :
      plusLowerT11Reserve S D s d (141 / 1000) (1578 / 10000) <
        plusLowerT11Reserve S D s d a (1578 / 10000) := by
    have heq := plusLowerT11Reserve_a_difference S D s d a
    have hprod : 0 < (a - 141 / 1000) *
        plusLowerT11ReserveASlope S D s d a :=
      mul_pos (sub_pos.mpr ha.1) haSlope
    nlinarith
  have hdSlope := plusLowerT11ReserveDStepSlope_pos S D s d hS hD hs hd
  have hdStep :
      plusLowerT11Reserve S D s (1687 / 100000)
          (141 / 1000) (1578 / 10000) <
        plusLowerT11Reserve S D s d (141 / 1000) (1578 / 10000) := by
    have heq := plusLowerT11Reserve_d_difference S D s d
    have hprod : 0 < (d - 1687 / 100000) *
        plusLowerT11ReserveDStepSlope S D s d :=
      mul_pos (sub_pos.mpr hd.1) hdSlope
    nlinarith
  have hsSlope := plusLowerT11ReserveSStepSlope_neg S D s hS hD hs
  have hsStep :
      plusLowerT11Reserve S D (56173 / 100000) (1687 / 100000)
          (141 / 1000) (1578 / 10000) <
        plusLowerT11Reserve S D s (1687 / 100000)
          (141 / 1000) (1578 / 10000) := by
    have heq := plusLowerT11Reserve_s_difference S D s
    have hprod : 0 < (s - 56173 / 100000) *
        plusLowerT11ReserveSStepSlope S D s :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hs.2) hsSlope
    nlinarith
  have hCapitalDSlope :=
    plusLowerT11ReserveCapitalDStepSlope_neg S D hS.2 hD.1
  have hCapitalDStep :
      plusLowerT11Reserve S (19581 / 1000000)
          (56173 / 100000) (1687 / 100000)
          (141 / 1000) (1578 / 10000) <
        plusLowerT11Reserve S D
          (56173 / 100000) (1687 / 100000)
          (141 / 1000) (1578 / 10000) := by
    have heq := plusLowerT11Reserve_capitalD_difference S D
    have hprod : 0 < (D - 19581 / 1000000) *
        plusLowerT11ReserveCapitalDStepSlope S D :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hD.2) hCapitalDSlope
    nlinarith
  have hCapitalSSlope :=
    plusLowerT11ReserveCapitalSStepSlope_neg S hS.1
  have hCapitalSStep :
      plusLowerT11Reserve (193081 / 1000000) (19581 / 1000000)
          (56173 / 100000) (1687 / 100000)
          (141 / 1000) (1578 / 10000) <
        plusLowerT11Reserve S (19581 / 1000000)
          (56173 / 100000) (1687 / 100000)
          (141 / 1000) (1578 / 10000) := by
    have heq := plusLowerT11Reserve_capitalS_difference S
    have hprod : 0 < (S - 193081 / 1000000) *
        plusLowerT11ReserveCapitalSStepSlope S :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hS.2) hCapitalSSlope
    nlinarith
  exact plusLowerT11Reserve_corner_pos.trans
    (hCapitalSStep.trans
      (hCapitalDStep.trans
        (hsStep.trans (hdStep.trans (haStep.trans hoStep)))))

private theorem plusLowerT11_pos :
    0 <
      symmetricDeterminant
          plusLower00 plusLower02 factorTwoIntrinsicSixUnbalancedEPlus04
          plusLower22 factorTwoIntrinsicSixUnbalancedEPlus24 plusP4Lower *
        factorTwoIntrinsicSixUnbalancedOMinus11 -
      adjugateQuadratic
        plusLower00 plusLower02 factorTwoIntrinsicSixUnbalancedEPlus04
        plusLower22 factorTwoIntrinsicSixUnbalancedEPlus24 plusP4Lower
        factorTwoIntrinsicSixUnbalancedKPlus01
        factorTwoIntrinsicSixUnbalancedKPlus21
        factorTwoIntrinsicSixUnbalancedKPlus41 := by
  let S : ℝ := factorTwoIntrinsicSixUnbalancedEPlus04 +
    factorTwoIntrinsicSixUnbalancedEPlus24
  let D : ℝ := factorTwoIntrinsicSixUnbalancedEPlus24 -
    factorTwoIntrinsicSixUnbalancedEPlus04
  let s : ℝ := factorTwoIntrinsicAlternating01 +
    factorTwoIntrinsicAlternating21
  let d : ℝ := factorTwoIntrinsicAlternating01 -
    factorTwoIntrinsicAlternating21
  let a : ℝ := factorTwoIntrinsicFourP45Cross41
  let o : ℝ := factorTwoIntrinsicSixUnbalancedOMinus11
  rcases factorTwoIntrinsicP4_positive_aligned_bounds with
    ⟨_hAL, _hAU, _hXL, _hXU, hSL, hSU, _hWL, _hWU, hDL, hDU⟩
  rcases factorTwoIntrinsicAlternatingSharpBounds with
    ⟨hsL, hsU, hdL, hdU, _hs3L, _hs3U, _hd3L, _hd3U⟩
  rcases factorTwoIntrinsicFourP45Cross41_bounds with ⟨haL, haU⟩
  have hoL := factorTwoIntrinsicOddPhaseLow_minus_entry_bounds.1
  have hreserve : 0 < plusLowerT11Reserve S D s d a o :=
    plusLowerT11Reserve_pos S D s d a o
      (by simpa only [S, factorTwoIntrinsicSixUnbalancedEPlus04,
          factorTwoIntrinsicSixUnbalancedEPlus24] using ⟨hSL, hSU⟩)
      (by simpa only [D, factorTwoIntrinsicSixUnbalancedEPlus04,
          factorTwoIntrinsicSixUnbalancedEPlus24] using ⟨hDL, hDU⟩)
      (by simpa only [s] using ⟨hsL, hsU⟩)
      (by simpa only [d] using ⟨hdL, hdU⟩)
      (by simpa only [a] using ⟨haL, haU⟩)
      (by simpa only [o, factorTwoIntrinsicSixUnbalancedOMinus11] using hoL)
  have heq :
      plusLowerT11Reserve S D s d a o =
        symmetricDeterminant
            plusLower00 plusLower02 factorTwoIntrinsicSixUnbalancedEPlus04
            plusLower22 factorTwoIntrinsicSixUnbalancedEPlus24 plusP4Lower *
          factorTwoIntrinsicSixUnbalancedOMinus11 -
        adjugateQuadratic
          plusLower00 plusLower02 factorTwoIntrinsicSixUnbalancedEPlus04
          plusLower22 factorTwoIntrinsicSixUnbalancedEPlus24 plusP4Lower
          factorTwoIntrinsicSixUnbalancedKPlus01
          factorTwoIntrinsicSixUnbalancedKPlus21
          factorTwoIntrinsicSixUnbalancedKPlus41 := by
    unfold plusLowerT11Reserve
    dsimp only [S, D, s, d, a, o]
    unfold factorTwoIntrinsicSixUnbalancedKPlus01
      factorTwoIntrinsicSixUnbalancedKPlus21
      factorTwoIntrinsicSixUnbalancedKPlus41
    ring
  rwa [heq] at hreserve

/-! ## Inverse-free transfer to the exact first Schur pivot -/

private def threeBilinear
    (e00 e02 e04 e22 e24 e44 x0 x2 x4 y0 y2 y4 : ℝ) : ℝ :=
  x0 * (e00 * y0 + e02 * y2 + e04 * y4) +
    x2 * (e02 * y0 + e22 * y2 + e24 * y4) +
    x4 * (e04 * y0 + e24 * y2 + e44 * y4)

private theorem symmetricQuadratic_eq_threeBilinear_self
    (e00 e02 e04 e22 e24 e44 x0 x2 x4 : ℝ) :
    symmetricQuadratic e00 e02 e04 e22 e24 e44 x0 x2 x4 =
      threeBilinear e00 e02 e04 e22 e24 e44 x0 x2 x4 x0 x2 x4 := by
  unfold symmetricQuadratic threeBilinear
  ring_nf

private theorem symmetricQuadratic_add_threeVector
    (e00 e02 e04 e22 e24 e44 x0 x2 x4 y0 y2 y4 : ℝ) :
    symmetricQuadratic e00 e02 e04 e22 e24 e44
        (x0 + y0) (x2 + y2) (x4 + y4) =
      symmetricQuadratic e00 e02 e04 e22 e24 e44 x0 x2 x4 +
        2 * threeBilinear e00 e02 e04 e22 e24 e44
          x0 x2 x4 y0 y2 y4 +
        symmetricQuadratic e00 e02 e04 e22 e24 e44 y0 y2 y4 := by
  unfold symmetricQuadratic threeBilinear
  ring_nf

private theorem symmetricQuadratic_scale_threeVector
    (e00 e02 e04 e22 e24 e44 d x0 x2 x4 : ℝ) :
    symmetricQuadratic e00 e02 e04 e22 e24 e44
        (d * x0) (d * x2) (d * x4) =
      d ^ 2 * symmetricQuadratic e00 e02 e04 e22 e24 e44 x0 x2 x4 := by
  unfold symmetricQuadratic
  ring_nf

private theorem threeBilinear_scale_left
    (e00 e02 e04 e22 e24 e44 d x0 x2 x4 y0 y2 y4 : ℝ) :
    threeBilinear e00 e02 e04 e22 e24 e44
        (d * x0) (d * x2) (d * x4) y0 y2 y4 =
      d * threeBilinear e00 e02 e04 e22 e24 e44
        x0 x2 x4 y0 y2 y4 := by
  unfold threeBilinear
  ring_nf

private theorem threeBilinear_adjugateVector
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 x0 x2 x4 : ℝ) :
    threeBilinear e00 e02 e04 e22 e24 e44 x0 x2 x4
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2) =
      symmetricDeterminant e00 e02 e04 e22 e24 e44 *
        (x0 * ell0 + x2 * ell2 + x4 * ell4) := by
  simp only [adjugateVector]
  unfold threeBilinear symmetricDeterminant
  ring_nf

private theorem symmetricQuadratic_adjugateVector_local
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 : ℝ) :
    symmetricQuadratic e00 e02 e04 e22 e24 e44
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2) =
      symmetricDeterminant e00 e02 e04 e22 e24 e44 *
        adjugateQuadratic e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 := by
  rw [symmetricQuadratic_eq_threeBilinear_self]
  rw [threeBilinear_adjugateVector]
  simp only [adjugateVector]
  unfold adjugateQuadratic
  ring_nf

private theorem fractionFree_three_by_three_completion_local
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 c0 c2 c4 r : ℝ) :
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
  rw [symmetricQuadratic_add_threeVector]
  rw [symmetricQuadratic_scale_threeVector]
  rw [threeBilinear_scale_left]
  rw [threeBilinear_adjugateVector]
  rw [symmetricQuadratic_adjugateVector_local]
  ring_nf

private theorem threePlusOne_scaled_completion
    (e00 e02 e04 e22 e24 e44 k0 k2 k4 o
      c0 c2 c4 c1 : ℝ) :
    let det := symmetricDeterminant e00 e02 e04 e22 e24 e44
    let v := adjugateVector e00 e02 e04 e22 e24 e44 k0 k2 k4
    det ^ 2 *
        (symmetricQuadratic e00 e02 e04 e22 e24 e44 c0 c2 c4 +
          2 * (c0 * k0 + c2 * k2 + c4 * k4) * c1 + o * c1 ^ 2) =
      symmetricQuadratic e00 e02 e04 e22 e24 e44
        (det * c0 + v 0 * c1)
        (det * c2 + v 1 * c1)
        (det * c4 + v 2 * c1) +
      det *
        (det * o - adjugateQuadratic e00 e02 e04 e22 e24 e44 k0 k2 k4) *
        c1 ^ 2 := by
  have h := fractionFree_three_by_three_completion_local
    e00 e02 e04 e22 e24 e44
    (k0 * c1) (k2 * c1) (k4 * c1) c0 c2 c4 (o * c1 ^ 2)
  have hv0 :
      adjugateVector e00 e02 e04 e22 e24 e44
          (k0 * c1) (k2 * c1) (k4 * c1) 0 =
        adjugateVector e00 e02 e04 e22 e24 e44 k0 k2 k4 0 * c1 := by
    simp only [adjugateVector]
    ring_nf
  have hv2 :
      adjugateVector e00 e02 e04 e22 e24 e44
          (k0 * c1) (k2 * c1) (k4 * c1) 1 =
        adjugateVector e00 e02 e04 e22 e24 e44 k0 k2 k4 1 * c1 := by
    simp only [adjugateVector]
    ring_nf
  have hv4 :
      adjugateVector e00 e02 e04 e22 e24 e44
          (k0 * c1) (k2 * c1) (k4 * c1) 2 =
        adjugateVector e00 e02 e04 e22 e24 e44 k0 k2 k4 2 * c1 := by
    simp only [adjugateVector]
    ring_nf
  have hadj :
      adjugateQuadratic e00 e02 e04 e22 e24 e44
          (k0 * c1) (k2 * c1) (k4 * c1) =
        adjugateQuadratic e00 e02 e04 e22 e24 e44 k0 k2 k4 * c1 ^ 2 := by
    unfold adjugateQuadratic
    ring_nf
  dsimp only at h ⊢
  rw [hv0, hv2, hv4, hadj] at h
  ring_nf at h ⊢
  exact h

private theorem threePlusOne_quadratic_pos
    (e00 e02 e04 e22 e24 e44 k0 k2 k4 o : ℝ)
    (he00 : 0 < e00)
    (heMinor : 0 < leadingMinorTwo e00 e02 e22)
    (heDet : 0 < symmetricDeterminant e00 e02 e04 e22 e24 e44)
    (hT : 0 < symmetricDeterminant e00 e02 e04 e22 e24 e44 * o -
      adjugateQuadratic e00 e02 e04 e22 e24 e44 k0 k2 k4)
    (c0 c2 c4 c1 : ℝ)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨ c1 ≠ 0) :
    0 < symmetricQuadratic e00 e02 e04 e22 e24 e44 c0 c2 c4 +
      2 * (c0 * k0 + c2 * k2 + c4 * k4) * c1 + o * c1 ^ 2 := by
  let det := symmetricDeterminant e00 e02 e04 e22 e24 e44
  let v := adjugateVector e00 e02 e04 e22 e24 e44 k0 k2 k4
  have hidentity := threePlusOne_scaled_completion
    e00 e02 e04 e22 e24 e44 k0 k2 k4 o c0 c2 c4 c1
  dsimp only [det, v] at hidentity
  have hright :
      0 < symmetricQuadratic e00 e02 e04 e22 e24 e44
          (det * c0 + v 0 * c1)
          (det * c2 + v 1 * c1)
          (det * c4 + v 2 * c1) +
        det *
          (det * o - adjugateQuadratic e00 e02 e04 e22 e24 e44 k0 k2 k4) *
          c1 ^ 2 := by
    by_cases hc1 : c1 = 0
    · subst c1
      have hevenNe : det * c0 ≠ 0 ∨ det * c2 ≠ 0 ∨ det * c4 ≠ 0 := by
        rcases hne with h0 | h2 | h4 | h1
        · exact Or.inl (mul_ne_zero heDet.ne' h0)
        · exact Or.inr (Or.inl (mul_ne_zero heDet.ne' h2))
        · exact Or.inr (Or.inr (mul_ne_zero heDet.ne' h4))
        · exact (h1 rfl).elim
      have heven := symmetricQuadratic_pos e00 e02 e04 e22 e24 e44
        he00 heMinor heDet (det * c0) (det * c2) (det * c4) hevenNe
      simpa using heven
    · have heven :
          0 ≤ symmetricQuadratic e00 e02 e04 e22 e24 e44
            (det * c0 + v 0 * c1)
            (det * c2 + v 1 * c1)
            (det * c4 + v 2 * c1) :=
        symmetricQuadratic_nonneg e00 e02 e04 e22 e24 e44
          he00 heMinor heDet _ _ _
      have htail :
          0 < det *
              (det * o -
                adjugateQuadratic e00 e02 e04 e22 e24 e44 k0 k2 k4) *
            c1 ^ 2 :=
        mul_pos (mul_pos heDet hT) (sq_pos_of_ne_zero hc1)
      exact add_pos_of_nonneg_of_pos heven htail
  have hscaled :
      0 < det ^ 2 *
        (symmetricQuadratic e00 e02 e04 e22 e24 e44 c0 c2 c4 +
          2 * (c0 * k0 + c2 * k2 + c4 * k4) * c1 + o * c1 ^ 2) := by
    rw [hidentity]
    exact hright
  exact ((mul_pos_iff.mp hscaled).resolve_right (fun hneg ↦
    (not_lt_of_ge (sq_nonneg det)) hneg.1)).2

private theorem plusLowerFourQuadratic_pos
    (c0 c2 c4 c1 : ℝ)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨ c1 ≠ 0) :
    0 < symmetricQuadratic
        plusLower00 plusLower02 factorTwoIntrinsicSixUnbalancedEPlus04
        plusLower22 factorTwoIntrinsicSixUnbalancedEPlus24 plusP4Lower
        c0 c2 c4 +
      2 * (c0 * factorTwoIntrinsicSixUnbalancedKPlus01 +
        c2 * factorTwoIntrinsicSixUnbalancedKPlus21 +
        c4 * factorTwoIntrinsicSixUnbalancedKPlus41) * c1 +
      factorTwoIntrinsicSixUnbalancedOMinus11 * c1 ^ 2 := by
  let S : ℝ := factorTwoIntrinsicSixUnbalancedEPlus04 +
    factorTwoIntrinsicSixUnbalancedEPlus24
  let D : ℝ := factorTwoIntrinsicSixUnbalancedEPlus24 -
    factorTwoIntrinsicSixUnbalancedEPlus04
  rcases factorTwoIntrinsicP4_positive_aligned_bounds with
    ⟨_hAL, _hAU, _hXL, _hXU, hSL, hSU, _hWL, _hWU, hDL, hDU⟩
  have hdet := plusLowerDet_pos S D
    (by simpa only [S, factorTwoIntrinsicSixUnbalancedEPlus04,
        factorTwoIntrinsicSixUnbalancedEPlus24] using ⟨hSL, hSU⟩)
    (by simpa only [D, factorTwoIntrinsicSixUnbalancedEPlus04,
        factorTwoIntrinsicSixUnbalancedEPlus24] using ⟨hDL, hDU⟩)
  have hdet' :
      0 < symmetricDeterminant
        plusLower00 plusLower02 factorTwoIntrinsicSixUnbalancedEPlus04
        plusLower22 factorTwoIntrinsicSixUnbalancedEPlus24 plusP4Lower := by
    have h04 : factorTwoIntrinsicSixUnbalancedEPlus04 = (S - D) / 2 := by
      dsimp only [S, D]
      ring_nf
    have h24 : factorTwoIntrinsicSixUnbalancedEPlus24 = (S + D) / 2 := by
      dsimp only [S, D]
      ring_nf
    rwa [h04, h24]
  apply threePlusOne_quadratic_pos
    plusLower00 plusLower02 factorTwoIntrinsicSixUnbalancedEPlus04
    plusLower22 factorTwoIntrinsicSixUnbalancedEPlus24 plusP4Lower
    factorTwoIntrinsicSixUnbalancedKPlus01
    factorTwoIntrinsicSixUnbalancedKPlus21
    factorTwoIntrinsicSixUnbalancedKPlus41
    factorTwoIntrinsicSixUnbalancedOMinus11
  · norm_num [plusLower00]
  · norm_num [leadingMinorTwo, plusLower00, plusLower02, plusLower22]
  · exact hdet'
  · exact plusLowerT11_pos
  · exact hne

private def plusExactFirstQuadratic
    (c0 c2 c4 c1 : ℝ) : ℝ :=
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
    factorTwoIntrinsicSixUnbalancedOMinus11 * c1 ^ 2

private theorem plusExactFirstQuadratic_pos
    (c0 c2 c4 c1 : ℝ)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨ c1 ≠ 0) :
    0 < plusExactFirstQuadratic c0 c2 c4 c1 := by
  have hlower := plusLowerFourQuadratic_pos c0 c2 c4 c1 hne
  have hrem := plusEvenRemainder_quadratic_nonneg c0 c2 c4
  have heq :
      plusExactFirstQuadratic c0 c2 c4 c1 =
        (symmetricQuadratic
            plusLower00 plusLower02 factorTwoIntrinsicSixUnbalancedEPlus04
            plusLower22 factorTwoIntrinsicSixUnbalancedEPlus24 plusP4Lower
            c0 c2 c4 +
          2 * (c0 * factorTwoIntrinsicSixUnbalancedKPlus01 +
            c2 * factorTwoIntrinsicSixUnbalancedKPlus21 +
            c4 * factorTwoIntrinsicSixUnbalancedKPlus41) * c1 +
          factorTwoIntrinsicSixUnbalancedOMinus11 * c1 ^ 2) +
        ((factorTwoIntrinsicSixUnbalancedEPlus00 - plusLower00) * c0 ^ 2 +
          2 * (factorTwoIntrinsicSixUnbalancedEPlus02 - plusLower02) * c0 * c2 +
          (factorTwoIntrinsicSixUnbalancedEPlus22 - plusLower22) * c2 ^ 2 +
          (factorTwoIntrinsicSixUnbalancedEPlus44 - plusP4Lower) * c4 ^ 2) := by
    unfold plusExactFirstQuadratic symmetricQuadratic
    ring_nf
  rw [heq]
  exact add_pos_of_pos_of_nonneg hlower hrem

set_option maxHeartbeats 800000 in
private theorem factorTwoIntrinsicSixUnbalancedTPlus11_eq_fractionFree :
    factorTwoIntrinsicSixUnbalancedTPlus11 =
      factorTwoIntrinsicSixUnbalancedEPlusDet *
          factorTwoIntrinsicSixUnbalancedOMinus11 -
        adjugateQuadratic
          factorTwoIntrinsicSixUnbalancedEPlus00
          factorTwoIntrinsicSixUnbalancedEPlus02
          factorTwoIntrinsicSixUnbalancedEPlus04
          factorTwoIntrinsicSixUnbalancedEPlus22
          factorTwoIntrinsicSixUnbalancedEPlus24
          factorTwoIntrinsicSixUnbalancedEPlus44
          factorTwoIntrinsicSixUnbalancedKPlus01
          factorTwoIntrinsicSixUnbalancedKPlus21
          factorTwoIntrinsicSixUnbalancedKPlus41 := by
  have h := factorTwoIntrinsicSixUnbalancedTPlusQuadratic_eq_fractionFree 1 0 0
  simpa only [factorTwoIntrinsicSixUnbalancedTPlusQuadratic,
    symmetricQuadratic, mul_one, mul_zero, add_zero, zero_mul, pow_two,
    one_mul, one_pow, zero_pow (by norm_num : 2 ≠ 0)] using h

/-- The first Sylvester gate of the corrected positive fraction-free Schur
block.  The proof is a rational lower-Gram completion, not an evaluation of
the transcendental matrix. -/
theorem factorTwoIntrinsicSixUnbalancedTPlus11_pos :
    0 < factorTwoIntrinsicSixUnbalancedTPlus11 := by
  let det : ℝ := factorTwoIntrinsicSixUnbalancedEPlusDet
  let v := adjugateVector
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    factorTwoIntrinsicSixUnbalancedKPlus01
    factorTwoIntrinsicSixUnbalancedKPlus21
    factorTwoIntrinsicSixUnbalancedKPlus41
  have hdet : 0 < det := by
    simpa only [det] using factorTwoIntrinsicSixUnbalancedEPlus_positive.2.2
  have hform : 0 < plusExactFirstQuadratic (-v 0) (-v 1) (-v 2) det :=
    plusExactFirstQuadratic_pos (-v 0) (-v 1) (-v 2) det
      (Or.inr (Or.inr (Or.inr hdet.ne')))
  have hcompletion := threePlusOne_scaled_completion
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    factorTwoIntrinsicSixUnbalancedKPlus01
    factorTwoIntrinsicSixUnbalancedKPlus21
    factorTwoIntrinsicSixUnbalancedKPlus41
    factorTwoIntrinsicSixUnbalancedOMinus11
    (-v 0) (-v 1) (-v 2) det
  have hidentity :
      det ^ 2 * plusExactFirstQuadratic (-v 0) (-v 1) (-v 2) det =
        det * factorTwoIntrinsicSixUnbalancedTPlus11 * det ^ 2 := by
    calc
      _ = symmetricQuadratic
            factorTwoIntrinsicSixUnbalancedEPlus00
            factorTwoIntrinsicSixUnbalancedEPlus02
            factorTwoIntrinsicSixUnbalancedEPlus04
            factorTwoIntrinsicSixUnbalancedEPlus22
            factorTwoIntrinsicSixUnbalancedEPlus24
            factorTwoIntrinsicSixUnbalancedEPlus44
            (det * (-v 0) + v 0 * det)
            (det * (-v 1) + v 1 * det)
            (det * (-v 2) + v 2 * det) +
          det *
            (det * factorTwoIntrinsicSixUnbalancedOMinus11 -
              adjugateQuadratic
                factorTwoIntrinsicSixUnbalancedEPlus00
                factorTwoIntrinsicSixUnbalancedEPlus02
                factorTwoIntrinsicSixUnbalancedEPlus04
                factorTwoIntrinsicSixUnbalancedEPlus22
                factorTwoIntrinsicSixUnbalancedEPlus24
                factorTwoIntrinsicSixUnbalancedEPlus44
                factorTwoIntrinsicSixUnbalancedKPlus01
                factorTwoIntrinsicSixUnbalancedKPlus21
                factorTwoIntrinsicSixUnbalancedKPlus41) * det ^ 2 := by
        simpa only [det, v, plusExactFirstQuadratic] using hcompletion
      _ = det * factorTwoIntrinsicSixUnbalancedTPlus11 * det ^ 2 := by
        rw [factorTwoIntrinsicSixUnbalancedTPlus11_eq_fractionFree]
        dsimp only [det]
        unfold symmetricQuadratic
        ring_nf
  have hscaled :
      0 < det * factorTwoIntrinsicSixUnbalancedTPlus11 * det ^ 2 := by
    rw [← hidentity]
    exact mul_pos (sq_pos_of_pos hdet) hform
  have hdetSq : 0 < det ^ 2 := sq_pos_of_pos hdet
  have hscaled' :
      0 < factorTwoIntrinsicSixUnbalancedTPlus11 * (det * det ^ 2) := by
    nlinarith [hscaled]
  have hfactor : 0 < det * det ^ 2 := mul_pos hdet hdetSq
  exact ((mul_pos_iff.mp hscaled').resolve_right (fun hneg ↦
    (not_lt_of_ge hfactor.le) hneg.2)).1

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusPositiveStructural
