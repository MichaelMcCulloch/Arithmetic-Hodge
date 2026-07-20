import ArithmeticHodge.Analysis.YoshidaFourCellOddP11ExactResidualTailCrossAlgebraicStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualEnergyStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualRegularMomentBoundStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedFiniteCertificateAssemblyStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedSchurPivotFloorStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualRegularMomentSmallStructural

noncomputable section

open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFourCellOddP11CoreEntryBoundsStructural
open YoshidaFourCellOddP11ExactResidualTailCrossAlgebraicStructural
open YoshidaFourCellOddP11GalerkinFiniteSolveStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP11GalerkinResidualEnergyStructural
open YoshidaFourCellOddP11GalerkinResidualRegularMomentBoundStructural
open YoshidaFourCellOddP11GalerkinRieszStructural
open YoshidaFourCellOddP11GalerkinSolutionBoxStructural
open YoshidaFourCellOddP13AugmentedFiniteCertificateAssemblyStructural
open YoshidaFourCellOddP13AugmentedRankOneSchurStructural
open YoshidaFourCellOddP13AugmentedSchurPivotFloorStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# Smallness of the exact old-residual--`P11` regular moment

The sixth-order kernel moment is sparse in the odd Legendre basis.  A
uniform remainder estimate then turns that exact cancellation into the
mixed-row bound needed by the rank-one finite Schur certificate.
-/

private theorem abs_fourCellOddFiveModeP11PolynomialMoment_lt_one_tenThousand
    (c d e f g : ℝ) (he : |e| < 1) (hf : |f| < 1) (hg : |g| < 1) :
    |fourCellOddFiveModeP11PolynomialMoment c d e f g| <
      (1 / 10000 : ℝ) := by
  let a := fourCellOperatorHalfWidth
  let A : ℝ := 31 * a ^ 5 / 2698531355520
  let B : ℝ := a ^ 3 / 320932800 + 31 * a ^ 5 / 1022170968000
  let C : ℝ := a / 220248 + a ^ 3 / 133722000 +
    31 * a ^ 5 / 849188188800
  have ha0 : 0 < a := by
    dsimp only [a]
    unfold fourCellOperatorHalfWidth
    positivity
  have ha1 : a < 1 :=
    YoshidaFourCellOddPolarPotentialStructural.fourCellOperatorHalfWidth_lt_one_half.trans
      (by norm_num)
  have ha3 : a ^ 3 ≤ 1 := pow_le_one₀ ha0.le ha1.le
  have ha5 : a ^ 5 ≤ 1 := pow_le_one₀ ha0.le ha1.le
  have hA0 : 0 < A := by
    dsimp only [A]
    positivity
  have hAhi : A < (1 / 1000000 : ℝ) := by
    dsimp only [A]
    nlinarith
  have hB0 : 0 < B := by
    dsimp only [B]
    positivity
  have hBhi : B < (1 / 1000000 : ℝ) := by
    dsimp only [B]
    nlinarith
  have hC0 : 0 < C := by
    dsimp only [C]
    positivity
  have hChi : C < (1 / 100000 : ℝ) := by
    dsimp only [C]
    nlinarith
  have heA : |-e * A| < (1 / 1000000 : ℝ) := by
    rw [abs_mul, abs_neg, abs_of_pos hA0]
    calc
      |e| * A < 1 * A := mul_lt_mul_of_pos_right he hA0
      _ < 1 * (1 / 1000000 : ℝ) :=
        mul_lt_mul_of_pos_left hAhi (by norm_num)
      _ = (1 / 1000000 : ℝ) := by ring
  have hfB : |f * B| < (1 / 1000000 : ℝ) := by
    rw [abs_mul, abs_of_pos hB0]
    calc
      |f| * B < 1 * B := mul_lt_mul_of_pos_right hf hB0
      _ < 1 * (1 / 1000000 : ℝ) :=
        mul_lt_mul_of_pos_left hBhi (by norm_num)
      _ = (1 / 1000000 : ℝ) := by ring
  have hgC : |g * C| < (1 / 100000 : ℝ) := by
    rw [abs_mul, abs_of_pos hC0]
    calc
      |g| * C < 1 * C := mul_lt_mul_of_pos_right hg hC0
      _ < 1 * (1 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_left hChi (by norm_num)
      _ = (1 / 100000 : ℝ) := by ring
  unfold fourCellOddFiveModeP11PolynomialMoment
  change |-e * A + f * B - g * C| < (1 / 10000 : ℝ)
  calc
    |-e * A + f * B - g * C| ≤
        |-e * A| + |f * B| + |g * C| := by
      calc
        |-e * A + f * B - g * C| ≤
            |-e * A + f * B| + |g * C| := abs_sub _ _
        _ ≤ (|-e * A| + |f * B|) + |g * C| := by
          linarith [abs_add_le (-e * A) (f * B)]
    _ < (1 / 1000000 : ℝ) + 1 / 1000000 + 1 / 100000 := by
      linarith
    _ < (1 / 10000 : ℝ) := by norm_num

/-- Exact polynomial cancellation at the inverse-defined old Galerkin
residual. -/
theorem abs_integral_regularKernelPolynomial6_mul_exactResidual_P11_lt_one_tenThousand :
    |(∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear
          fourCellOddP11GalerkinRetainedResidualProfile
          fourCellOddP11DirectTail t)| < (1 / 10000 : ℝ) := by
  have hEq := integral_regularKernelPolynomial6_mul_fiveModeP11Correlation
    1 (-fourCellOddP11GalerkinRetainedSolution 0)
      (-fourCellOddP11GalerkinRetainedSolution 1)
      (-fourCellOddP11GalerkinRetainedSolution 2)
      (-fourCellOddP11GalerkinRetainedSolution 3)
  rw [show fourCellOddP11GalerkinRetainedResidualProfile =
      fourCellOddOneThreeFiveSevenNineLowProfile
        1 (-fourCellOddP11GalerkinRetainedSolution 0)
          (-fourCellOddP11GalerkinRetainedSolution 1)
          (-fourCellOddP11GalerkinRetainedSolution 2)
          (-fourCellOddP11GalerkinRetainedSolution 3) by
    unfold fourCellOddP11GalerkinRetainedResidualProfile
    exact fourCellOddP11GalerkinResidualProfile_eq_fiveMode _ _ _ _]
  rw [hEq]
  rcases fourCellOddP11GalerkinRetainedSolution_coordinate_bounds with
    ⟨_s0lo, _s0hi, hs1lo, hs1hi, hs2lo, hs2hi, hs3lo, hs3hi⟩
  apply abs_fourCellOddFiveModeP11PolynomialMoment_lt_one_tenThousand
  · simpa only [abs_neg] using
      (abs_lt.2 ⟨by linarith, by linarith⟩ :
        |fourCellOddP11GalerkinRetainedSolution 1| < (1 : ℝ))
  · simpa only [abs_neg] using
      (abs_lt.2 ⟨by linarith, by linarith⟩ :
        |fourCellOddP11GalerkinRetainedSolution 2| < (1 : ℝ))
  · simpa only [abs_neg] using
      (abs_lt.2 ⟨by linarith, by linarith⟩ :
        |fourCellOddP11GalerkinRetainedSolution 3| < (1 : ℝ))

private theorem continuous_exactResidual_P11_correlation :
    Continuous (fun t : ℝ ↦ factorTwoCenteredCorrelationBilinear
      fourCellOddP11GalerkinRetainedResidualProfile
      fourCellOddP11DirectTail t) := by
  rw [show fourCellOddP11GalerkinRetainedResidualProfile =
      fourCellOddOneThreeFiveSevenNineLowProfile
        1 (-fourCellOddP11GalerkinRetainedSolution 0)
          (-fourCellOddP11GalerkinRetainedSolution 1)
          (-fourCellOddP11GalerkinRetainedSolution 2)
          (-fourCellOddP11GalerkinRetainedSolution 3) by
    unfold fourCellOddP11GalerkinRetainedResidualProfile
    exact fourCellOddP11GalerkinResidualProfile_eq_fiveMode _ _ _ _]
  simp_rw [YoshidaFourCellOddP11GalerkinResidualRegularMomentStructural.factorTwoCenteredCorrelationBilinear_fiveMode_P11_eq]
  unfold YoshidaFourCellOddP11GalerkinResidualRegularMomentStructural.fourCellOddFiveModeP11CorrelationPolynomial
  fun_prop

/-- The true regular moment is the sparse polynomial moment plus a uniform
kernel remainder. -/
theorem abs_fourCellOddP11CoreRegularMoment_exactResidual_lt_one_eightThousand :
    |fourCellOddP11CoreRegularMoment
      fourCellOddP11GalerkinRetainedResidualProfile| < (1 / 8000 : ℝ) := by
  let C : ℝ → ℝ := fun t ↦ factorTwoCenteredCorrelationBilinear
    fourCellOddP11GalerkinRetainedResidualProfile fourCellOddP11DirectTail t
  let K : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t)
  let P : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) * C t
  let E : ℝ := fourCellWideRegularEnvelopeError C
  have hC : Continuous C := by
    dsimp only [C]
    exact continuous_exactResidual_P11_correlation
  have hKmeas : Measurable K := by
    dsimp only [K]
    exact measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)
  have hKbound : ∀ t ∈ Icc (0 : ℝ) 2, |K t| ≤ (1 / 4 : ℝ) := by
    intro t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1
    have harg4 : fourCellOperatorHalfWidth * t ≤ 5 * Real.log 2 / 4 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
      calc
        fourCellOperatorHalfWidth * t ≤
            fourCellOperatorHalfWidth * 2 := hmul
        _ = 5 * Real.log 2 / 4 := by
          unfold fourCellOperatorHalfWidth
          ring
    have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg4
    have hk1 := yoshidaRegularKernel_le_quarter harg0
    dsimp only [K]
    rw [abs_of_nonneg hk0]
    exact hk1
  have hfull : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume 0 2 :=
    intervalIntegrable_boundedLag_mul_continuous K C hKmeas hC
      (1 / 4 : ℝ) hKbound
  have hpoly : IntervalIntegrable (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) * C t)
      volume 0 2 := by
    exact (by
      unfold yoshidaRegularKernelPolynomial6
      fun_prop : Continuous (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          C t)).intervalIntegrable 0 2
  have hEeq : E = (∫ t : ℝ in 0..2, K t * C t) - P := by
    dsimp only [E, P]
    unfold fourCellWideRegularEnvelopeError
    rw [← intervalIntegral.integral_sub hfull hpoly]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only [K]
    ring
  have hPabs : |P| < (1 / 10000 : ℝ) := by
    dsimp only [P, C]
    exact
      abs_integral_regularKernelPolynomial6_mul_exactResidual_P11_lt_one_tenThousand
  have hL1 : (∫ t : ℝ in 0..2, |C t|) < 2 := by
    dsimp only [C]
    exact integral_abs_exactResidual_P11_correlation_lt_two
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths C hC
  change |E| ≤ (1 / 80000 : ℝ) * (∫ t : ℝ in 0..2, |C t|)
    at herr
  have hEabs : |E| < (1 / 40000 : ℝ) := by
    calc
      |E| ≤ (1 / 80000 : ℝ) * (∫ t : ℝ in 0..2, |C t|) :=
        herr
      _ < (1 / 80000 : ℝ) * 2 :=
        mul_lt_mul_of_pos_left hL1 (by norm_num)
      _ = (1 / 40000 : ℝ) := by norm_num
  have hdecomp : (∫ t : ℝ in 0..2, K t * C t) = P + E := by
    linarith [hEeq]
  unfold fourCellOddP11CoreRegularMoment
  have htarget : |∫ t : ℝ in 0..2, K t * C t| < (1 / 8000 : ℝ) := by
    rw [hdecomp]
    calc
      |P + E| ≤ |P| + |E| := abs_add_le P E
      _ < (1 / 10000 : ℝ) + 1 / 40000 := add_lt_add hPabs hEabs
      _ = (1 / 8000 : ℝ) := by norm_num
  simpa only [K, C] using htarget

/-- The regular correction in the exact mixed Schur scalar is much smaller
than the available rational margin. -/
theorem abs_two_mul_halfWidth_mul_exactResidualRegularMoment_lt_one_eightThousand :
    |2 * fourCellOperatorHalfWidth *
      fourCellOddP11CoreRegularMoment
        fourCellOddP11GalerkinRetainedResidualProfile| < (1 / 8000 : ℝ) := by
  have ha0 : 0 < 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha1 : 2 * fourCellOperatorHalfWidth < 1 := by
    nlinarith [YoshidaFourCellOddPolarPotentialStructural.fourCellOperatorHalfWidth_lt_one_half]
  rw [abs_mul, abs_of_pos ha0]
  calc
    (2 * fourCellOperatorHalfWidth) *
        |fourCellOddP11CoreRegularMoment
          fourCellOddP11GalerkinRetainedResidualProfile| <
      (2 * fourCellOperatorHalfWidth) * (1 / 8000 : ℝ) :=
        mul_lt_mul_of_pos_left
          abs_fourCellOddP11CoreRegularMoment_exactResidual_lt_one_eightThousand
          ha0
    _ < 1 * (1 / 8000 : ℝ) :=
      mul_lt_mul_of_pos_right ha1 (by norm_num)
    _ = (1 / 8000 : ℝ) := by ring

/-- Completed exact bound on the old-residual--`P11` Schur row. -/
theorem abs_fourCellOddP11ExactResidualTailCross_lt_one_twoHundredFifty :
    |fourCellOddP11ExactResidualTailCross| < (1 / 250 : ℝ) := by
  rw [fourCellOddP11ExactResidualTailCross_eq_algebraicPart_sub_regular]
  have hA := fourCellOddP11ExactResidualTailCrossAlgebraicPart_bounds
  have hAabs : |fourCellOddP11ExactResidualTailCrossAlgebraicPart| <
      (7 / 2000 : ℝ) := by
    rw [abs_of_pos hA.1]
    exact hA.2
  calc
    |fourCellOddP11ExactResidualTailCrossAlgebraicPart -
        2 * fourCellOperatorHalfWidth *
          fourCellOddP11CoreRegularMoment
            fourCellOddP11OldGalerkinResidual| ≤
      |fourCellOddP11ExactResidualTailCrossAlgebraicPart| +
        |2 * fourCellOperatorHalfWidth *
          fourCellOddP11CoreRegularMoment
            fourCellOddP11OldGalerkinResidual| := abs_sub _ _
    _ < (7 / 2000 : ℝ) + 1 / 8000 := by
      unfold fourCellOddP11OldGalerkinResidual
      exact add_lt_add hAabs
        abs_two_mul_halfWidth_mul_exactResidualRegularMoment_lt_one_eightThousand
    _ < (1 / 250 : ℝ) := by norm_num

/-- Unconditional positivity of the P11-augmented finite Galerkin residual.
The later tail certificate may retain more modes, but this rank-one pivot is
a reusable finite checkpoint. -/
theorem fourCellOddP13RankOneAugmentedResidual_core_pos :
    0 < fourCellOddCoreLocalQuadratic
      fourCellOddP13RankOneAugmentedResidual :=
  fourCellOddP13RankOneAugmentedResidual_core_pos_of_D_and_cross_bounds
    three_div_twenty_lt_fourCellOddP11OldBlockSchurPivot
    abs_fourCellOddP11ExactResidualTailCross_lt_one_twoHundredFifty

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualRegularMomentSmallStructural
