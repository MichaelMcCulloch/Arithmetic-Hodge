import ArithmeticHodge.Analysis.YoshidaFactorTwoContinuousLagUniformErrorStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedFiniteSevenEntryEnclosuresStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP51TailBudgetAssemblyStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51Kernel18ErrorBudgetStructural

noncomputable section

open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoContinuousLagUniformErrorStructural
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFourCellEvenEndpointSeedFiniteSevenEntryEnclosuresStructural
open YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddP51TailBudgetAssemblyStructural
open YoshidaFourCellOddPolarPotentialStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# Degree-eighteen kernel error budget for the P51 tail

The exact regular Yoshida lag kernel is replaced by its degree-eighteen
polynomial center.  The one-sided envelope on `[0, 7/8]` supplies a uniform
error of `1 / 380000000000`; the continuous-lag `L²` estimate then makes the
scaled representer consume at most one thousandth of the P51 Schur budget.

The exact kernel has only a measurable removable value at zero.  Accordingly,
the proof uses the measurable-lag representer API and the `MemLp` Cauchy
handoff, never a fictitious continuity statement for the kernel error.
-/

/-- Exact regular Yoshida lag kernel on the normalized four-cell distance. -/
def fourCellOddP51ExactRegularLagKernel (t : ℝ) : ℝ :=
  yoshidaRegularKernel (fourCellOperatorHalfWidth * t)

/-- Degree-eighteen polynomial lag kernel on the same normalized distance. -/
def fourCellOddP51Polynomial18RegularLagKernel (t : ℝ) : ℝ :=
  fourCellEvenFiniteSevenRegularKernelPolynomial18
    (fourCellOperatorHalfWidth * t)

/-- Lag-kernel error after scaling the centered distance by the four-cell
halfwidth. -/
def fourCellOddP51Kernel18LagError (t : ℝ) : ℝ :=
  fourCellOddP51ExactRegularLagKernel t -
    fourCellOddP51Polynomial18RegularLagKernel t

/-- Error term in the exact P51 regular representer.  The factor `-2h` is the
coefficient of the regular row in the odd four-cell bilinear form. -/
def fourCellOddP51Kernel18ErrorRepresenter (x : ℝ) : ℝ :=
  (-2 * fourCellOperatorHalfWidth) *
    factorTwoContinuousLagK fourCellOddP51Kernel18LagError fourCellOddQ51 x

theorem measurable_fourCellOddP51Kernel18LagError :
    Measurable fourCellOddP51Kernel18LagError := by
  unfold fourCellOddP51Kernel18LagError
    fourCellOddP51ExactRegularLagKernel
    fourCellOddP51Polynomial18RegularLagKernel
  apply Measurable.sub
  · exact measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)
  · apply Continuous.measurable
    change Continuous (fun t : ℝ ↦ (1 / 4 : ℝ) *
      ((1 - (fourCellOperatorHalfWidth * t / 2) ^ 2 / 2 +
          5 * (fourCellOperatorHalfWidth * t / 2) ^ 4 / 24 -
          61 * (fourCellOperatorHalfWidth * t / 2) ^ 6 / 720 +
          277 * (fourCellOperatorHalfWidth * t / 2) ^ 8 / 8064 -
          50521 * (fourCellOperatorHalfWidth * t / 2) ^ 10 / 3628800 +
          540553 * (fourCellOperatorHalfWidth * t / 2) ^ 12 / 95800320 -
          199360981 * (fourCellOperatorHalfWidth * t / 2) ^ 14 / 87178291200 +
          3878302429 * (fourCellOperatorHalfWidth * t / 2) ^ 16 /
            4184557977600 -
          2404879675441 * (fourCellOperatorHalfWidth * t / 2) ^ 18 /
            6402373705728000) +
        (-(fourCellOperatorHalfWidth * t / 2) / 6 +
          7 * (fourCellOperatorHalfWidth * t / 2) ^ 3 / 360 -
          31 * (fourCellOperatorHalfWidth * t / 2) ^ 5 / 15120 +
          127 * (fourCellOperatorHalfWidth * t / 2) ^ 7 / 604800 -
          73 * (fourCellOperatorHalfWidth * t / 2) ^ 9 / 3421440 +
          1414477 * (fourCellOperatorHalfWidth * t / 2) ^ 11 /
            653837184000 -
          8191 * (fourCellOperatorHalfWidth * t / 2) ^ 13 / 37362124800 +
          16931177 * (fourCellOperatorHalfWidth * t / 2) ^ 15 /
            762187345920000 -
          5749691557 * (fourCellOperatorHalfWidth * t / 2) ^ 17 /
            2554547108585472000)))
    fun_prop

/-- The degree-eighteen center controls the complete lag range used by the
four-cell operator. -/
theorem abs_fourCellOddP51Kernel18LagError_le
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    |fourCellOddP51Kernel18LagError t| ≤
      (1 / 380000000000 : ℝ) := by
  have hh0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
    mul_nonneg hh0 ht.1
  have harg : fourCellOperatorHalfWidth * t ≤ (7 / 8 : ℝ) := by
    calc
      fourCellOperatorHalfWidth * t ≤
          fourCellOperatorHalfWidth * 2 :=
        mul_le_mul_of_nonneg_left ht.2 hh0
      _ ≤ (7 / 8 : ℝ) := by
        have hlog := YoshidaConstantBounds.strict_log_two_bounds.2
        unfold fourCellOperatorHalfWidth
        nlinarith
  have henv :=
    fourCellEvenFiniteSevenRegularKernelPolynomial18_sevenEighths_envelope
      harg0 harg
  unfold fourCellOddP51Kernel18LagError
    fourCellOddP51ExactRegularLagKernel
    fourCellOddP51Polynomial18RegularLagKernel
  rw [abs_of_nonneg henv.1]
  exact henv.2.le

/-- Positive-half `L²` error before spending any finite P51 pivot reserve. -/
theorem integral_zero_one_fourCellOddP51Kernel18ErrorRepresenter_sq_le :
    (∫ x : ℝ in 0..1,
      fourCellOddP51Kernel18ErrorRepresenter x ^ 2) ≤
      16 * fourCellOperatorHalfWidth ^ 2 *
        (1 / 380000000000 : ℝ) ^ 2 *
          ∫ x : ℝ in 0..1, fourCellOddQ51 x ^ 2 := by
  have hbase :=
    integral_zero_one_factorTwoContinuousLagK_sq_le_of_uniform_of_odd
      fourCellOddP51Kernel18LagError fourCellOddQ51
      (1 / 380000000000 : ℝ)
      contDiff_fourCellOddQ51.continuous odd_fourCellOddQ51
      (by norm_num) (fun t ht ↦ abs_fourCellOddP51Kernel18LagError_le ht)
  rw [show (fun x : ℝ ↦
      fourCellOddP51Kernel18ErrorRepresenter x ^ 2) =
      fun x ↦ 4 * fourCellOperatorHalfWidth ^ 2 *
        factorTwoContinuousLagK fourCellOddP51Kernel18LagError
          fourCellOddQ51 x ^ 2 by
    funext x
    unfold fourCellOddP51Kernel18ErrorRepresenter
    ring,
    intervalIntegral.integral_const_mul]
  calc
    4 * fourCellOperatorHalfWidth ^ 2 *
        (∫ x : ℝ in 0..1,
          factorTwoContinuousLagK fourCellOddP51Kernel18LagError
            fourCellOddQ51 x ^ 2) ≤
        4 * fourCellOperatorHalfWidth ^ 2 *
          (4 * (1 / 380000000000 : ℝ) ^ 2 *
            ∫ x : ℝ in 0..1, fourCellOddQ51 x ^ 2) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = 16 * fourCellOperatorHalfWidth ^ 2 *
        (1 / 380000000000 : ℝ) ^ 2 *
          ∫ x : ℝ in 0..1, fourCellOddQ51 x ^ 2 := by ring

/-- The scaled error representer belongs to `L²(0,1)`.  This is proved from
bounded measurable lag disintegration, not continuity of the regular kernel. -/
theorem memLp_fourCellOddP51Kernel18ErrorRepresenter_two_restrict :
    MemLp fourCellOddP51Kernel18ErrorRepresenter 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  let d : ℝ → ℝ := fourCellOddP51Kernel18LagError
  let q : ℝ → ℝ := fourCellOddQ51
  let eps : ℝ := 1 / 380000000000
  have hdMeas : Measurable d := by
    simpa only [d] using measurable_fourCellOddP51Kernel18LagError
  have hq : Continuous q := by
    simpa only [q] using contDiff_fourCellOddQ51.continuous
  have hdBound : ∀ t ∈ Icc (0 : ℝ) 2, |d t| ≤ eps := by
    intro t ht
    simpa only [d, eps] using abs_fourCellOddP51Kernel18LagError_le ht
  have hrightI :=
    intervalIntegrable_mul_factorTwoContinuousLagRightRepresenter_of_bounded
      d q (fun _ : ℝ ↦ 1) hdMeas hq continuous_const eps hdBound
  have hleftI :=
    intervalIntegrable_mul_factorTwoContinuousLagLeftRepresenter_of_bounded
      d (fun _ : ℝ ↦ 1) q hdMeas continuous_const hq eps hdBound
  have hKI : IntervalIntegrable (factorTwoContinuousLagK d q)
      volume (-1) 1 := by
    apply (hrightI.add hleftI).congr
    intro x _hx
    unfold factorTwoContinuousLagK
    simp only [one_mul]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hKI
  have hKI01 : IntegrableOn (factorTwoContinuousLagK d q)
      (Ioc (0 : ℝ) 1) := by
    exact hKI.mono_set (by
      intro x hx
      exact ⟨by linarith [hx.1], hx.2⟩)
  have hmeas : AEStronglyMeasurable (factorTwoContinuousLagK d q)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hKI01.aestronglyMeasurable
  let L : ℝ := ∫ y : ℝ in -1..1, |q y|
  have hLp : MemLp (factorTwoContinuousLagK d q) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply MemLp.of_bound hmeas (eps * L)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    exact abs_factorTwoContinuousLagK_le_of_uniform
      d q eps hq (by dsimp only [eps]; norm_num) hdBound
        ⟨by linarith [hx.1], hx.2⟩
  have hscaled := hLp.const_mul (-2 * fourCellOperatorHalfWidth)
  simpa only [d, q, fourCellOddP51Kernel18ErrorRepresenter] using hscaled

/-- Exact finite premise still needed from the P51 Galerkin solve. -/
def FourCellOddP51GalerkinPivotSevenTenThousandFloor : Prop :=
  (7 / 10000 : ℝ) ≤ fourCellOddP51GalerkinPivot

/-- Harmless normalization premise for the exact polynomial `q51`. -/
def FourCellOddQ51PositiveHalfMassAtMostOne : Prop :=
  (∫ x : ℝ in 0..1, fourCellOddQ51 x ^ 2) ≤ 1

/-- Any coercivity constant above `343 / 12500` leaves far more than enough
room for the uniform degree-eighteen kernel error. -/
theorem integral_zero_one_fourCellOddP51Kernel18ErrorRepresenter_sq_le_budget_of_kappa_floor
    (kappa : ℝ) (hkappa : (343 / 12500 : ℝ) ≤ kappa)
    (hpivot : FourCellOddP51GalerkinPivotSevenTenThousandFloor)
    (hmass : FourCellOddQ51PositiveHalfMassAtMostOne) :
    (∫ x : ℝ in 0..1,
      fourCellOddP51Kernel18ErrorRepresenter x ^ 2) ≤
      (1 / 1000 : ℝ) *
        (fourCellOddP51GalerkinPivot * kappa) := by
  have hl2 := integral_zero_one_fourCellOddP51Kernel18ErrorRepresenter_sq_le
  have hh0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hh : fourCellOperatorHalfWidth < (1 / 2 : ℝ) :=
    fourCellOperatorHalfWidth_lt_one_half
  have hhSq : fourCellOperatorHalfWidth ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [sq_nonneg (fourCellOperatorHalfWidth - 1 / 2)]
  have hpivot0 : 0 ≤ fourCellOddP51GalerkinPivot :=
    (by norm_num : (0 : ℝ) ≤ 7 / 10000).trans hpivot
  have hprod : (7 / 10000 : ℝ) * (343 / 12500 : ℝ) ≤
      fourCellOddP51GalerkinPivot * kappa := by
    calc
      (7 / 10000 : ℝ) * (343 / 12500 : ℝ) ≤
          fourCellOddP51GalerkinPivot * (343 / 12500 : ℝ) :=
        mul_le_mul_of_nonneg_right hpivot (by norm_num)
      _ ≤ fourCellOddP51GalerkinPivot * kappa :=
        mul_le_mul_of_nonneg_left hkappa hpivot0
  calc
    (∫ x : ℝ in 0..1,
        fourCellOddP51Kernel18ErrorRepresenter x ^ 2) ≤
        16 * fourCellOperatorHalfWidth ^ 2 *
          (1 / 380000000000 : ℝ) ^ 2 *
            ∫ x : ℝ in 0..1, fourCellOddQ51 x ^ 2 := hl2
    _ ≤ 16 * fourCellOperatorHalfWidth ^ 2 *
          (1 / 380000000000 : ℝ) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ 16 * (1 / 4 : ℝ) *
          (1 / 380000000000 : ℝ) ^ 2 * 1 := by
      gcongr
    _ ≤ (1 / 1000 : ℝ) *
          ((7 / 10000 : ℝ) * (343 / 12500 : ℝ)) := by
      norm_num
    _ ≤ (1 / 1000 : ℝ) *
        (fourCellOddP51GalerkinPivot * kappa) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)

/-- The uniform kernel error is far below one thousandth of the production
P51 Schur budget.  Only the explicit finite pivot floor and `q51` mass bound
remain as premises. -/
theorem integral_zero_one_fourCellOddP51Kernel18ErrorRepresenter_sq_le_budget
    (hpivot : FourCellOddP51GalerkinPivotSevenTenThousandFloor)
    (hmass : FourCellOddQ51PositiveHalfMassAtMostOne) :
    (∫ x : ℝ in 0..1,
      fourCellOddP51Kernel18ErrorRepresenter x ^ 2) ≤
      (1 / 1000 : ℝ) *
        (fourCellOddP51GalerkinPivot *
          fourCellOddNineteenTwentiethsCoercivityConstant) := by
  exact
    integral_zero_one_fourCellOddP51Kernel18ErrorRepresenter_sq_le_budget_of_kappa_floor
      fourCellOddNineteenTwentiethsCoercivityConstant
      threeHundredFortyThree_div_twelveThousandFiveHundred_lt_coercivityConstant.le
      hpivot hmass

/-- Literal `19/20` specialization, useful when the retained fraction itself
is used as the ambient L² constant. -/
theorem integral_zero_one_fourCellOddP51Kernel18ErrorRepresenter_sq_le_nineteenTwentieths_budget
    (hpivot : FourCellOddP51GalerkinPivotSevenTenThousandFloor)
    (hmass : FourCellOddQ51PositiveHalfMassAtMostOne) :
    (∫ x : ℝ in 0..1,
      fourCellOddP51Kernel18ErrorRepresenter x ^ 2) ≤
      (1 / 1000 : ℝ) *
        (fourCellOddP51GalerkinPivot * (19 / 20 : ℝ)) := by
  exact
    integral_zero_one_fourCellOddP51Kernel18ErrorRepresenter_sq_le_budget_of_kappa_floor
      (19 / 20) (by norm_num) hpivot hmass

/-- Concrete `1/1000` error-pairing budget for the production
nineteen-twentieths P51 coercivity constant. -/
theorem fourCellOddP51Kernel18ErrorTailPairBudget
    (hpivot : FourCellOddP51GalerkinPivotSevenTenThousandFloor)
    (hmass : FourCellOddQ51PositiveHalfMassAtMostOne) :
    FourCellOddP51TailPairBudget (1 / 1000)
      fourCellOddNineteenTwentiethsCoercivityConstant
      fourCellOddP51Kernel18ErrorRepresenter := by
  exact fourCellOddP51TailPairBudget_one_thousandth_of_memLp_l2
    fourCellOddNineteenTwentiethsCoercivityConstant
    fourCellOddP51Kernel18ErrorRepresenter
    memLp_fourCellOddP51Kernel18ErrorRepresenter_two_restrict
    (integral_zero_one_fourCellOddP51Kernel18ErrorRepresenter_sq_le_budget
      hpivot hmass)

/-- Concrete literal-`19/20` form of the same `1/1000` pairing budget. -/
theorem fourCellOddP51Kernel18ErrorTailPairBudget_nineteenTwentieths
    (hpivot : FourCellOddP51GalerkinPivotSevenTenThousandFloor)
    (hmass : FourCellOddQ51PositiveHalfMassAtMostOne) :
    FourCellOddP51TailPairBudget (1 / 1000) (19 / 20)
      fourCellOddP51Kernel18ErrorRepresenter := by
  exact fourCellOddP51TailPairBudget_one_thousandth_of_memLp_l2
    (19 / 20) fourCellOddP51Kernel18ErrorRepresenter
    memLp_fourCellOddP51Kernel18ErrorRepresenter_two_restrict
    (integral_zero_one_fourCellOddP51Kernel18ErrorRepresenter_sq_le_nineteenTwentieths_budget
      hpivot hmass)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51Kernel18ErrorBudgetStructural
