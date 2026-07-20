import ArithmeticHodge.Analysis.YoshidaFourCellOddP51EndpointStripRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP51Kernel18ErrorBudgetStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51Kernel18RowDecompositionStructural

noncomputable section

open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFourCellEvenEndpointSeedFiniteSevenEntryEnclosuresStructural
open YoshidaFourCellOddP51EndpointStripRepresenterStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddP51Kernel18ErrorBudgetStructural
open YoshidaFourCellOddP51RawMassCancellationStructural
open YoshidaFourCellOddP51TailBudgetAssemblyStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# Exact degree-eighteen row decomposition at the P51 cutoff

The exact regular kernel is only measurable at its removable value, so the
decomposition is performed after integration.  A bounded-measurable lag
representer lemma folds the exact, polynomial, and error rows separately to
the positive half interval.  The endpoint strip is then inserted as one
piecewise polynomial correction.
-/

private theorem lagRightRepresenter_neg_of_odd
    (q p : ℝ → ℝ) (hp : Function.Odd p) (x : ℝ) :
    factorTwoContinuousLagRightRepresenter q p (-x) =
      -factorTwoContinuousLagLeftRepresenter q p x := by
  unfold factorTwoContinuousLagRightRepresenter
    factorTwoContinuousLagLeftRepresenter
  have h := intervalIntegral.integral_comp_neg
    (f := fun y : ℝ ↦ q (y + x) * p y)
    (a := (-1 : ℝ)) (b := x)
  have heq : (fun y : ℝ ↦ q (-y + x) * p (-y)) =
      fun y ↦ -(q (x - y) * p y) := by
    funext y
    rw [hp y]
    ring
  rw [heq, intervalIntegral.integral_neg] at h
  calc
    (∫ y : ℝ in -x..1, q (y - -x) * p y) =
        ∫ y : ℝ in -x..1, q (y + x) * p y := by
      apply intervalIntegral.integral_congr
      intro y _hy
      ring
    _ = _ := by simpa only [neg_neg] using h.symm

private theorem lagLeftRepresenter_neg_of_odd
    (q p : ℝ → ℝ) (hp : Function.Odd p) (x : ℝ) :
    factorTwoContinuousLagLeftRepresenter q p (-x) =
      -factorTwoContinuousLagRightRepresenter q p x := by
  unfold factorTwoContinuousLagLeftRepresenter
    factorTwoContinuousLagRightRepresenter
  have h := intervalIntegral.integral_comp_neg
    (f := fun y : ℝ ↦ q (y - x) * p y)
    (a := (-1 : ℝ)) (b := -x)
  have heq : (fun y : ℝ ↦ q (-y - x) * p (-y)) =
      fun y ↦ -(q (-x - y) * p y) := by
    funext y
    rw [hp y]
    ring
  rw [heq, intervalIntegral.integral_neg] at h
  have h' := congrArg Neg.neg h
  simpa only [neg_neg] using h'

/-- The symmetric continuous-lag representer preserves odd parity without
requiring continuity of the lag kernel. -/
theorem odd_factorTwoContinuousLagK_of_odd
    (q p : ℝ → ℝ) (hp : Function.Odd p) :
    Function.Odd (factorTwoContinuousLagK q p) := by
  intro x
  unfold factorTwoContinuousLagK
  rw [lagRightRepresenter_neg_of_odd q p hp,
    lagLeftRepresenter_neg_of_odd q p hp]
  ring

/-- A bounded measurable lag kernel paired with two odd continuous profiles
is represented directly on the positive half interval. -/
theorem integral_boundedLag_mul_correlationBilinear_eq_zero_one_K_of_odd
    (q u v : ℝ → ℝ) (hq : Measurable q)
    (hu : Continuous u) (hv : Continuous v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v)
    (C : ℝ) (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    (∫ t : ℝ in 0..2,
        q t * factorTwoCenteredCorrelationBilinear u v t) =
      ∫ x : ℝ in 0..1,
        v x * factorTwoContinuousLagK q u x := by
  have hright :=
    intervalIntegrable_mul_factorTwoContinuousLagRightRepresenter_of_bounded
      q u v hq hu hv C hqC
  have hleft :=
    intervalIntegrable_mul_factorTwoContinuousLagLeftRepresenter_of_bounded
      q v u hq hv hu C hqC
  have hKI : IntervalIntegrable
      (fun x : ℝ ↦ v x * factorTwoContinuousLagK q u x)
      volume (-1) 1 := by
    unfold factorTwoContinuousLagK
    rw [show (fun x : ℝ ↦ v x *
        (factorTwoContinuousLagRightRepresenter q u x +
          factorTwoContinuousLagLeftRepresenter q u x)) =
      fun x ↦
        v x * factorTwoContinuousLagRightRepresenter q u x +
          v x * factorTwoContinuousLagLeftRepresenter q u x by
      funext x
      ring]
    exact hright.add hleft
  have heven : Function.Even (fun x : ℝ ↦
      v x * factorTwoContinuousLagK q u x) := by
    intro x
    change v (-x) * factorTwoContinuousLagK q u (-x) =
      v x * factorTwoContinuousLagK q u x
    rw [hvodd x, odd_factorTwoContinuousLagK_of_odd q u huodd x]
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ v x * factorTwoContinuousLagK q u x) hKI heven
  have hrepr := integral_boundedLag_mul_correlationBilinear_eq_K
    q u v hq hu hv C hqC
  calc
    (∫ t : ℝ in 0..2,
        q t * factorTwoCenteredCorrelationBilinear u v t) =
        (1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
          v x * factorTwoContinuousLagK q u x := hrepr
    _ = (1 / 2 : ℝ) *
        (2 * ∫ x : ℝ in 0..1,
          v x * factorTwoContinuousLagK q u x) := by rw [hfold]
    _ = ∫ x : ℝ in 0..1,
        v x * factorTwoContinuousLagK q u x := by ring

theorem continuous_fourCellOddP51Polynomial18RegularLagKernel :
    Continuous fourCellOddP51Polynomial18RegularLagKernel := by
  unfold fourCellOddP51Polynomial18RegularLagKernel
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

private theorem exactRegularLag_abs_le_quarter
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    |fourCellOddP51ExactRegularLagKernel t| ≤ (1 / 4 : ℝ) := by
  have hh0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
    mul_nonneg hh0 ht.1
  have harg4 : fourCellOperatorHalfWidth * t ≤
      5 * Real.log 2 / 4 := by
    calc
      fourCellOperatorHalfWidth * t ≤ fourCellOperatorHalfWidth * 2 :=
        mul_le_mul_of_nonneg_left ht.2 hh0
      _ = 5 * Real.log 2 / 4 := by
        unfold fourCellOperatorHalfWidth
        ring
  have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg4
  unfold fourCellOddP51ExactRegularLagKernel
  rw [abs_of_nonneg hk0]
  exact yoshidaRegularKernel_le_quarter harg0

private theorem polynomial18RegularLag_abs_le
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    |fourCellOddP51Polynomial18RegularLagKernel t| ≤
      (1 / 4 + 1 / 380000000000 : ℝ) := by
  have herror := abs_fourCellOddP51Kernel18LagError_le ht
  have hexact := exactRegularLag_abs_le_quarter t ht
  unfold fourCellOddP51Kernel18LagError at herror
  calc
    |fourCellOddP51Polynomial18RegularLagKernel t| =
        |fourCellOddP51ExactRegularLagKernel t -
          fourCellOddP51Kernel18LagError t| := by
      congr 1
      unfold fourCellOddP51Kernel18LagError
      ring
    _ ≤ |fourCellOddP51ExactRegularLagKernel t| +
        |fourCellOddP51Kernel18LagError t| := abs_sub _ _
    _ ≤ (1 / 4 : ℝ) + 1 / 380000000000 := add_le_add hexact herror

private theorem measurable_fourCellOddP51ExactRegularLagKernel :
    Measurable fourCellOddP51ExactRegularLagKernel := by
  unfold fourCellOddP51ExactRegularLagKernel
  exact measurable_yoshidaRegularKernel.comp
    (measurable_const.mul measurable_id)

private theorem measurable_fourCellOddP51Polynomial18RegularLagKernel :
    Measurable fourCellOddP51Polynomial18RegularLagKernel :=
  continuous_fourCellOddP51Polynomial18RegularLagKernel.measurable

/-- Exact regular correlation equals the degree-eighteen correlation plus
the measurable lag-error correlation. -/
theorem fourCellOddP51ExactRegularCorrelation_eq_polynomial18_add_error
    (r : ℝ → ℝ) (hr : Continuous r) :
    (∫ t : ℝ in 0..2,
        fourCellOddP51ExactRegularLagKernel t *
          factorTwoCenteredCorrelationBilinear fourCellOddQ51 r t) =
      (∫ t : ℝ in 0..2,
        fourCellOddP51Polynomial18RegularLagKernel t *
          factorTwoCenteredCorrelationBilinear fourCellOddQ51 r t) +
      ∫ t : ℝ in 0..2,
        fourCellOddP51Kernel18LagError t *
          factorTwoCenteredCorrelationBilinear fourCellOddQ51 r t := by
  let C : ℝ → ℝ :=
    factorTwoCenteredCorrelationBilinear fourCellOddQ51 r
  have hC : Continuous C := by
    dsimp only [C]
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation
      fourCellOddQ51 r contDiff_fourCellOddQ51.continuous hr).add
      (continuous_factorTwoCenteredCrossCorrelation
        r fourCellOddQ51 hr contDiff_fourCellOddQ51.continuous)).div_const 2
  have hexactI := intervalIntegrable_boundedLag_mul_continuous
    fourCellOddP51ExactRegularLagKernel C
    measurable_fourCellOddP51ExactRegularLagKernel hC (1 / 4)
    exactRegularLag_abs_le_quarter
  have hpolyI := intervalIntegrable_boundedLag_mul_continuous
    fourCellOddP51Polynomial18RegularLagKernel C
    measurable_fourCellOddP51Polynomial18RegularLagKernel hC
    (1 / 4 + 1 / 380000000000) polynomial18RegularLag_abs_le
  have herr :
      (∫ t : ℝ in 0..2,
        fourCellOddP51Kernel18LagError t * C t) =
      (∫ t : ℝ in 0..2,
        fourCellOddP51ExactRegularLagKernel t * C t) -
      ∫ t : ℝ in 0..2,
        fourCellOddP51Polynomial18RegularLagKernel t * C t := by
    rw [← intervalIntegral.integral_sub hexactI hpolyI]
    apply intervalIntegral.integral_congr
    intro t _ht
    unfold fourCellOddP51Kernel18LagError
    ring
  have herr' :
      (∫ t : ℝ in 0..2,
        fourCellOddP51Kernel18LagError t *
          factorTwoCenteredCorrelationBilinear fourCellOddQ51 r t) =
      (∫ t : ℝ in 0..2,
        fourCellOddP51ExactRegularLagKernel t *
          factorTwoCenteredCorrelationBilinear fourCellOddQ51 r t) -
      ∫ t : ℝ in 0..2,
        fourCellOddP51Polynomial18RegularLagKernel t *
          factorTwoCenteredCorrelationBilinear fourCellOddQ51 r t := by
    simpa only [C] using herr
  linarith [herr']

/-- The exact smooth P51 row splits into the polynomial representer and the
compiled measurable error representer on every odd continuous test. -/
theorem fourCellOddP51ExactRegularRow_eq_polynomial18_add_error
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r) :
    -2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          fourCellOddP51ExactRegularLagKernel t *
            factorTwoCenteredCorrelationBilinear fourCellOddQ51 r t) =
      (∫ x : ℝ in 0..1,
        ((-2 * fourCellOperatorHalfWidth) *
          factorTwoContinuousLagK
            fourCellOddP51Polynomial18RegularLagKernel
            fourCellOddQ51 x) * r x) +
      ∫ x : ℝ in 0..1,
        fourCellOddP51Kernel18ErrorRepresenter x * r x := by
  have hpoly :=
    integral_boundedLag_mul_correlationBilinear_eq_zero_one_K_of_odd
      fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 r
      measurable_fourCellOddP51Polynomial18RegularLagKernel
      contDiff_fourCellOddQ51.continuous hr
      odd_fourCellOddQ51 hodd
      (1 / 4 + 1 / 380000000000) polynomial18RegularLag_abs_le
  have herror :=
    integral_boundedLag_mul_correlationBilinear_eq_zero_one_K_of_odd
      fourCellOddP51Kernel18LagError fourCellOddQ51 r
      measurable_fourCellOddP51Kernel18LagError
      contDiff_fourCellOddQ51.continuous hr
      odd_fourCellOddQ51 hodd (1 / 380000000000)
      (fun _t ht ↦ abs_fourCellOddP51Kernel18LagError_le ht)
  have hsplit := fourCellOddP51ExactRegularCorrelation_eq_polynomial18_add_error
    r hr
  rw [hpoly, herror] at hsplit
  rw [hsplit]
  unfold fourCellOddP51Kernel18ErrorRepresenter
  rw [show (fun x : ℝ ↦
      ((-2 * fourCellOperatorHalfWidth) *
        factorTwoContinuousLagK
          fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x) * r x) =
    fun x ↦ (-2 * fourCellOperatorHalfWidth) *
      (r x * factorTwoContinuousLagK
        fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul,
    show (fun x : ℝ ↦
      ((-2 * fourCellOperatorHalfWidth) *
        factorTwoContinuousLagK fourCellOddP51Kernel18LagError
          fourCellOddQ51 x) * r x) =
      fun x ↦ (-2 * fourCellOperatorHalfWidth) *
        (r x * factorTwoContinuousLagK fourCellOddP51Kernel18LagError
          fourCellOddQ51 x) by
      funext x
      ring,
    intervalIntegral.integral_const_mul]
  ring

/-- Degree-eighteen nonsingular base density, before inserting the physical
upper-strip correction. -/
def fourCellOddP51Kernel18BaseRepresenter (x : ℝ) : ℝ :=
  (93 / 50 : ℝ) * yoshidaEndpointPotential x * fourCellOddQ51 x -
    2 * fourCellOperatorHalfWidth *
      factorTwoContinuousLagK
        fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x

/-- Complete finite-main density.  The weak inequality puts the cutoff point
in the lower interval; the upper interval integral excludes that point. -/
def fourCellOddP51Kernel18MainRepresenter (x : ℝ) : ℝ :=
  if x ≤ (3 / 5 : ℝ) then
    fourCellOddP51Kernel18BaseRepresenter x
  else
    fourCellOddP51Kernel18BaseRepresenter x +
      fourCellOddQ51UpperEndpointCorrection x

/-- Integral of the piecewise main density is the global potential and
polynomial regular row plus the physical upper-strip correction. -/
theorem integral_zero_one_fourCellOddP51Kernel18MainRepresenter_mul
    (r : ℝ → ℝ) (hr : Continuous r) :
    (∫ x : ℝ in 0..1,
        fourCellOddP51Kernel18MainRepresenter x * r x) =
      (93 / 50 : ℝ) *
          (∫ x : ℝ in 0..1,
            yoshidaEndpointPotential x * fourCellOddQ51 x * r x) -
        2 * fourCellOperatorHalfWidth *
          (∫ x : ℝ in 0..1,
            factorTwoContinuousLagK
              fourCellOddP51Polynomial18RegularLagKernel
              fourCellOddQ51 x * r x) +
        ∫ x : ℝ in 3 / 5..1,
          fourCellOddQ51UpperEndpointCorrection x * r x := by
  let P : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * fourCellOddQ51 x * r x
  let R : ℝ → ℝ := fun x ↦
    factorTwoContinuousLagK
      fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x * r x
  let U : ℝ → ℝ := fun x ↦
    fourCellOddQ51UpperEndpointCorrection x * r x
  let B : ℝ → ℝ := fun x ↦
    (93 / 50 : ℝ) * P x - 2 * fourCellOperatorHalfWidth * R x
  have hP : IntervalIntegrable P volume 0 1 := by
    have hPfull := intervalIntegrable_endpointPotential_mul
      fourCellOddQ51 r contDiff_fourCellOddQ51.continuous hr
    dsimp only [P]
    exact hPfull.mono_set (by
      intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact ⟨by linarith [hx.1], hx.2⟩)
  have hR : IntervalIntegrable R volume 0 1 := by
    dsimp only [R]
    exact ((continuous_factorTwoContinuousLagK
      fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51
      continuous_fourCellOddP51Polynomial18RegularLagKernel
      contDiff_fourCellOddQ51.continuous).mul hr).intervalIntegrable _ _
  have hB : IntervalIntegrable B volume 0 1 := by
    dsimp only [B]
    exact (hP.const_mul _).sub (hR.const_mul _)
  have hBL : IntervalIntegrable B volume 0 (3 / 5) := by
    exact hB.mono_set (by
      intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact ⟨hx.1, by linarith [hx.2]⟩)
  have hBU : IntervalIntegrable B volume (3 / 5) 1 := by
    exact hB.mono_set (by
      intro x hx
      rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact ⟨by linarith [hx.1], hx.2⟩)
  have hU : IntervalIntegrable U volume (3 / 5) 1 := by
    dsimp only [U]
    exact (continuous_fourCellOddQ51UpperEndpointCorrection.mul hr)
      |>.intervalIntegrable _ _
  have hmainL : IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddP51Kernel18MainRepresenter x * r x)
      volume 0 (3 / 5) := by
    apply hBL.congr
    intro x hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    unfold fourCellOddP51Kernel18MainRepresenter
      fourCellOddP51Kernel18BaseRepresenter
    change B x = (if x ≤ (3 / 5 : ℝ) then
        (93 / 50 : ℝ) * yoshidaEndpointPotential x * fourCellOddQ51 x -
          2 * fourCellOperatorHalfWidth *
            factorTwoContinuousLagK
              fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x
      else
        ((93 / 50 : ℝ) * yoshidaEndpointPotential x * fourCellOddQ51 x -
          2 * fourCellOperatorHalfWidth *
            factorTwoContinuousLagK
              fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x) +
          fourCellOddQ51UpperEndpointCorrection x) * r x
    rw [if_pos hx.2]
    dsimp only [B, P, R]
    ring
  have hmainU : IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddP51Kernel18MainRepresenter x * r x)
      volume (3 / 5) 1 := by
    apply (hBU.add hU).congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      MeasureTheory.ae_restrict_of_ae
        (MeasureTheory.Measure.ae_ne volume (3 / 5 : ℝ))] with x hx hxne
    rw [uIoc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    unfold fourCellOddP51Kernel18MainRepresenter
      fourCellOddP51Kernel18BaseRepresenter
    rw [if_neg (by linarith [hx.1])]
    dsimp only [B, P, R, U]
    ring
  have hmainSplit := intervalIntegral.integral_add_adjacent_intervals
    hmainL hmainU
  have hbaseSplit := intervalIntegral.integral_add_adjacent_intervals
    hBL hBU
  have hmainLower :
      (∫ x : ℝ in 0..3 / 5,
        fourCellOddP51Kernel18MainRepresenter x * r x) =
      ∫ x : ℝ in 0..3 / 5, B x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    unfold fourCellOddP51Kernel18MainRepresenter
      fourCellOddP51Kernel18BaseRepresenter
    change (if x ≤ (3 / 5 : ℝ) then
        (93 / 50 : ℝ) * yoshidaEndpointPotential x * fourCellOddQ51 x -
          2 * fourCellOperatorHalfWidth *
            factorTwoContinuousLagK
              fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x
      else
        ((93 / 50 : ℝ) * yoshidaEndpointPotential x * fourCellOddQ51 x -
          2 * fourCellOperatorHalfWidth *
            factorTwoContinuousLagK
              fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x) +
          fourCellOddQ51UpperEndpointCorrection x) * r x = B x
    rw [if_pos hx.2]
    dsimp only [B, P, R]
    ring
  have hmainUpper :
      (∫ x : ℝ in 3 / 5..1,
        fourCellOddP51Kernel18MainRepresenter x * r x) =
      (∫ x : ℝ in 3 / 5..1, B x) +
        ∫ x : ℝ in 3 / 5..1, U x := by
    rw [← intervalIntegral.integral_add hBU hU]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (3 / 5 : ℝ)] with x hxne
    intro hx
    rw [uIoc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    unfold fourCellOddP51Kernel18MainRepresenter
      fourCellOddP51Kernel18BaseRepresenter
    rw [if_neg (by linarith [hx.1])]
    dsimp only [B, P, R, U]
    ring
  calc
    (∫ x : ℝ in 0..1,
        fourCellOddP51Kernel18MainRepresenter x * r x) =
        (∫ x : ℝ in 0..3 / 5,
          fourCellOddP51Kernel18MainRepresenter x * r x) +
        ∫ x : ℝ in 3 / 5..1,
          fourCellOddP51Kernel18MainRepresenter x * r x := hmainSplit.symm
    _ = (∫ x : ℝ in 0..3 / 5, B x) +
        ((∫ x : ℝ in 3 / 5..1, B x) +
          ∫ x : ℝ in 3 / 5..1, U x) := by
      rw [hmainLower, hmainUpper]
    _ = ((∫ x : ℝ in 0..3 / 5, B x) +
          ∫ x : ℝ in 3 / 5..1, B x) +
        ∫ x : ℝ in 3 / 5..1, U x := by ring
    _ = (∫ x : ℝ in 0..1, B x) +
        ∫ x : ℝ in 3 / 5..1, U x := by rw [hbaseSplit]
    _ = (93 / 50 : ℝ) *
          (∫ x : ℝ in 0..1,
            yoshidaEndpointPotential x * fourCellOddQ51 x * r x) -
        2 * fourCellOperatorHalfWidth *
          (∫ x : ℝ in 0..1,
            factorTwoContinuousLagK
              fourCellOddP51Polynomial18RegularLagKernel
              fourCellOddQ51 x * r x) +
        ∫ x : ℝ in 3 / 5..1,
          fourCellOddQ51UpperEndpointCorrection x * r x := by
      dsimp only [B, P, R, U]
      rw [intervalIntegral.integral_sub (hP.const_mul _) (hR.const_mul _)]
      repeat rw [intervalIntegral.integral_const_mul]

/-- Exact production row decomposition into the degree-eighteen finite main
representer and the uniformly tiny measurable kernel error. -/
theorem fourCellOddP51Kernel18TailRowDecomposition :
    FourCellOddP51TailRowDecomposition
      fourCellOddP51Kernel18MainRepresenter
      fourCellOddP51Kernel18ErrorRepresenter := by
  intro r hr hodd htail
  have hcore := fourCellOddCoreLocalBilinear_Q51_P53Plus_eq_retained_regular
    r hr hodd htail
  have hchannels := fourCellOddQ51_endpoint_channels_eq_upperCorrection r hr
  have hregular := fourCellOddP51ExactRegularRow_eq_polynomial18_add_error
    r hr.continuous hodd
  have hmain := integral_zero_one_fourCellOddP51Kernel18MainRepresenter_mul
    r hr.continuous
  have hpolyScale :
      (∫ x : ℝ in 0..1,
        ((-2 * fourCellOperatorHalfWidth) *
          factorTwoContinuousLagK
            fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x) *
          r x) =
      -2 * fourCellOperatorHalfWidth *
        ∫ x : ℝ in 0..1,
          factorTwoContinuousLagK
            fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x *
            r x := by
    rw [show (fun x : ℝ ↦
        ((-2 * fourCellOperatorHalfWidth) *
          factorTwoContinuousLagK
            fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x) *
          r x) =
      fun x ↦ (-2 * fourCellOperatorHalfWidth) *
        (factorTwoContinuousLagK
          fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x *
            r x) by
      funext x
      ring,
      intervalIntegral.integral_const_mul]
  rw [hpolyScale] at hregular
  unfold fourCellOddRetainedPrimePotentialBilinear at hcore
  change fourCellOddCoreLocalBilinear fourCellOddQ51 r =
      -(1 / 2 : ℝ) *
          fourCellOddEndpointStripOddRawPolarization fourCellOddQ51 r +
        (Real.sqrt 2 * Real.log 2 *
            fourCellOddEndpointStripEvenMassBilinear fourCellOddQ51 r +
          (2 - Real.sqrt 2 * Real.log 2) *
            fourCellOddEndpointStripOddMassBilinear fourCellOddQ51 r +
          (93 / 50 : ℝ) *
            (∫ x : ℝ in 0..1,
              yoshidaEndpointPotential x * fourCellOddQ51 x * r x)) -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            fourCellOddP51ExactRegularLagKernel t *
              factorTwoCenteredCorrelationBilinear fourCellOddQ51 r t) at hcore
  linear_combination hcore + hchannels + hregular - hmain

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51Kernel18RowDecompositionStructural
