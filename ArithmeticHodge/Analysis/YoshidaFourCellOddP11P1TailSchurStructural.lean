import ArithmeticHodge.Analysis.YoshidaFourCellOddP11ThreeHalvesClosureStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedRegularRemainderStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5CleanSharpStructural
import ArithmeticHodge.Analysis.IntervalIntegralAEMajorantStructural

set_option autoImplicit false

open MeasureTheory Real Set
open scoped Interval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11P1TailSchurStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicSixP5CleanSharpStructural
open YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
open YoshidaFourCellOddP11EndpointFormDualClosureStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP11ThreeHalvesClosureStructural
open YoshidaFourCellOddP11WeightedDualSelectorStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellEvenEndpointSeedCutoffEightBridgeStructural
open YoshidaFourCellEvenEndpointSeedRegularRemainderStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound
open IntervalIntegralAEMajorantStructural

/-!
# The pure `P₁`--`P₁₁+` Schur row

The failed scalar selector for an arbitrary retained five-mode polynomial
does not decide the pure degree-one row.  This file isolates that smaller
question.  The already proved scalar tail reserve is sufficient: one only
needs a degree-`< 11` selector whose weighted cost is at most the exact
`P₁` pivot.
-/

/-- The pure tail corrected reserve is the Schur complement of the `P₁`
pivot against one genuine `P₁₁+` residual. -/
def FourCellOddP11P1TailSchurNonnegative : Prop :=
  ∀ (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    0 ≤ fourCellOddP11TailCorrectedReserve r

/-- A scalar-weight proof of the pure row.  This is much weaker than the
discarded universal five-mode scalar selector: only the actual `P₁` row is
charged to the exact multiplication reserve. -/
def FourCellOddP11P1ExactWeightDual : Prop :=
  ∀ (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    fourCellOddCoreLocalBilinear centeredP1 r ^ 2 ≤
      fourCellOddCoreLocalQuadratic centeredP1 *
        fourCellOddP1ExactTailWeight r

/-- The existing exact scalar reserve and a selector proof for the sole
`P₁` row imply the genuine corrected tail Schur sign. -/
theorem fourCellOddP11P1TailSchurNonnegative_of_exactWeightDual
    (hdual : FourCellOddP11P1ExactWeightDual) :
    FourCellOddP11P1TailSchurNonnegative := by
  intro r hr hodd h1 h3 h5 h7 h9
  have hweight := fourCellOddP1ExactTailWeight_le_core r hr hodd h1
  have hpivot := fourCellOddCoreLocalQuadratic_centeredP1_nonneg
  have hmul := mul_le_mul_of_nonneg_left hweight hpivot
  have hrow := hdual r hr hodd h1 h3 h5 h7 h9
  unfold fourCellOddP11TailCorrectedReserve
  linarith

private theorem factorTwoContinuousLagRightRepresenter_neg_of_odd
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

private theorem factorTwoContinuousLagLeftRepresenter_neg_of_odd
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

/-- The regular convolution generated by an odd profile is odd.  The lag
weight need not be extended evenly: both ordered integrals only see
nonnegative lags, and reflection interchanges them. -/
private theorem odd_factorTwoContinuousLagK_of_odd
    (q p : ℝ → ℝ) (hp : Function.Odd p) :
    Function.Odd (factorTwoContinuousLagK q p) := by
  intro x
  unfold factorTwoContinuousLagK
  rw [factorTwoContinuousLagRightRepresenter_neg_of_odd q p hp,
    factorTwoContinuousLagLeftRepresenter_neg_of_odd q p hp]
  ring

/-- The degree-one smooth-kernel row in the exact affine representer. -/
def fourCellOddP11P1RegularRepresenter (x : ℝ) : ℝ :=
  fourCellOddFiveModeRegularRepresenter 1 0 0 0 0 x

/-- Degree-four kernel model of the smooth `P₁` representer. -/
def fourCellOddP11P1RegularPolynomialRepresenter (x : ℝ) : ℝ :=
  factorTwoContinuousLagK
    (fun t ↦ fourCellRegularKernelPolynomial4
      (fourCellOperatorHalfWidth * t)) centeredP1 x

/-- The genuine analytic remainder after removing the degree-four kernel
model from the smooth `P₁` representer. -/
def fourCellOddP11P1RegularRemainderRepresenter (x : ℝ) : ℝ :=
  factorTwoContinuousLagK fourCellEndpointSeedRegularKernelRemainder
    centeredP1 x

private theorem abs_centeredP1_le_one
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |centeredP1 x| ≤ 1 := by
  unfold centeredP1
  exact (abs_le.mpr hx)

/-- The analytic remainder is uniformly tiny on the complete centered
interval.  This is the first quantitative input for the selector cost: the
only nonpolynomial smooth row costs at most `1/700` pointwise. -/
theorem norm_fourCellOddP11P1RegularRemainderRepresenter_le
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖fourCellOddP11P1RegularRemainderRepresenter x‖ ≤
      (1 / 700 : ℝ) := by
  let E := fourCellEndpointSeedRegularKernelRemainder
  have hrightPoint : ∀ y ∈ Ι x 1,
      ‖E (y - x) * centeredP1 y‖ ≤ (1 / 1400 : ℝ) := by
    intro y hy
    rw [uIoc_of_le hx.2] at hy
    have hyIcc : y ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hx.1, hy.1], hy.2⟩
    have hlag : y - x ∈ Icc (0 : ℝ) 2 :=
      ⟨by linarith [hy.1], by linarith [hx.1, hy.2]⟩
    have hE := abs_fourCellEndpointSeedRegularKernelRemainder_le hlag
    have hp := abs_centeredP1_le_one hyIcc
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul hE hp (abs_nonneg _) (by norm_num)).trans_eq (by
      norm_num)
  have hleftPoint : ∀ y ∈ Ι (-1) x,
      ‖E (x - y) * centeredP1 y‖ ≤ (1 / 1400 : ℝ) := by
    intro y hy
    rw [uIoc_of_le hx.1] at hy
    have hyIcc : y ∈ Icc (-1 : ℝ) 1 :=
      ⟨hy.1.le, by linarith [hy.2, hx.2]⟩
    have hlag : x - y ∈ Icc (0 : ℝ) 2 :=
      ⟨by linarith [hy.2], by linarith [hy.1, hx.2]⟩
    have hE := abs_fourCellEndpointSeedRegularKernelRemainder_le hlag
    have hp := abs_centeredP1_le_one hyIcc
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul hE hp (abs_nonneg _) (by norm_num)).trans_eq (by
      norm_num)
  have hright := intervalIntegral.norm_integral_le_of_norm_le_const
    hrightPoint
  have hleft := intervalIntegral.norm_integral_le_of_norm_le_const
    hleftPoint
  have hright' :
      ‖factorTwoContinuousLagRightRepresenter E centeredP1 x‖ ≤
        (1 / 1400 : ℝ) * (1 - x) := by
    change ‖∫ y : ℝ in x..1, E (y - x) * centeredP1 y‖ ≤ _
    simpa only [abs_of_nonneg (sub_nonneg.mpr hx.2)] using hright
  have hleft' :
      ‖factorTwoContinuousLagLeftRepresenter E centeredP1 x‖ ≤
        (1 / 1400 : ℝ) * (x + 1) := by
    change ‖∫ y : ℝ in -1..x, E (x - y) * centeredP1 y‖ ≤ _
    rw [abs_of_nonneg (by linarith [hx.1])] at hleft
    simpa only [sub_neg_eq_add] using hleft
  unfold fourCellOddP11P1RegularRemainderRepresenter
    factorTwoContinuousLagK
  dsimp only [E] at hright' hleft' ⊢
  exact (norm_add_le _ _).trans (by linarith)

/-- Closed polynomial formula for the degree-four smooth-kernel model. -/
theorem fourCellOddP11P1RegularPolynomialRepresenter_eq (x : ℝ) :
    fourCellOddP11P1RegularPolynomialRepresenter x =
      7 * fourCellOperatorHalfWidth ^ 3 * x ^ 5 / 115200 +
      (-(5 * fourCellOperatorHalfWidth ^ 4 / 576) -
          7 * fourCellOperatorHalfWidth ^ 3 / 11520 -
          fourCellOperatorHalfWidth / 144) * x ^ 3 +
      (-(fourCellOperatorHalfWidth ^ 4 / 192) -
          7 * fourCellOperatorHalfWidth ^ 3 / 7680 +
          fourCellOperatorHalfWidth ^ 2 / 24 +
          fourCellOperatorHalfWidth / 48) * x := by
  let a := fourCellOperatorHalfWidth
  let r1 :=
    (75 * a ^ 4 * x ^ 4 - 14 * a ^ 3 * x ^ 3 -
      720 * a ^ 2 * x ^ 2 + 480 * a * x + 5760) / 23040
  let r2 :=
    -a * (50 * a ^ 3 * x ^ 3 - 7 * a ^ 2 * x ^ 2 -
      240 * a * x + 80) / 3840
  let r3 := a ^ 2 *
    (75 * a ^ 2 * x ^ 2 - 7 * a * x - 120) / 3840
  let r4 := -a ^ 3 * (150 * a * x - 7) / 11520
  let r5 := 5 * a ^ 4 / 1536
  let l1 :=
    (75 * a ^ 4 * x ^ 4 + 14 * a ^ 3 * x ^ 3 -
      720 * a ^ 2 * x ^ 2 - 480 * a * x + 5760) / 23040
  let l2 :=
    -a * (50 * a ^ 3 * x ^ 3 + 7 * a ^ 2 * x ^ 2 -
      240 * a * x - 80) / 3840
  let l3 := a ^ 2 *
    (75 * a ^ 2 * x ^ 2 + 7 * a * x - 120) / 3840
  let l4 := -a ^ 3 * (150 * a * x + 7) / 11520
  let l5 := 5 * a ^ 4 / 1536
  have hpoly (c1 c2 c3 c4 c5 l u : ℝ) :
      (∫ y : ℝ in l..u,
        c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4 + c5 * y ^ 5) =
        c1 * (u ^ 2 - l ^ 2) / 2 +
        c2 * (u ^ 3 - l ^ 3) / 3 +
        c3 * (u ^ 4 - l ^ 4) / 4 +
        c4 * (u ^ 5 - l ^ 5) / 5 +
        c5 * (u ^ 6 - l ^ 6) / 6 := by
    repeat rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    repeat rw [intervalIntegral.integral_const_mul]
    rw [integral_id]
    repeat rw [integral_pow]
    ring
  have hright :
      (∫ y : ℝ in x..1,
        fourCellRegularKernelPolynomial4 (a * (y - x)) * centeredP1 y) =
      r1 * (1 ^ 2 - x ^ 2) / 2 +
        r2 * (1 ^ 3 - x ^ 3) / 3 +
        r3 * (1 ^ 4 - x ^ 4) / 4 +
        r4 * (1 ^ 5 - x ^ 5) / 5 +
        r5 * (1 ^ 6 - x ^ 6) / 6 := by
    rw [show (fun y : ℝ ↦
        fourCellRegularKernelPolynomial4 (a * (y - x)) * centeredP1 y) =
      fun y ↦ r1 * y + r2 * y ^ 2 + r3 * y ^ 3 + r4 * y ^ 4 +
        r5 * y ^ 5 by
      funext y
      unfold fourCellRegularKernelPolynomial4 centeredP1
      dsimp only [r1, r2, r3, r4, r5]
      ring]
    exact hpoly r1 r2 r3 r4 r5 x 1
  have hleft :
      (∫ y : ℝ in -1..x,
        fourCellRegularKernelPolynomial4 (a * (x - y)) * centeredP1 y) =
      l1 * (x ^ 2 - (-1) ^ 2) / 2 +
        l2 * (x ^ 3 - (-1) ^ 3) / 3 +
        l3 * (x ^ 4 - (-1) ^ 4) / 4 +
        l4 * (x ^ 5 - (-1) ^ 5) / 5 +
        l5 * (x ^ 6 - (-1) ^ 6) / 6 := by
    rw [show (fun y : ℝ ↦
        fourCellRegularKernelPolynomial4 (a * (x - y)) * centeredP1 y) =
      fun y ↦ l1 * y + l2 * y ^ 2 + l3 * y ^ 3 + l4 * y ^ 4 +
        l5 * y ^ 5 by
      funext y
      unfold fourCellRegularKernelPolynomial4 centeredP1
      dsimp only [l1, l2, l3, l4, l5]
      ring]
    exact hpoly l1 l2 l3 l4 l5 (-1) x
  unfold fourCellOddP11P1RegularPolynomialRepresenter
    factorTwoContinuousLagK factorTwoContinuousLagRightRepresenter
    factorTwoContinuousLagLeftRepresenter
  change
    (∫ y : ℝ in x..1,
        fourCellRegularKernelPolynomial4 (a * (y - x)) * centeredP1 y) +
      (∫ y : ℝ in -1..x,
        fourCellRegularKernelPolynomial4 (a * (x - y)) * centeredP1 y) = _
  rw [hright, hleft]
  dsimp only [a, r1, r2, r3, r4, r5, l1, l2, l3, l4, l5]
  ring

theorem odd_fourCellOddP11P1RegularRepresenter :
    Function.Odd fourCellOddP11P1RegularRepresenter := by
  have hp :
      fourCellOddOneThreeFiveSevenNineLowProfile 1 0 0 0 0 = centeredP1 := by
    funext x
    unfold fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  unfold fourCellOddP11P1RegularRepresenter
    fourCellOddFiveModeRegularRepresenter
  rw [hp]
  exact odd_factorTwoContinuousLagK_of_odd _ centeredP1 (by
    intro x
    unfold centeredP1
    ring)

private theorem fourCellRegularLag_abs_le_quarter_local
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    |yoshidaRegularKernel (fourCellOperatorHalfWidth * t)| ≤ 1 / 4 := by
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
    mul_nonneg ha0 ht.1
  have harg4 : fourCellOperatorHalfWidth * t ≤
      5 * Real.log 2 / 4 := by
    calc
      fourCellOperatorHalfWidth * t ≤ fourCellOperatorHalfWidth * 2 :=
        mul_le_mul_of_nonneg_left ht.2 ha0
      _ = 5 * Real.log 2 / 4 := by
        unfold fourCellOperatorHalfWidth
        ring
  have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg4
  rw [abs_of_nonneg hk0]
  exact yoshidaRegularKernel_le_quarter harg0

private theorem intervalIntegrable_mul_P1RegularRepresenter
    (u : ℝ → ℝ) (hu : Continuous u) :
    IntervalIntegrable
      (fun x : ℝ ↦ u x * fourCellOddP11P1RegularRepresenter x)
      volume (-1) 1 := by
  let q : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t)
  let p : ℝ → ℝ :=
    fourCellOddOneThreeFiveSevenNineLowProfile 1 0 0 0 0
  have hq : Measurable q := by
    dsimp only [q]
    exact measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)
  have hp : Continuous p := by
    dsimp only [p]
    exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
      1 0 0 0 0).continuous
  have hqbound : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ 1 / 4 := by
    intro t ht
    simpa only [q] using fourCellRegularLag_abs_le_quarter_local t ht
  have hright :=
    intervalIntegrable_mul_factorTwoContinuousLagRightRepresenter_of_bounded
      q p u hq hp hu (1 / 4) hqbound
  have hleft :=
    intervalIntegrable_mul_factorTwoContinuousLagLeftRepresenter_of_bounded
      q u p hq hu hp (1 / 4) hqbound
  change IntervalIntegrable
    (fun x : ℝ ↦ u x * factorTwoContinuousLagK q p x)
      volume (-1) 1
  unfold factorTwoContinuousLagK
  rw [show (fun x : ℝ ↦ u x *
      (factorTwoContinuousLagRightRepresenter q p x +
        factorTwoContinuousLagLeftRepresenter q p x)) =
      fun x ↦
        u x * factorTwoContinuousLagRightRepresenter q p x +
          u x * factorTwoContinuousLagLeftRepresenter q p x by
    funext x
    ring]
  exact hright.add hleft

theorem integral_P1RegularRepresenter_fold
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r) :
    (∫ x : ℝ in -1..1,
        r x * fourCellOddP11P1RegularRepresenter x) =
      2 * ∫ x : ℝ in 0..1,
        r x * fourCellOddP11P1RegularRepresenter x := by
  have heven : Function.Even (fun x : ℝ ↦
      r x * fourCellOddP11P1RegularRepresenter x) := by
    intro x
    change r (-x) * fourCellOddP11P1RegularRepresenter (-x) =
      r x * fourCellOddP11P1RegularRepresenter x
    rw [hodd x, odd_fourCellOddP11P1RegularRepresenter x]
    ring
  exact integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ r x * fourCellOddP11P1RegularRepresenter x)
    (intervalIntegrable_mul_P1RegularRepresenter r hr) heven

/-- The exact degree-one row on the lower positive-half strip. -/
def fourCellOddP11P1LowerRepresenter (x : ℝ) : ℝ :=
  (93 / 50 : ℝ) * yoshidaEndpointPotential x * x -
    2 * fourCellOperatorHalfWidth * fourCellOddP11P1RegularRepresenter x

/-- The exact degree-one row on the upper endpoint strip. -/
def fourCellOddP11P1UpperRepresenter (x : ℝ) : ℝ :=
  Real.sqrt 2 * Real.log 2 * (8 / 5 - x) +
    fourCellOddP11P1LowerRepresenter x

/-- A simple rational selector near the numerical weighted projection of
the pure row.  Its cost has a wide margin below the `P₁` pivot. -/
def fourCellOddP11P1Selector : ℝ → ℝ :=
  fourCellOddOneThreeFiveSevenNineLowProfile
    2 (3 / 2) (1 / 5) (3 / 4) (7 / 10)

private theorem intervalIntegrable_zero_one_endpointPotential_mul_x_mul
    (u : ℝ → ℝ) (hu : Continuous u) :
    IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x * u x)
      volume 0 1 := by
  have hfull := intervalIntegrable_endpointPotential_mul
    (fun x : ℝ ↦ x * u x) (continuous_id.mul hu)
  have hsub : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * (x * u x))
      volume 0 1 := by
    apply hfull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  simpa only [mul_assoc] using hsub

/-- Exact positive-half normal form of the pure `P₁` tail row. -/
theorem fourCellOddCoreLocalBilinear_P1_P11Plus_eq_twoStripRepresenter
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    fourCellOddCoreLocalBilinear centeredP1 r =
      (∫ x : ℝ in 0..3 / 5,
        fourCellOddP11P1LowerRepresenter x * r x) +
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddP11P1UpperRepresenter x * r x := by
  let P : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * x * r x
  let R : ℝ → ℝ := fun x ↦
    r x * fourCellOddP11P1RegularRepresenter x
  have hP : IntervalIntegrable P volume 0 1 := by
    dsimp only [P]
    exact intervalIntegrable_zero_one_endpointPotential_mul_x_mul
      r hr.continuous
  have hRfull : IntervalIntegrable R volume (-1) 1 := by
    dsimp only [R]
    exact intervalIntegrable_mul_P1RegularRepresenter r hr.continuous
  have hPL : IntervalIntegrable P volume 0 (3 / 5) := by
    apply hP.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hPU : IntervalIntegrable P volume (3 / 5) 1 := by
    apply hP.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hR : IntervalIntegrable R volume 0 1 := by
    apply hRfull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hRL : IntervalIntegrable R volume 0 (3 / 5) := by
    apply hR.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hRU : IntervalIntegrable R volume (3 / 5) 1 := by
    apply hR.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hPSplit := intervalIntegral.integral_add_adjacent_intervals hPL hPU
  have hRSplit := intervalIntegral.integral_add_adjacent_intervals hRL hRU
  have hE : IntervalIntegrable (fun x : ℝ ↦
      Real.sqrt 2 * Real.log 2 * ((8 / 5 - x) * r x))
      volume (3 / 5) 1 := by
    exact (continuous_const.mul
      ((continuous_const.sub continuous_id).mul hr.continuous))
        |>.intervalIntegrable _ _
  have hRFold := integral_P1RegularRepresenter_fold r hr.continuous hodd
  have hrow :=
    fourCellOddCoreLocalBilinear_P1_P11Plus_eq_affineEndpointRepresenter
      r hr hodd h1 h3 h5 h7 h9
  change fourCellOddCoreLocalBilinear centeredP1 r =
      Real.sqrt 2 * Real.log 2 *
          (∫ x : ℝ in 3 / 5..1, (8 / 5 - x) * r x) +
        (93 / 50 : ℝ) * (∫ x : ℝ in 0..1, P x) -
        fourCellOperatorHalfWidth * (∫ x : ℝ in -1..1, R x)
    at hrow
  rw [← hPSplit, hRFold, ← hRSplit] at hrow
  rw [show (fun x : ℝ ↦
      fourCellOddP11P1LowerRepresenter x * r x) = fun x ↦
        (93 / 50 : ℝ) * P x -
          2 * fourCellOperatorHalfWidth * R x by
      funext x
      dsimp only [P, R]
      unfold fourCellOddP11P1LowerRepresenter
      ring,
    show (fun x : ℝ ↦
      fourCellOddP11P1UpperRepresenter x * r x) = fun x ↦
        Real.sqrt 2 * Real.log 2 * ((8 / 5 - x) * r x) +
          ((93 / 50 : ℝ) * P x -
            2 * fourCellOperatorHalfWidth * R x) by
      funext x
      dsimp only [P, R]
      unfold fourCellOddP11P1UpperRepresenter
        fourCellOddP11P1LowerRepresenter
      ring,
    intervalIntegral.integral_sub (hPL.const_mul _)
      (hRL.const_mul _),
    intervalIntegral.integral_add hE
      ((hPU.const_mul _).sub (hRU.const_mul _)),
    intervalIntegral.integral_sub (hPU.const_mul _)
      (hRU.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [hrow]
  ring

def fourCellOddP11P1LowerSelectorResidual (x : ℝ) : ℝ :=
  fourCellOddP11P1LowerRepresenter x - fourCellOddP11P1Selector x

def fourCellOddP11P1UpperSelectorResidual (x : ℝ) : ℝ :=
  fourCellOddP11P1UpperRepresenter x - fourCellOddP11P1Selector x

/-! ## Rational reciprocal certificate for the selector cost -/

/-- A rational center for the four-cell halfwidth. -/
private def fourCellOddP11P1RationalHalfWidth : ℝ := 433217 / 1000000

/-- A rational center for `sqrt 2 * log 2`. -/
private def fourCellOddP11P1RationalEndpointScale : ℝ := 980259 / 1000000

/-- The rational degree-five model obtained from the exact polynomial lag
formula by replacing the halfwidth with its certified rational center. -/
private def fourCellOddP11P1RationalRegularRepresenter (x : ℝ) : ℝ :=
  let a := fourCellOddP11P1RationalHalfWidth
  7 * a ^ 3 * x ^ 5 / 115200 +
    (-(5 * a ^ 4 / 576) - 7 * a ^ 3 / 11520 - a / 144) * x ^ 3 +
    (-(a ^ 4 / 192) - 7 * a ^ 3 / 7680 + a ^ 2 / 24 + a / 48) * x

private def fourCellOddP11P1RationalLowerH (x : ℝ) : ℝ :=
  -2 * fourCellOddP11P1RationalHalfWidth *
      fourCellOddP11P1RationalRegularRepresenter x -
    fourCellOddP11P1Selector x - (27 / 250) * x

private def fourCellOddP11P1RationalUpperH (x : ℝ) : ℝ :=
  fourCellOddP11P1RationalEndpointScale * (8 / 5 - x) -
    2 * fourCellOddP11P1RationalHalfWidth *
      fourCellOddP11P1RationalRegularRepresenter x -
    fourCellOddP11P1Selector x - (6 / 5 - (57 / 25) * x)

private def fourCellOddP11P1HexLowerWeight (x : ℝ) : ℝ :=
  (27 / 250 : ℝ) + (93 / 50) * yoshidaEndpointHexadecic x

/-- `x` times the upper hexadecic weight, written without division. -/
private def fourCellOddP11P1HexUpperDensity (x : ℝ) : ℝ :=
  (93 / 50 : ℝ) * x * yoshidaEndpointHexadecic x +
    6 / 5 - (57 / 25) * x

private def bernsteinAtom (n k : ℕ) (t : ℝ) : ℝ :=
  (Nat.choose n k : ℝ) * t ^ k * (1 - t) ^ (n - k)

private def fourCellOddP11P1LowerReciprocalCoeff : ℕ → ℝ
  | 0 => 4645237 / 500000
  | 1 => 1842383 / 200000
  | 2 => 4355817 / 500000
  | 3 => 1805413 / 250000
  | 4 => 1488669 / 250000
  | 5 => 122123 / 25000
  | 6 => 2010147 / 500000
  | 7 => 3322669 / 1000000
  | 8 => 1378727 / 500000
  | 9 => 1147639 / 500000
  | 10 => 1912931 / 1000000
  | _ => 0

private def fourCellOddP11P1UpperReciprocalCoeff : ℕ → ℝ
  | 0 => 3085951 / 250000
  | 1 => 17334703 / 1000000
  | 2 => 8175499 / 100000
  | 3 => -(4322409 / 1000000)
  | 4 => 3073283 / 250000
  | 5 => 2188457 / 500000
  | 6 => 3175221 / 1000000
  | 7 => 414493 / 200000
  | 8 => 352823 / 250000
  | 9 => 19611 / 20000
  | 10 => 138359 / 200000
  | _ => 0

private def fourCellOddP11P1LowerReciprocalMajorant (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 11,
    fourCellOddP11P1LowerReciprocalCoeff k * bernsteinAtom 10 k t

private def fourCellOddP11P1UpperReciprocalMajorant (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 11,
    fourCellOddP11P1UpperReciprocalCoeff k * bernsteinAtom 10 k t

private def fourCellOddP11P1LowerReciprocalRemainderCoeff : ℕ → ℝ
  | 0 => 15301287813334960937500000
  | 1 => 490067207023925781250000
  | 2 => 494749542924355468750000
  | 3 => 2006030128789924316406250
  | 4 => 2216826051310408398437500
  | 5 => 1574735981749461425781250
  | 6 => 901533507072946210937500
  | 7 => 589004606202845136718750
  | 8 => 622386791414461209062500
  | 9 => 813445209195795816718750
  | 10 => 988507394523133748462500
  | 11 => 1068380451369202504946875
  | 12 => 1062490433267932701282250
  | 13 => 1023650564979912971583625
  | 14 => 1002821834284107280382005
  | 15 => 1024711572186278309006575
  | 16 => 1086890582576428512159454
  | 17 => 1173332958072259601502655
  | 18 => 1269696194254556317075192
  | 19 => 1371037018596121370456098
  | 20 => 1479883015165420364255620
  | 21 => 1599487124362520038661680
  | 22 => 1729925291820114582135712
  | 23 => 1870699716585813102466543
  | 24 => 2024657925932286429172234
  | 25 => 2191804859749081270601050
  | 26 => 2374125281350933156388485
  | _ => 0

private def fourCellOddP11P1UpperReciprocalRemainderCoeff : ℕ → ℝ
  | 0 => 49650744012255389165387940
  | 1 => 42206949003534362123698050
  | 2 => 362117671791821137343142354000
  | 3 => 482174539442302518422454363894
  | 4 => 373777256624170811200219655664
  | 5 => 193513953777846174566443878396
  | 6 => 56617916369710944458080745595
  | 7 => 21776136983480303846429875
  | 8 => 5602105360475649219441026972
  | 9 => 35689393047853587823042109940
  | 10 => 59141097208684848013022342445
  | 11 => 62308711294976716468600812825
  | 12 => 47679044313186059712844578750
  | 13 => 26119097435655077319209315000
  | 14 => 8448444727856819426757445000
  | 15 => 97487643971345944190531250
  | 16 => 120527438442695700543187500
  | 17 => 3695675163267309157091093750
  | 18 => 5984232993623449681136718750
  | 19 => 5037978230170140910734375000
  | 20 => 2248324756774922278710937500
  | 21 => 315943443774655219335937500
  | 22 => 377475253625086297119140625
  | 23 => 964562019427415704345703125
  | 24 => 534031340603198657226562500
  | 25 => 633185704354266357421875000
  | 26 => 749728653249822235107421875
  | 27 => 886873851295635223388671875
  | _ => 0

private def fourCellOddP11P1LowerReciprocalRemainder (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 27,
    fourCellOddP11P1LowerReciprocalRemainderCoeff k * bernsteinAtom 26 k t

private def fourCellOddP11P1UpperReciprocalRemainder (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 28,
    fourCellOddP11P1UpperReciprocalRemainderCoeff k * bernsteinAtom 27 k t

private theorem fourCellOddP11P1LowerReciprocalRemainder_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ fourCellOddP11P1LowerReciprocalRemainder t := by
  have hc : ∀ k ∈ Finset.range 27,
      0 ≤ fourCellOddP11P1LowerReciprocalRemainderCoeff k := by
    intro k hk
    simp only [Finset.mem_range] at hk
    interval_cases k <;>
      norm_num [fourCellOddP11P1LowerReciprocalRemainderCoeff]
  unfold fourCellOddP11P1LowerReciprocalRemainder
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (hc k hk) (by
    unfold bernsteinAtom
    have hcomp : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    positivity)

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem one_le_fourCellOddP11P1LowerReciprocalCertificate
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 ≤ fourCellOddP11P1LowerReciprocalMajorant t *
      fourCellOddP11P1HexLowerWeight (3 * t / 5) := by
  have hrem := fourCellOddP11P1LowerReciprocalRemainder_nonneg ht0 ht1
  have hfactor :
      (4538836059570312500000000000 : ℝ) *
          (fourCellOddP11P1LowerReciprocalMajorant t *
              fourCellOddP11P1HexLowerWeight (3 * t / 5) - 1) =
        fourCellOddP11P1LowerReciprocalRemainder t := by
    unfold fourCellOddP11P1LowerReciprocalMajorant
      fourCellOddP11P1HexLowerWeight yoshidaEndpointHexadecic
      fourCellOddP11P1LowerReciprocalRemainder bernsteinAtom
    norm_num [Finset.sum_range_succ, Nat.choose,
      fourCellOddP11P1LowerReciprocalCoeff,
      fourCellOddP11P1LowerReciprocalRemainderCoeff]
    ring
  nlinarith

private theorem fourCellOddP11P1UpperReciprocalRemainder_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ fourCellOddP11P1UpperReciprocalRemainder t := by
  have hc : ∀ k ∈ Finset.range 28,
      0 ≤ fourCellOddP11P1UpperReciprocalRemainderCoeff k := by
    intro k hk
    simp only [Finset.mem_range] at hk
    interval_cases k <;>
      norm_num [fourCellOddP11P1UpperReciprocalRemainderCoeff]
  unfold fourCellOddP11P1UpperReciprocalRemainder
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (hc k hk) (by
    unfold bernsteinAtom
    have hcomp : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    positivity)

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem one_le_fourCellOddP11P1UpperReciprocalCertificate
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 ≤ fourCellOddP11P1UpperReciprocalMajorant t *
      fourCellOddP11P1HexUpperDensity ((3 + 2 * t) / 5) := by
  have hrem := fourCellOddP11P1UpperReciprocalRemainder_nonneg ht0 ht1
  have hfactor :
      (612742868041992187500000000000 : ℝ) *
          (fourCellOddP11P1UpperReciprocalMajorant t *
              fourCellOddP11P1HexUpperDensity ((3 + 2 * t) / 5) - 1) =
        fourCellOddP11P1UpperReciprocalRemainder t := by
    unfold fourCellOddP11P1UpperReciprocalMajorant
      fourCellOddP11P1HexUpperDensity yoshidaEndpointHexadecic
      fourCellOddP11P1UpperReciprocalRemainder bernsteinAtom
    norm_num [Finset.sum_range_succ, Nat.choose,
      fourCellOddP11P1UpperReciprocalCoeff,
      fourCellOddP11P1UpperReciprocalRemainderCoeff]
    ring
  nlinarith

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem fourCellOddP11P1RationalH_reciprocal_cost_lt :
    (∫ x : ℝ in 0..3 / 5,
        fourCellOddP11P1RationalLowerH x ^ 2 *
          fourCellOddP11P1LowerReciprocalMajorant (5 * x / 3)) +
      (∫ x : ℝ in 3 / 5..1,
        x * fourCellOddP11P1RationalUpperH x ^ 2 *
          fourCellOddP11P1UpperReciprocalMajorant ((5 * x - 3) / 2)) <
    (23 / 50 : ℝ) := by
  unfold fourCellOddP11P1RationalLowerH
    fourCellOddP11P1RationalUpperH
    fourCellOddP11P1RationalRegularRepresenter
    fourCellOddP11P1RationalHalfWidth
    fourCellOddP11P1RationalEndpointScale fourCellOddP11P1Selector
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
    fourCellOddP11P1LowerReciprocalMajorant
    fourCellOddP11P1UpperReciprocalMajorant bernsteinAtom
  simp_rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fourCellOddP11P1LowerReciprocalCoeff,
    fourCellOddP11P1UpperReciprocalCoeff]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  norm_num

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
private theorem fourCellOddP11P1Reciprocal_majorant_mass_lt :
    (∫ x : ℝ in 0..3 / 5,
        fourCellOddP11P1LowerReciprocalMajorant (5 * x / 3)) +
      (∫ x : ℝ in 3 / 5..1,
        x * fourCellOddP11P1UpperReciprocalMajorant ((5 * x - 3) / 2)) <
    (7 : ℝ) := by
  unfold fourCellOddP11P1LowerReciprocalMajorant
    fourCellOddP11P1UpperReciprocalMajorant bernsteinAtom
  norm_num [Finset.sum_range_succ, Nat.choose,
    fourCellOddP11P1LowerReciprocalCoeff,
    fourCellOddP11P1UpperReciprocalCoeff]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  norm_num

/-- Exact scalar cost of the concrete degree-`< 11` selector. -/
def fourCellOddP11P1SelectorDual : ℝ :=
  (∫ x : ℝ in 0..3 / 5,
      fourCellOddP11P1LowerSelectorResidual x ^ 2 /
        fourCellOddP11SelectorLowerWeight x) +
    ∫ x : ℝ in 3 / 5..1,
      fourCellOddP11P1UpperSelectorResidual x ^ 2 /
        fourCellOddP11SelectorUpperWeight x

/-- The five tail moment equations remove the concrete selector exactly,
leaving only its two weighted residuals. -/
theorem fourCellOddCoreLocalBilinear_P1_P11Plus_eq_selectorResiduals
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    fourCellOddCoreLocalBilinear centeredP1 r =
      (∫ x : ℝ in 0..3 / 5,
        fourCellOddP11P1LowerSelectorResidual x * r x) +
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddP11P1UpperSelectorResidual x * r x := by
  have hselector :
      (∫ x : ℝ in 0..1, fourCellOddP11P1Selector x * r x) = 0 := by
    unfold fourCellOddP11P1Selector
    exact integral_zero_one_fiveMode_mul_P11Plus_eq_zero
      r hr.continuous hodd h1 h3 h5 h7 h9
        2 (3 / 2) (1 / 5) (3 / 4) (7 / 10)
  have hselectorInt : IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddP11P1Selector x * r x)
      volume 0 1 := by
    exact ((contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
      2 (3 / 2) (1 / 5) (3 / 4) (7 / 10)).continuous.mul
        hr.continuous).intervalIntegrable _ _
  have hselectorL : IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddP11P1Selector x * r x)
      volume 0 (3 / 5) := by
    apply hselectorInt.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hselectorU : IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddP11P1Selector x * r x)
      volume (3 / 5) 1 := by
    apply hselectorInt.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hselectorSplit :=
    intervalIntegral.integral_add_adjacent_intervals hselectorL hselectorU
  rw [hselector] at hselectorSplit
  have hrow :=
    fourCellOddCoreLocalBilinear_P1_P11Plus_eq_twoStripRepresenter
      r hr hodd h1 h3 h5 h7 h9
  rw [show (fun x : ℝ ↦
      fourCellOddP11P1LowerSelectorResidual x * r x) = fun x ↦
        fourCellOddP11P1LowerRepresenter x * r x -
          fourCellOddP11P1Selector x * r x by
      funext x
      unfold fourCellOddP11P1LowerSelectorResidual
      ring,
    show (fun x : ℝ ↦
      fourCellOddP11P1UpperSelectorResidual x * r x) = fun x ↦
        fourCellOddP11P1UpperRepresenter x * r x -
          fourCellOddP11P1Selector x * r x by
      funext x
      unfold fourCellOddP11P1UpperSelectorResidual
      ring]
  have hLowerRep : IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddP11P1LowerRepresenter x * r x)
      volume 0 (3 / 5) := by
    let P : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * x * r x
    let R : ℝ → ℝ := fun x ↦
      r x * fourCellOddP11P1RegularRepresenter x
    have hP : IntervalIntegrable P volume 0 1 := by
      dsimp only [P]
      exact intervalIntegrable_zero_one_endpointPotential_mul_x_mul
        r hr.continuous
    have hPL : IntervalIntegrable P volume 0 (3 / 5) := by
      apply hP.mono_set
      intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact ⟨hx.1, by linarith [hx.2]⟩
    have hRfull : IntervalIntegrable R volume (-1) 1 := by
      dsimp only [R]
      exact intervalIntegrable_mul_P1RegularRepresenter r hr.continuous
    have hRL : IntervalIntegrable R volume 0 (3 / 5) := by
      apply hRfull.mono_set
      intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [show (fun x : ℝ ↦
        fourCellOddP11P1LowerRepresenter x * r x) = fun x ↦
          (93 / 50 : ℝ) * P x -
            2 * fourCellOperatorHalfWidth * R x by
      funext x
      dsimp only [P, R]
      unfold fourCellOddP11P1LowerRepresenter
      ring]
    exact (hPL.const_mul _).sub (hRL.const_mul _)
  have hUpperRep : IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddP11P1UpperRepresenter x * r x)
      volume (3 / 5) 1 := by
    have hE : IntervalIntegrable (fun x : ℝ ↦
        Real.sqrt 2 * Real.log 2 * ((8 / 5 - x) * r x))
        volume (3 / 5) 1 := by
      exact (continuous_const.mul
        ((continuous_const.sub continuous_id).mul hr.continuous))
          |>.intervalIntegrable _ _
    have hrowRep := hrow
    -- Integrability follows from the same exact split used by `hrow`.
    have hLowerFull : IntervalIntegrable
        (fun x : ℝ ↦ fourCellOddP11P1LowerRepresenter x * r x)
        volume (3 / 5) 1 := by
      let P : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * x * r x
      let R : ℝ → ℝ := fun x ↦
        r x * fourCellOddP11P1RegularRepresenter x
      have hP : IntervalIntegrable P volume 0 1 := by
        dsimp only [P]
        exact intervalIntegrable_zero_one_endpointPotential_mul_x_mul
          r hr.continuous
      have hPU : IntervalIntegrable P volume (3 / 5) 1 := by
        apply hP.mono_set
        intro x hx
        rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact ⟨by linarith [hx.1], hx.2⟩
      have hRfull : IntervalIntegrable R volume (-1) 1 := by
        dsimp only [R]
        exact intervalIntegrable_mul_P1RegularRepresenter r hr.continuous
      have hRU : IntervalIntegrable R volume (3 / 5) 1 := by
        apply hRfull.mono_set
        intro x hx
        rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        exact ⟨by linarith [hx.1], hx.2⟩
      rw [show (fun x : ℝ ↦
          fourCellOddP11P1LowerRepresenter x * r x) = fun x ↦
            (93 / 50 : ℝ) * P x -
              2 * fourCellOperatorHalfWidth * R x by
        funext x
        dsimp only [P, R]
        unfold fourCellOddP11P1LowerRepresenter
        ring]
      exact (hPU.const_mul _).sub (hRU.const_mul _)
    rw [show (fun x : ℝ ↦
        fourCellOddP11P1UpperRepresenter x * r x) = fun x ↦
          Real.sqrt 2 * Real.log 2 * ((8 / 5 - x) * r x) +
            fourCellOddP11P1LowerRepresenter x * r x by
      funext x
      unfold fourCellOddP11P1UpperRepresenter
      ring]
    exact hE.add hLowerFull
  rw [intervalIntegral.integral_sub hLowerRep hselectorL,
    intervalIntegral.integral_sub hUpperRep hselectorU]
  rw [hrow]
  linarith

private theorem intervalIntegrable_P1_regularRemainder_right
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    IntervalIntegrable
      (fun y : ℝ ↦
        fourCellEndpointSeedRegularKernelRemainder (y - x) * centeredP1 y)
      volume x 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.2]
  let f : ℝ → ℝ := fun y ↦
    fourCellEndpointSeedRegularKernelRemainder (y - x) * centeredP1 y
  let g : ℝ → ℝ := fun _y ↦ (1 / 1400 : ℝ)
  have hgIcc : IntegrableOn g (Icc x 1) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact continuous_const.continuousOn
  have hg : Integrable g (volume.restrict (Ioc x 1)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc x 1)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact
      (measurable_fourCellEndpointSeedRegularKernelRemainder.comp
        (measurable_id.sub measurable_const)).mul (by
          unfold centeredP1
          fun_prop)
  have hfg : ∀ᵐ y : ℝ ∂(volume.restrict (Ioc x 1)),
      ‖f y‖ ≤ g y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hyIcc : y ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hx.1, hy.1], hy.2⟩
    have hlag : y - x ∈ Icc (0 : ℝ) 2 :=
      ⟨by linarith [hy.1], by linarith [hx.1, hy.2]⟩
    have hE := abs_fourCellEndpointSeedRegularKernelRemainder_le hlag
    have hp := abs_centeredP1_le_one hyIcc
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul hE hp (abs_nonneg _) (by norm_num)).trans_eq
      (by norm_num)
  exact Integrable.mono' hg hfmeas hfg

private theorem intervalIntegrable_P1_regularRemainder_left
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    IntervalIntegrable
      (fun y : ℝ ↦
        fourCellEndpointSeedRegularKernelRemainder (x - y) * centeredP1 y)
      volume (-1) x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1]
  let f : ℝ → ℝ := fun y ↦
    fourCellEndpointSeedRegularKernelRemainder (x - y) * centeredP1 y
  let g : ℝ → ℝ := fun _y ↦ (1 / 1400 : ℝ)
  have hgIcc : IntegrableOn g (Icc (-1) x) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact continuous_const.continuousOn
  have hg : Integrable g (volume.restrict (Ioc (-1) x)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (-1) x)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact
      (measurable_fourCellEndpointSeedRegularKernelRemainder.comp
        (measurable_const.sub measurable_id)).mul (by
          unfold centeredP1
          fun_prop)
  have hfg : ∀ᵐ y : ℝ ∂(volume.restrict (Ioc (-1) x)),
      ‖f y‖ ≤ g y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hyIcc : y ∈ Icc (-1 : ℝ) 1 :=
      ⟨hy.1.le, by linarith [hy.2, hx.2]⟩
    have hlag : x - y ∈ Icc (0 : ℝ) 2 :=
      ⟨by linarith [hy.2], by linarith [hy.1, hx.2]⟩
    have hE := abs_fourCellEndpointSeedRegularKernelRemainder_le hlag
    have hp := abs_centeredP1_le_one hyIcc
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul hE hp (abs_nonneg _) (by norm_num)).trans_eq
      (by norm_num)
  exact Integrable.mono' hg hfmeas hfg

/-- Exact analytic decomposition of the smooth `P₁` row on the physical
interval.  Thus every later rational approximation error separates into a
degree-five coefficient error and the already bounded kernel remainder. -/
theorem fourCellOddP11P1RegularRepresenter_eq_polynomial_add_remainder
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    fourCellOddP11P1RegularRepresenter x =
      fourCellOddP11P1RegularPolynomialRepresenter x +
        fourCellOddP11P1RegularRemainderRepresenter x := by
  let P : ℝ → ℝ := fun t ↦
    fourCellRegularKernelPolynomial4 (fourCellOperatorHalfWidth * t)
  have hp :
      fourCellOddOneThreeFiveSevenNineLowProfile 1 0 0 0 0 = centeredP1 := by
    funext y
    unfold fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  have hPRight : IntervalIntegrable
      (fun y : ℝ ↦ P (y - x) * centeredP1 y) volume x 1 := by
    dsimp only [P]
    unfold fourCellRegularKernelPolynomial4 centeredP1
    exact (by fun_prop : Continuous (fun y : ℝ ↦
      ((1 / 4 : ℝ) - fourCellOperatorHalfWidth * (y - x) / 48 -
          (fourCellOperatorHalfWidth * (y - x)) ^ 2 / 32 +
          7 * (fourCellOperatorHalfWidth * (y - x)) ^ 3 / 11520 +
          5 * (fourCellOperatorHalfWidth * (y - x)) ^ 4 / 1536) * y))
      |>.intervalIntegrable x 1
  have hPLeft : IntervalIntegrable
      (fun y : ℝ ↦ P (x - y) * centeredP1 y) volume (-1) x := by
    dsimp only [P]
    unfold fourCellRegularKernelPolynomial4 centeredP1
    exact (by fun_prop : Continuous (fun y : ℝ ↦
      ((1 / 4 : ℝ) - fourCellOperatorHalfWidth * (x - y) / 48 -
          (fourCellOperatorHalfWidth * (x - y)) ^ 2 / 32 +
          7 * (fourCellOperatorHalfWidth * (x - y)) ^ 3 / 11520 +
          5 * (fourCellOperatorHalfWidth * (x - y)) ^ 4 / 1536) * y))
      |>.intervalIntegrable (-1) x
  have hERight := intervalIntegrable_P1_regularRemainder_right hx
  have hELeft := intervalIntegrable_P1_regularRemainder_left hx
  have hright :
      factorTwoContinuousLagRightRepresenter
          (fun t : ℝ ↦ yoshidaRegularKernel
            (fourCellOperatorHalfWidth * t)) centeredP1 x =
        factorTwoContinuousLagRightRepresenter P centeredP1 x +
          factorTwoContinuousLagRightRepresenter
            fourCellEndpointSeedRegularKernelRemainder centeredP1 x := by
    unfold factorTwoContinuousLagRightRepresenter
    rw [← intervalIntegral.integral_add hPRight hERight]
    apply intervalIntegral.integral_congr
    intro y _hy
    dsimp only [P]
    unfold fourCellEndpointSeedRegularKernelRemainder
    ring
  have hleft :
      factorTwoContinuousLagLeftRepresenter
          (fun t : ℝ ↦ yoshidaRegularKernel
            (fourCellOperatorHalfWidth * t)) centeredP1 x =
        factorTwoContinuousLagLeftRepresenter P centeredP1 x +
          factorTwoContinuousLagLeftRepresenter
            fourCellEndpointSeedRegularKernelRemainder centeredP1 x := by
    unfold factorTwoContinuousLagLeftRepresenter
    rw [← intervalIntegral.integral_add hPLeft hELeft]
    apply intervalIntegral.integral_congr
    intro y _hy
    dsimp only [P]
    unfold fourCellEndpointSeedRegularKernelRemainder
    ring
  unfold fourCellOddP11P1RegularRepresenter
    fourCellOddFiveModeRegularRepresenter
  rw [hp]
  unfold fourCellOddP11P1RegularPolynomialRepresenter
    fourCellOddP11P1RegularRemainderRepresenter factorTwoContinuousLagK
  dsimp only [P] at hright hleft ⊢
  rw [hright, hleft]
  ring

private def fourCellOddP11P1PolynomialInteraction (a x : ℝ) : ℝ :=
  7 * a ^ 4 * x ^ 5 / 57600 +
    (-(5 * a ^ 5 / 288) - 7 * a ^ 4 / 5760 - a ^ 2 / 72) * x ^ 3 +
    (-(a ^ 5 / 96) - 7 * a ^ 4 / 3840 + a ^ 3 / 12 + a ^ 2 / 24) * x

private theorem fourCellOddP11P1PolynomialInteraction_lipschitz
    {a b x : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |fourCellOddP11P1PolynomialInteraction a x -
        fourCellOddP11P1PolynomialInteraction b x| ≤ |a - b| := by
  let S2 : ℝ := a + b
  let S3 : ℝ := a ^ 2 + a * b + b ^ 2
  let S4 : ℝ := a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3
  let S5 : ℝ :=
    a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4
  let Q : ℝ :=
    7 / 57600 * (S4 * x ^ 5) +
      (-(5 / 288) * (S5 * x ^ 3) -
        7 / 5760 * (S4 * x ^ 3) - 1 / 72 * (S2 * x ^ 3)) +
      (-(1 / 96) * (S5 * x) - 7 / 3840 * (S4 * x) +
        1 / 12 * (S3 * x) + 1 / 24 * (S2 * x))
  have hpowA (n : ℕ) : 0 ≤ a ^ n ∧ a ^ n ≤ 1 :=
    ⟨pow_nonneg ha0 n, pow_le_one₀ ha0 ha1⟩
  have hpowB (n : ℕ) : 0 ≤ b ^ n ∧ b ^ n ≤ 1 :=
    ⟨pow_nonneg hb0 n, pow_le_one₀ hb0 hb1⟩
  have hpowX (n : ℕ) : 0 ≤ x ^ n ∧ x ^ n ≤ 1 :=
    ⟨pow_nonneg hx0 n, pow_le_one₀ hx0 hx1⟩
  have hab (i j : ℕ) :
      0 ≤ a ^ i * b ^ j ∧ a ^ i * b ^ j ≤ 1 := by
    exact ⟨mul_nonneg (hpowA i).1 (hpowB j).1,
      mul_le_one₀ (hpowA i).2 (hpowB j).1 (hpowB j).2⟩
  have hS2 : 0 ≤ S2 ∧ S2 ≤ 2 := by
    dsimp only [S2]
    constructor <;> linarith
  have hS3 : 0 ≤ S3 ∧ S3 ≤ 3 := by
    dsimp only [S3]
    constructor
    · positivity
    · linarith [(hpowA 2).2, (hab 1 1).2, (hpowB 2).2]
  have hS4 : 0 ≤ S4 ∧ S4 ≤ 4 := by
    dsimp only [S4]
    constructor
    · positivity
    · linarith [(hpowA 3).2, (hab 2 1).2, (hab 1 2).2,
        (hpowB 3).2]
  have hS5 : 0 ≤ S5 ∧ S5 ≤ 5 := by
    dsimp only [S5]
    constructor
    · positivity
    · linarith [(hpowA 4).2, (hab 3 1).2, (hab 2 2).2,
        (hab 1 3).2, (hpowB 4).2]
  have hS4x5 : 0 ≤ S4 * x ^ 5 ∧ S4 * x ^ 5 ≤ 4 := by
    constructor
    · exact mul_nonneg hS4.1 (hpowX 5).1
    · exact (mul_le_mul hS4.2 (hpowX 5).2 (hpowX 5).1
        (by norm_num)).trans_eq (by norm_num)
  have hS5x3 : 0 ≤ S5 * x ^ 3 ∧ S5 * x ^ 3 ≤ 5 := by
    constructor
    · exact mul_nonneg hS5.1 (hpowX 3).1
    · exact (mul_le_mul hS5.2 (hpowX 3).2 (hpowX 3).1
        (by norm_num)).trans_eq (by norm_num)
  have hS4x3 : 0 ≤ S4 * x ^ 3 ∧ S4 * x ^ 3 ≤ 4 := by
    constructor
    · exact mul_nonneg hS4.1 (hpowX 3).1
    · exact (mul_le_mul hS4.2 (hpowX 3).2 (hpowX 3).1
        (by norm_num)).trans_eq (by norm_num)
  have hS2x3 : 0 ≤ S2 * x ^ 3 ∧ S2 * x ^ 3 ≤ 2 := by
    constructor
    · exact mul_nonneg hS2.1 (hpowX 3).1
    · exact (mul_le_mul hS2.2 (hpowX 3).2 (hpowX 3).1
        (by norm_num)).trans_eq (by norm_num)
  have hS5x : 0 ≤ S5 * x ∧ S5 * x ≤ 5 := by
    constructor
    · exact mul_nonneg hS5.1 hx0
    · exact (mul_le_mul hS5.2 hx1 hx0 (by norm_num)).trans_eq
        (by norm_num)
  have hS4x : 0 ≤ S4 * x ∧ S4 * x ≤ 4 := by
    constructor
    · exact mul_nonneg hS4.1 hx0
    · exact (mul_le_mul hS4.2 hx1 hx0 (by norm_num)).trans_eq
        (by norm_num)
  have hS3x : 0 ≤ S3 * x ∧ S3 * x ≤ 3 := by
    constructor
    · exact mul_nonneg hS3.1 hx0
    · exact (mul_le_mul hS3.2 hx1 hx0 (by norm_num)).trans_eq
        (by norm_num)
  have hS2x : 0 ≤ S2 * x ∧ S2 * x ≤ 2 := by
    constructor
    · exact mul_nonneg hS2.1 hx0
    · exact (mul_le_mul hS2.2 hx1 hx0 (by norm_num)).trans_eq
        (by norm_num)
  have hQ : |Q| ≤ 1 := by
    rw [abs_le]
    dsimp only [Q]
    constructor <;> nlinarith [hS4x5.1, hS4x5.2, hS5x3.1, hS5x3.2,
      hS4x3.1, hS4x3.2, hS2x3.1, hS2x3.2, hS5x.1, hS5x.2,
      hS4x.1, hS4x.2, hS3x.1, hS3x.2, hS2x.1, hS2x.2]
  have hfactor :
      fourCellOddP11P1PolynomialInteraction a x -
          fourCellOddP11P1PolynomialInteraction b x = (a - b) * Q := by
    unfold fourCellOddP11P1PolynomialInteraction
    dsimp only [Q, S2, S3, S4, S5]
    ring
  rw [hfactor, abs_mul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hQ (abs_nonneg (a - b))

private theorem abs_fourCellOperatorHalfWidth_sub_rational_lt :
    |fourCellOperatorHalfWidth - fourCellOddP11P1RationalHalfWidth| <
      (1 / 1000000 : ℝ) := by
  have hlog := YoshidaConstantBounds.strict_log_two_fine_bounds
  have hnonpos : fourCellOperatorHalfWidth -
      fourCellOddP11P1RationalHalfWidth ≤ 0 := by
    unfold fourCellOperatorHalfWidth fourCellOddP11P1RationalHalfWidth
    linarith [hlog.2]
  rw [abs_of_nonpos hnonpos]
  unfold fourCellOperatorHalfWidth fourCellOddP11P1RationalHalfWidth
  linarith [hlog.1]

private theorem sqrt_two_mul_log_two_P1_fine_bounds :
    (1414213562 / 1000000000 : ℝ) *
        (69314718055 / 100000000000 : ℝ) <
          Real.sqrt 2 * Real.log 2 ∧
      Real.sqrt 2 * Real.log 2 <
        (1414213563 / 1000000000 : ℝ) *
          (69314718057 / 100000000000 : ℝ) := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := by
    simpa only using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hslo : (1414213562 / 1000000000 : ℝ) < Real.sqrt 2 := by
    have hrat : (1414213562 / 1000000000 : ℝ) ^ 2 < 2 := by
      norm_num
    nlinarith
  have hshi : Real.sqrt 2 < (1414213563 / 1000000000 : ℝ) := by
    have hrat : (2 : ℝ) <
        (1414213563 / 1000000000 : ℝ) ^ 2 := by
      norm_num
    nlinarith
  have hlog := YoshidaConstantBounds.strict_log_two_fine_bounds
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · exact (mul_lt_mul_of_pos_right hslo (by norm_num)).trans
      (mul_lt_mul_of_pos_left hlog.1 hspos)
  · exact (mul_lt_mul_of_pos_right hshi hlogpos).trans
      (mul_lt_mul_of_pos_left hlog.2 (by norm_num))

private theorem abs_endpointScale_sub_rational_lt :
    |Real.sqrt 2 * Real.log 2 -
        fourCellOddP11P1RationalEndpointScale| < (1 / 1000000 : ℝ) := by
  have hs := sqrt_two_mul_log_two_P1_fine_bounds
  have hnonpos : Real.sqrt 2 * Real.log 2 -
      fourCellOddP11P1RationalEndpointScale ≤ 0 := by
    unfold fourCellOddP11P1RationalEndpointScale
    norm_num at hs ⊢
    linarith [hs.2]
  rw [abs_of_nonpos hnonpos]
  unfold fourCellOddP11P1RationalEndpointScale
  norm_num at hs ⊢
  linarith [hs.1]

private def fourCellOddP11P1ExactLowerH (x : ℝ) : ℝ :=
  -2 * fourCellOperatorHalfWidth * fourCellOddP11P1RegularRepresenter x -
    fourCellOddP11P1Selector x - (27 / 250) * x

private def fourCellOddP11P1ExactUpperH (x : ℝ) : ℝ :=
  Real.sqrt 2 * Real.log 2 * (8 / 5 - x) -
    2 * fourCellOperatorHalfWidth * fourCellOddP11P1RegularRepresenter x -
    fourCellOddP11P1Selector x - (6 / 5 - (57 / 25) * x)

private theorem fourCellOddP11P1LowerResidual_eq_weight_add_H (x : ℝ) :
    fourCellOddP11P1LowerSelectorResidual x =
      x * fourCellOddP11SelectorLowerWeight x +
        fourCellOddP11P1ExactLowerH x := by
  unfold fourCellOddP11P1LowerSelectorResidual
    fourCellOddP11P1LowerRepresenter
    fourCellOddP11SelectorLowerWeight fourCellOddP11P1ExactLowerH
  ring

private theorem fourCellOddP11P1UpperResidual_eq_weight_add_H
    {x : ℝ} (hx : x ≠ 0) :
    fourCellOddP11P1UpperSelectorResidual x =
      x * fourCellOddP11SelectorUpperWeight x +
        fourCellOddP11P1ExactUpperH x := by
  unfold fourCellOddP11P1UpperSelectorResidual
    fourCellOddP11P1UpperRepresenter fourCellOddP11P1LowerRepresenter
    fourCellOddP11SelectorUpperWeight fourCellOddP11P1ExactUpperH
  field_simp [hx]
  ring

private theorem abs_P1_polynomialInteraction_sub_rational_lt
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |2 * fourCellOperatorHalfWidth *
          fourCellOddP11P1RegularPolynomialRepresenter x -
        2 * fourCellOddP11P1RationalHalfWidth *
          fourCellOddP11P1RationalRegularRepresenter x| <
      (1 / 1000000 : ℝ) := by
  have hlog := YoshidaConstantBounds.strict_log_two_fine_bounds
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha1 : fourCellOperatorHalfWidth ≤ 1 := by
    unfold fourCellOperatorHalfWidth
    linarith [hlog.2]
  have hb0 : 0 ≤ fourCellOddP11P1RationalHalfWidth := by
    unfold fourCellOddP11P1RationalHalfWidth
    norm_num
  have hb1 : fourCellOddP11P1RationalHalfWidth ≤ 1 := by
    unfold fourCellOddP11P1RationalHalfWidth
    norm_num
  have hlip := fourCellOddP11P1PolynomialInteraction_lipschitz
    ha0 ha1 hb0 hb1 hx0 hx1
  have heq :
      2 * fourCellOperatorHalfWidth *
            fourCellOddP11P1RegularPolynomialRepresenter x -
          2 * fourCellOddP11P1RationalHalfWidth *
            fourCellOddP11P1RationalRegularRepresenter x =
        fourCellOddP11P1PolynomialInteraction fourCellOperatorHalfWidth x -
          fourCellOddP11P1PolynomialInteraction
            fourCellOddP11P1RationalHalfWidth x := by
    rw [fourCellOddP11P1RegularPolynomialRepresenter_eq]
    unfold fourCellOddP11P1RationalRegularRepresenter
      fourCellOddP11P1PolynomialInteraction
    ring
  rw [heq]
  exact hlip.trans_lt abs_fourCellOperatorHalfWidth_sub_rational_lt

private theorem abs_twoHalfWidth_mul_P1Remainder_le
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |2 * fourCellOperatorHalfWidth *
        fourCellOddP11P1RegularRemainderRepresenter x| ≤
      (1 / 700 : ℝ) := by
  have hlog := YoshidaConstantBounds.strict_log_two_fine_bounds
  have ha0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha1 : 2 * fourCellOperatorHalfWidth ≤ 1 := by
    unfold fourCellOperatorHalfWidth
    linarith [hlog.2]
  have hrem := norm_fourCellOddP11P1RegularRemainderRepresenter_le hx
  rw [Real.norm_eq_abs] at hrem
  rw [abs_mul, abs_of_nonneg ha0]
  calc
    2 * fourCellOperatorHalfWidth *
        |fourCellOddP11P1RegularRemainderRepresenter x| ≤
        1 * (1 / 700 : ℝ) :=
      mul_le_mul ha1 hrem (abs_nonneg _) (by norm_num)
    _ = _ := by ring

private theorem abs_fourCellOddP11P1ExactLowerH_sub_rational_lt
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |fourCellOddP11P1ExactLowerH x -
        fourCellOddP11P1RationalLowerH x| < (1 / 600 : ℝ) := by
  have hx : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, hx1⟩
  have hsplit :=
    fourCellOddP11P1RegularRepresenter_eq_polynomial_add_remainder hx
  have hpoly := abs_P1_polynomialInteraction_sub_rational_lt hx0 hx1
  have hrem := abs_twoHalfWidth_mul_P1Remainder_le hx
  have heq :
      fourCellOddP11P1ExactLowerH x -
          fourCellOddP11P1RationalLowerH x =
        -(2 * fourCellOperatorHalfWidth *
            fourCellOddP11P1RegularPolynomialRepresenter x -
          2 * fourCellOddP11P1RationalHalfWidth *
            fourCellOddP11P1RationalRegularRepresenter x) -
          2 * fourCellOperatorHalfWidth *
            fourCellOddP11P1RegularRemainderRepresenter x := by
    unfold fourCellOddP11P1ExactLowerH fourCellOddP11P1RationalLowerH
    rw [hsplit]
    ring
  rw [heq]
  calc
    |-(2 * fourCellOperatorHalfWidth *
          fourCellOddP11P1RegularPolynomialRepresenter x -
        2 * fourCellOddP11P1RationalHalfWidth *
          fourCellOddP11P1RationalRegularRepresenter x) -
        2 * fourCellOperatorHalfWidth *
          fourCellOddP11P1RegularRemainderRepresenter x| ≤
        |2 * fourCellOperatorHalfWidth *
            fourCellOddP11P1RegularPolynomialRepresenter x -
          2 * fourCellOddP11P1RationalHalfWidth *
            fourCellOddP11P1RationalRegularRepresenter x| +
          |2 * fourCellOperatorHalfWidth *
            fourCellOddP11P1RegularRemainderRepresenter x| := by
      simpa only [abs_neg] using abs_sub
        (-(2 * fourCellOperatorHalfWidth *
            fourCellOddP11P1RegularPolynomialRepresenter x -
          2 * fourCellOddP11P1RationalHalfWidth *
            fourCellOddP11P1RationalRegularRepresenter x))
        (2 * fourCellOperatorHalfWidth *
          fourCellOddP11P1RegularRemainderRepresenter x)
    _ < (1 / 1000000 : ℝ) + 1 / 700 :=
      add_lt_add_of_lt_of_le hpoly hrem
    _ < (1 / 600 : ℝ) := by norm_num

private theorem abs_fourCellOddP11P1ExactUpperH_sub_rational_lt
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |fourCellOddP11P1ExactUpperH x -
        fourCellOddP11P1RationalUpperH x| < (1 / 600 : ℝ) := by
  have hx : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, hx1⟩
  have hsplit :=
    fourCellOddP11P1RegularRepresenter_eq_polynomial_add_remainder hx
  have hpoly := abs_P1_polynomialInteraction_sub_rational_lt hx0 hx1
  have hrem := abs_twoHalfWidth_mul_P1Remainder_le hx
  have hscale := abs_endpointScale_sub_rational_lt
  have hfactor0 : 0 ≤ (8 / 5 : ℝ) - x := by linarith
  have hfactor1 : (8 / 5 : ℝ) - x ≤ 8 / 5 := by linarith
  have hendpoint :
      |(Real.sqrt 2 * Real.log 2 -
          fourCellOddP11P1RationalEndpointScale) * (8 / 5 - x)| <
        (8 / 5 : ℝ) * (1 / 1000000) := by
    rw [abs_mul, abs_of_nonneg hfactor0]
    calc
      |Real.sqrt 2 * Real.log 2 -
          fourCellOddP11P1RationalEndpointScale| * (8 / 5 - x) <
          (1 / 1000000 : ℝ) * (8 / 5 - x) :=
        mul_lt_mul_of_pos_right hscale (by linarith)
      _ ≤ (1 / 1000000 : ℝ) * (8 / 5) :=
        mul_le_mul_of_nonneg_left hfactor1 (by norm_num)
      _ = (8 / 5 : ℝ) * (1 / 1000000) := by ring
  have heq :
      fourCellOddP11P1ExactUpperH x -
          fourCellOddP11P1RationalUpperH x =
        (Real.sqrt 2 * Real.log 2 -
            fourCellOddP11P1RationalEndpointScale) * (8 / 5 - x) -
          (2 * fourCellOperatorHalfWidth *
              fourCellOddP11P1RegularPolynomialRepresenter x -
            2 * fourCellOddP11P1RationalHalfWidth *
              fourCellOddP11P1RationalRegularRepresenter x) -
          2 * fourCellOperatorHalfWidth *
            fourCellOddP11P1RegularRemainderRepresenter x := by
    unfold fourCellOddP11P1ExactUpperH fourCellOddP11P1RationalUpperH
    rw [hsplit]
    ring
  rw [heq]
  calc
    |(Real.sqrt 2 * Real.log 2 -
          fourCellOddP11P1RationalEndpointScale) * (8 / 5 - x) -
        (2 * fourCellOperatorHalfWidth *
            fourCellOddP11P1RegularPolynomialRepresenter x -
          2 * fourCellOddP11P1RationalHalfWidth *
            fourCellOddP11P1RationalRegularRepresenter x) -
        2 * fourCellOperatorHalfWidth *
          fourCellOddP11P1RegularRemainderRepresenter x| ≤
        |(Real.sqrt 2 * Real.log 2 -
            fourCellOddP11P1RationalEndpointScale) * (8 / 5 - x)| +
          |2 * fourCellOperatorHalfWidth *
              fourCellOddP11P1RegularPolynomialRepresenter x -
            2 * fourCellOddP11P1RationalHalfWidth *
              fourCellOddP11P1RationalRegularRepresenter x| +
          |2 * fourCellOperatorHalfWidth *
            fourCellOddP11P1RegularRemainderRepresenter x| := by
      calc
        |(Real.sqrt 2 * Real.log 2 -
              fourCellOddP11P1RationalEndpointScale) * (8 / 5 - x) -
            (2 * fourCellOperatorHalfWidth *
                fourCellOddP11P1RegularPolynomialRepresenter x -
              2 * fourCellOddP11P1RationalHalfWidth *
                fourCellOddP11P1RationalRegularRepresenter x) -
            2 * fourCellOperatorHalfWidth *
              fourCellOddP11P1RegularRemainderRepresenter x| ≤
            |(Real.sqrt 2 * Real.log 2 -
                fourCellOddP11P1RationalEndpointScale) * (8 / 5 - x) -
              (2 * fourCellOperatorHalfWidth *
                  fourCellOddP11P1RegularPolynomialRepresenter x -
                2 * fourCellOddP11P1RationalHalfWidth *
                  fourCellOddP11P1RationalRegularRepresenter x)| +
              |2 * fourCellOperatorHalfWidth *
                fourCellOddP11P1RegularRemainderRepresenter x| := abs_sub _ _
        _ ≤ (|(Real.sqrt 2 * Real.log 2 -
                fourCellOddP11P1RationalEndpointScale) * (8 / 5 - x)| +
              |2 * fourCellOperatorHalfWidth *
                  fourCellOddP11P1RegularPolynomialRepresenter x -
                2 * fourCellOddP11P1RationalHalfWidth *
                  fourCellOddP11P1RationalRegularRepresenter x|) +
              |2 * fourCellOperatorHalfWidth *
                fourCellOddP11P1RegularRemainderRepresenter x| :=
          add_le_add_left (abs_sub _ _) _
    _ < (8 / 5 : ℝ) * (1 / 1000000) + 1 / 1000000 + 1 / 700 := by
      linarith
    _ < (1 / 600 : ℝ) := by norm_num

private theorem one_div_lowerWeight_le_reciprocalMajorant
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 3 / 5) :
    1 / fourCellOddP11SelectorLowerWeight x ≤
      fourCellOddP11P1LowerReciprocalMajorant (5 * x / 3) := by
  let t : ℝ := 5 * x / 3
  have ht0 : 0 ≤ t := by dsimp only [t]; linarith
  have ht1 : t ≤ 1 := by dsimp only [t]; linarith
  have hcert := one_le_fourCellOddP11P1LowerReciprocalCertificate ht0 ht1
  have htx : 3 * t / 5 = x := by
    dsimp only [t]
    ring
  have hcertx :
      1 ≤ fourCellOddP11P1LowerReciprocalMajorant t *
        fourCellOddP11P1HexLowerWeight x := by
    rw [← htx]
    exact hcert
  have hhexpos : 0 < fourCellOddP11P1HexLowerWeight x := by
    unfold fourCellOddP11P1HexLowerWeight yoshidaEndpointHexadecic
    have hxpow (n : ℕ) : 0 ≤ x ^ n := pow_nonneg hx0 n
    positivity
  have hPpos : 0 < fourCellOddP11P1LowerReciprocalMajorant t := by
    by_contra hnot
    have hPnonpos : fourCellOddP11P1LowerReciprocalMajorant t ≤ 0 :=
      le_of_not_gt hnot
    have := mul_nonpos_of_nonpos_of_nonneg hPnonpos hhexpos.le
    linarith
  have hhexle : fourCellOddP11P1HexLowerWeight x ≤
      fourCellOddP11SelectorLowerWeight x := by
    have hV := hexadecic_le_endpointPotential (x := x) (by
      rw [abs_lt]
      constructor <;> linarith)
    unfold fourCellOddP11P1HexLowerWeight
      fourCellOddP11SelectorLowerWeight
    nlinarith
  have hprod : 1 ≤ fourCellOddP11P1LowerReciprocalMajorant t *
      fourCellOddP11SelectorLowerWeight x :=
    hcertx.trans (mul_le_mul_of_nonneg_left hhexle hPpos.le)
  have hWpos := fourCellOddP11SelectorLowerWeight_pos ⟨hx0, hx1⟩
  rw [div_le_iff₀ hWpos]
  simpa only [one_mul] using hprod

private theorem one_fiftieth_mul_x_le_hexUpperDensity
    {x : ℝ} (hx0 : (3 / 5 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    (1 / 50 : ℝ) * x ≤ fourCellOddP11P1HexUpperDensity x := by
  let t : ℝ := (5 * x - 3) / 2
  have ht0 : 0 ≤ t := by dsimp only [t]; linarith
  have ht1 : t ≤ 1 := by dsimp only [t]; linarith
  have hcomp : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  rw [← sub_nonneg]
  rw [show fourCellOddP11P1HexUpperDensity x - (1 / 50 : ℝ) * x =
      (53171469 / 781250000 : ℝ) * (1 - t) ^ 9 +
      (42090487 / 156250000 : ℝ) * t * (1 - t) ^ 8 +
      (1968121 / 7812500 : ℝ) * t ^ 2 * (1 - t) ^ 7 +
      (15799 / 62500 : ℝ) * t ^ 3 * (1 - t) ^ 6 +
      (1806347 / 625000 : ℝ) * t ^ 4 * (1 - t) ^ 5 +
      (1157849 / 125000 : ℝ) * t ^ 5 * (1 - t) ^ 4 +
      (172237 / 12500 : ℝ) * t ^ 6 * (1 - t) ^ 3 +
      (27683 / 2500 : ℝ) * t ^ 7 * (1 - t) ^ 2 +
      (9413 / 2000 : ℝ) * t ^ 8 * (1 - t) +
      (67 / 80 : ℝ) * t ^ 9 +
      (93 / 50 : ℝ) * x *
        (x ^ 10 / 10 + x ^ 12 / 12 + x ^ 14 / 14 + x ^ 16 / 16) by
    dsimp only [t]
    unfold fourCellOddP11P1HexUpperDensity yoshidaEndpointHexadecic
    ring]
  positivity

private theorem one_div_upperDensity_le_reciprocalMajorant
    {x : ℝ} (hx0 : (3 / 5 : ℝ) ≤ x) (hx1 : x < 1) :
    1 / (x * fourCellOddP11SelectorUpperWeight x) ≤
      fourCellOddP11P1UpperReciprocalMajorant ((5 * x - 3) / 2) := by
  let t : ℝ := (5 * x - 3) / 2
  have ht0 : 0 ≤ t := by dsimp only [t]; linarith
  have ht1 : t ≤ 1 := by dsimp only [t]; linarith
  have hxpos : 0 < x := by linarith
  have hcert := one_le_fourCellOddP11P1UpperReciprocalCertificate ht0 ht1
  have htx : (3 + 2 * t) / 5 = x := by
    dsimp only [t]
    ring
  have hcertx :
      1 ≤ fourCellOddP11P1UpperReciprocalMajorant t *
        fourCellOddP11P1HexUpperDensity x := by
    rw [← htx]
    exact hcert
  have hhexpos : 0 < fourCellOddP11P1HexUpperDensity x := by
    have hlow := one_fiftieth_mul_x_le_hexUpperDensity hx0 hx1.le
    nlinarith
  have hPpos : 0 < fourCellOddP11P1UpperReciprocalMajorant t := by
    by_contra hnot
    have hPnonpos : fourCellOddP11P1UpperReciprocalMajorant t ≤ 0 :=
      le_of_not_gt hnot
    have := mul_nonpos_of_nonpos_of_nonneg hPnonpos hhexpos.le
    linarith
  have hV := hexadecic_le_endpointPotential (x := x) (by
    rw [abs_lt]
    constructor <;> linarith)
  have hdensity : fourCellOddP11P1HexUpperDensity x ≤
      x * fourCellOddP11SelectorUpperWeight x := by
    unfold fourCellOddP11P1HexUpperDensity
      fourCellOddP11SelectorUpperWeight
    field_simp [hxpos.ne']
    nlinarith [mul_le_mul_of_nonneg_left hV
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 93 / 50) hxpos.le)]
  have hprod : 1 ≤ fourCellOddP11P1UpperReciprocalMajorant t *
      (x * fourCellOddP11SelectorUpperWeight x) :=
    hcertx.trans (mul_le_mul_of_nonneg_left hdensity hPpos.le)
  have hDpos : 0 < x * fourCellOddP11SelectorUpperWeight x :=
    lt_of_lt_of_le hhexpos hdensity
  rw [div_le_iff₀ hDpos]
  simpa only [one_mul] using hprod

private theorem fourCellOddP11P1Rational_base_lt :
    (∫ x : ℝ in 0..3 / 5,
        x ^ 2 * fourCellOddP11SelectorLowerWeight x +
          2 * x * fourCellOddP11P1RationalLowerH x) +
      (∫ x : ℝ in 3 / 5..1,
        x ^ 2 * fourCellOddP11SelectorUpperWeight x +
          2 * x * fourCellOddP11P1RationalUpperH x) <
    (-29 / 120 : ℝ) := by
  let V2 : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * x ^ 2
  let pL : ℝ → ℝ := fun x ↦
    (27 / 250 : ℝ) * x ^ 2 +
      2 * x * fourCellOddP11P1RationalLowerH x
  let pU : ℝ → ℝ := fun x ↦
    (6 / 5 : ℝ) * x - (57 / 25) * x ^ 2 +
      2 * x * fourCellOddP11P1RationalUpperH x
  have hV : IntervalIntegrable V2 volume 0 1 := by
    have h := intervalIntegrable_zero_one_endpointPotential_mul_x_mul
      (fun x : ℝ ↦ x) continuous_id
    apply h.congr
    intro x _hx
    dsimp only [V2]
    ring
  have hVL : IntervalIntegrable V2 volume 0 (3 / 5) := by
    apply hV.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hVU : IntervalIntegrable V2 volume (3 / 5) 1 := by
    apply hV.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hPL : IntervalIntegrable pL volume 0 (3 / 5) := by
    apply Continuous.intervalIntegrable
    dsimp only [pL]
    unfold fourCellOddP11P1RationalLowerH
      fourCellOddP11P1RationalRegularRepresenter
      fourCellOddP11P1Selector
      fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
      centeredP1 centeredP3 factorTwoCenteredP5
    simp_rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
    fun_prop
  have hPU : IntervalIntegrable pU volume (3 / 5) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [pU]
    unfold fourCellOddP11P1RationalUpperH
      fourCellOddP11P1RationalRegularRepresenter
      fourCellOddP11P1Selector
      fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
      centeredP1 centeredP3 factorTwoCenteredP5
    simp_rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
    fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hVL hVU
  have hpotential :=
    integral_zero_one_endpointPotential_oddStructuralLow 1 0
  unfold factorTwoOddStructuralLowProfile centeredP1 at hpotential
  norm_num at hpotential
  have hpotentialV :
      (∫ x : ℝ in 0..1, V2 x) =
        4 / 9 - (1 / 3 : ℝ) * Real.log 2 := by
    simpa only [V2] using hpotential
  rw [show (fun x : ℝ ↦
      x ^ 2 * fourCellOddP11SelectorLowerWeight x +
        2 * x * fourCellOddP11P1RationalLowerH x) = fun x ↦
      (93 / 50 : ℝ) * V2 x + pL x by
    funext x
    dsimp only [V2, pL]
    unfold fourCellOddP11SelectorLowerWeight
    ring,
    show (fun x : ℝ ↦
      x ^ 2 * fourCellOddP11SelectorUpperWeight x +
        2 * x * fourCellOddP11P1RationalUpperH x) = fun x ↦
      (93 / 50 : ℝ) * V2 x + pU x by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [V2, pU, fourCellOddP11SelectorUpperWeight]
    · dsimp only [V2, pU]
      unfold fourCellOddP11SelectorUpperWeight
      field_simp [hx]
      ring,
    intervalIntegral.integral_add (hVL.const_mul _) hPL,
    intervalIntegral.integral_add (hVU.const_mul _) hPU]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [show
      ((93 / 50 : ℝ) * (∫ x : ℝ in 0..3 / 5, V2 x) +
          (∫ x : ℝ in 0..3 / 5, pL x)) +
        ((93 / 50 : ℝ) * (∫ x : ℝ in 3 / 5..1, V2 x) +
          (∫ x : ℝ in 3 / 5..1, pU x)) =
        (93 / 50 : ℝ) *
            ((∫ x : ℝ in 0..3 / 5, V2 x) +
              (∫ x : ℝ in 3 / 5..1, V2 x)) +
          (∫ x : ℝ in 0..3 / 5, pL x) +
          (∫ x : ℝ in 3 / 5..1, pU x) by ring,
    hsplit, hpotentialV]
  unfold pL pU fourCellOddP11P1RationalLowerH
    fourCellOddP11P1RationalUpperH
    fourCellOddP11P1RationalRegularRepresenter
    fourCellOddP11P1RationalHalfWidth
    fourCellOddP11P1RationalEndpointScale fourCellOddP11P1Selector
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
  simp_rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  norm_num
  nlinarith [YoshidaConstantBounds.strict_log_two_fine_bounds.1,
    YoshidaConstantBounds.strict_log_two_fine_bounds.2]

private def fourCellOddP11P1LowerDualMajorant (x : ℝ) : ℝ :=
  x ^ 2 * fourCellOddP11SelectorLowerWeight x +
    2 * x * fourCellOddP11P1RationalLowerH x + 1 / 300 +
    (101 / 100) * fourCellOddP11P1RationalLowerH x ^ 2 *
      fourCellOddP11P1LowerReciprocalMajorant (5 * x / 3) +
    (101 / 360000) *
      fourCellOddP11P1LowerReciprocalMajorant (5 * x / 3)

private def fourCellOddP11P1UpperDualMajorant (x : ℝ) : ℝ :=
  x ^ 2 * fourCellOddP11SelectorUpperWeight x +
    2 * x * fourCellOddP11P1RationalUpperH x + 1 / 300 +
    (101 / 100) * x * fourCellOddP11P1RationalUpperH x ^ 2 *
      fourCellOddP11P1UpperReciprocalMajorant ((5 * x - 3) / 2) +
    (101 / 360000) * x *
      fourCellOddP11P1UpperReciprocalMajorant ((5 * x - 3) / 2)

private theorem sq_le_rational_transfer
    {h h₀ : ℝ} (herr : |h - h₀| ≤ (1 / 600 : ℝ)) :
    h ^ 2 ≤ (101 / 100 : ℝ) * h₀ ^ 2 + 101 / 360000 := by
  have hd0 : 0 ≤ |h - h₀| := abs_nonneg _
  have hdsq : (h - h₀) ^ 2 ≤ (1 / 600 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (|h - h₀| - 1 / 600), sq_abs (h - h₀)]
  have hsquare := sq_nonneg (h₀ / 10 - 10 * (h - h₀))
  nlinarith

private theorem lowerSelectorDualIntegrand_le_majorant
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 3 / 5) :
    fourCellOddP11P1LowerSelectorResidual x ^ 2 /
        fourCellOddP11SelectorLowerWeight x ≤
      fourCellOddP11P1LowerDualMajorant x := by
  let W := fourCellOddP11SelectorLowerWeight x
  let H := fourCellOddP11P1ExactLowerH x
  let H₀ := fourCellOddP11P1RationalLowerH x
  let P := fourCellOddP11P1LowerReciprocalMajorant (5 * x / 3)
  have hW : 0 < W := fourCellOddP11SelectorLowerWeight_pos ⟨hx0, hx1⟩
  have hrecip : 1 / W ≤ P := by
    dsimp only [W, P]
    exact one_div_lowerWeight_le_reciprocalMajorant hx0 hx1
  have hP : 0 ≤ P := by
    have hone : 0 < 1 / W := one_div_pos.mpr hW
    linarith
  have herr : |H - H₀| ≤ (1 / 600 : ℝ) := by
    dsimp only [H, H₀]
    exact (abs_fourCellOddP11P1ExactLowerH_sub_rational_lt hx0
      (by linarith)).le
  have hsq := sq_le_rational_transfer herr
  have hbase : 2 * x * H ≤ 2 * x * H₀ + 1 / 300 := by
    have hdelta : H - H₀ ≤ (1 / 600 : ℝ) :=
      (le_abs_self (H - H₀)).trans herr
    have hmul := mul_le_mul_of_nonneg_left hdelta
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx0)
    nlinarith [hx1]
  have hcost : H ^ 2 / W ≤
      (101 / 100 : ℝ) * H₀ ^ 2 * P + 101 / 360000 * P := by
    have hfirst : H ^ 2 / W ≤ H ^ 2 * P := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [one_div] using hrecip) (sq_nonneg H)
    have hsecond := mul_le_mul_of_nonneg_right hsq hP
    nlinarith
  have hres := fourCellOddP11P1LowerResidual_eq_weight_add_H x
  have hid : (x * W + H) ^ 2 / W =
      x ^ 2 * W + 2 * x * H + H ^ 2 / W := by
    field_simp [hW.ne']
    ring
  rw [hres]
  change (x * W + H) ^ 2 / W ≤ _
  rw [hid]
  unfold fourCellOddP11P1LowerDualMajorant
  dsimp only [W, H, H₀, P] at hbase hcost ⊢
  linarith

private theorem upperSelectorDualIntegrand_le_majorant
    {x : ℝ} (hx0 : (3 / 5 : ℝ) < x) (hx1 : x < 1) :
    fourCellOddP11P1UpperSelectorResidual x ^ 2 /
        fourCellOddP11SelectorUpperWeight x ≤
      fourCellOddP11P1UpperDualMajorant x := by
  let W := fourCellOddP11SelectorUpperWeight x
  let H := fourCellOddP11P1ExactUpperH x
  let H₀ := fourCellOddP11P1RationalUpperH x
  let P := fourCellOddP11P1UpperReciprocalMajorant ((5 * x - 3) / 2)
  have hxpos : 0 < x := by linarith
  have hrecip : 1 / (x * W) ≤ P := by
    dsimp only [W, P]
    exact one_div_upperDensity_le_reciprocalMajorant hx0.le hx1
  have hW : 0 < W := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 50)
      (one_fiftieth_le_fourCellOddP11SelectorUpperWeight hx0 hx1)
  have hP : 0 ≤ P := by
    have hone : 0 < 1 / (x * W) := one_div_pos.mpr (mul_pos hxpos hW)
    linarith
  have herr : |H - H₀| ≤ (1 / 600 : ℝ) := by
    dsimp only [H, H₀]
    exact (abs_fourCellOddP11P1ExactUpperH_sub_rational_lt hxpos.le
      hx1.le).le
  have hsq := sq_le_rational_transfer herr
  have hbase : 2 * x * H ≤ 2 * x * H₀ + 1 / 300 := by
    have hdelta : H - H₀ ≤ (1 / 600 : ℝ) :=
      (le_abs_self (H - H₀)).trans herr
    have hmul := mul_le_mul_of_nonneg_left hdelta
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hxpos.le)
    nlinarith [hx1.le]
  have hcost : H ^ 2 / W ≤
      (101 / 100 : ℝ) * x * H₀ ^ 2 * P +
        101 / 360000 * x * P := by
    have hidcost : H ^ 2 / W = x * H ^ 2 * (1 / (x * W)) := by
      field_simp [hxpos.ne', hW.ne']
    rw [hidcost]
    have hfirst : x * H ^ 2 * (1 / (x * W)) ≤ x * H ^ 2 * P :=
      mul_le_mul_of_nonneg_left hrecip
        (mul_nonneg hxpos.le (sq_nonneg H))
    have hsecond := mul_le_mul_of_nonneg_right hsq
      (mul_nonneg hxpos.le hP)
    nlinarith
  have hres := fourCellOddP11P1UpperResidual_eq_weight_add_H hxpos.ne'
  have hid : (x * W + H) ^ 2 / W =
      x ^ 2 * W + 2 * x * H + H ^ 2 / W := by
    field_simp [hW.ne']
    ring
  rw [hres]
  change (x * W + H) ^ 2 / W ≤ _
  rw [hid]
  unfold fourCellOddP11P1UpperDualMajorant
  dsimp only [W, H, H₀, P] at hbase hcost ⊢
  linarith

private theorem continuous_fourCellOddP11P1RationalLowerH :
    Continuous fourCellOddP11P1RationalLowerH := by
  unfold fourCellOddP11P1RationalLowerH
    fourCellOddP11P1RationalRegularRepresenter
    fourCellOddP11P1Selector
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
  simp_rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
  fun_prop

private theorem continuous_fourCellOddP11P1RationalUpperH :
    Continuous fourCellOddP11P1RationalUpperH := by
  unfold fourCellOddP11P1RationalUpperH
    fourCellOddP11P1RationalRegularRepresenter
    fourCellOddP11P1Selector
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
  simp_rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
  fun_prop

private theorem continuous_fourCellOddP11P1LowerReciprocalMajorant :
    Continuous fourCellOddP11P1LowerReciprocalMajorant := by
  unfold fourCellOddP11P1LowerReciprocalMajorant bernsteinAtom
  fun_prop

private theorem continuous_fourCellOddP11P1UpperReciprocalMajorant :
    Continuous fourCellOddP11P1UpperReciprocalMajorant := by
  unfold fourCellOddP11P1UpperReciprocalMajorant bernsteinAtom
  fun_prop

private theorem intervalIntegrable_P1_lower_rational_base :
    IntervalIntegrable (fun x : ℝ ↦
      x ^ 2 * fourCellOddP11SelectorLowerWeight x +
        2 * x * fourCellOddP11P1RationalLowerH x)
      volume 0 (3 / 5) := by
  let V2 : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * x ^ 2
  have hV : IntervalIntegrable V2 volume 0 1 := by
    have h := intervalIntegrable_zero_one_endpointPotential_mul_x_mul
      (fun x : ℝ ↦ x) continuous_id
    apply h.congr
    intro x _hx
    dsimp only [V2]
    ring
  have hVL : IntervalIntegrable V2 volume 0 (3 / 5) := by
    apply hV.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hx.1, by linarith [hx.2]⟩
  rw [show (fun x : ℝ ↦
      x ^ 2 * fourCellOddP11SelectorLowerWeight x +
        2 * x * fourCellOddP11P1RationalLowerH x) = fun x ↦
      (93 / 50 : ℝ) * V2 x +
        ((27 / 250 : ℝ) * x ^ 2 +
          2 * x * fourCellOddP11P1RationalLowerH x) by
    funext x
    dsimp only [V2]
    unfold fourCellOddP11SelectorLowerWeight
    ring]
  have hpoly : IntervalIntegrable (fun x : ℝ ↦
      (27 / 250 : ℝ) * x ^ 2 +
        2 * x * fourCellOddP11P1RationalLowerH x)
      volume 0 (3 / 5) := by
    have hcont : Continuous (fun x : ℝ ↦
        (27 / 250 : ℝ) * x ^ 2 +
          2 * x * fourCellOddP11P1RationalLowerH x) :=
      (continuous_const.mul (continuous_id.pow 2)).add
        ((continuous_const.mul continuous_id).mul
          continuous_fourCellOddP11P1RationalLowerH)
    exact hcont.intervalIntegrable _ _
  exact (hVL.const_mul _).add hpoly

private theorem intervalIntegrable_P1_upper_rational_base :
    IntervalIntegrable (fun x : ℝ ↦
      x ^ 2 * fourCellOddP11SelectorUpperWeight x +
        2 * x * fourCellOddP11P1RationalUpperH x)
      volume (3 / 5) 1 := by
  let V2 : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * x ^ 2
  have hV : IntervalIntegrable V2 volume 0 1 := by
    have h := intervalIntegrable_zero_one_endpointPotential_mul_x_mul
      (fun x : ℝ ↦ x) continuous_id
    apply h.congr
    intro x _hx
    dsimp only [V2]
    ring
  have hVU : IntervalIntegrable V2 volume (3 / 5) 1 := by
    apply hV.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  rw [show (fun x : ℝ ↦
      x ^ 2 * fourCellOddP11SelectorUpperWeight x +
        2 * x * fourCellOddP11P1RationalUpperH x) = fun x ↦
      (93 / 50 : ℝ) * V2 x +
        ((6 / 5 : ℝ) * x - (57 / 25) * x ^ 2 +
          2 * x * fourCellOddP11P1RationalUpperH x) by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [V2, fourCellOddP11SelectorUpperWeight]
    · dsimp only [V2]
      unfold fourCellOddP11SelectorUpperWeight
      field_simp [hx]
      ring]
  have hpoly : IntervalIntegrable (fun x : ℝ ↦
      (6 / 5 : ℝ) * x - (57 / 25) * x ^ 2 +
        2 * x * fourCellOddP11P1RationalUpperH x)
      volume (3 / 5) 1 := by
    have hcont : Continuous (fun x : ℝ ↦
        (6 / 5 : ℝ) * x - (57 / 25) * x ^ 2 +
          2 * x * fourCellOddP11P1RationalUpperH x) :=
      ((continuous_const.mul continuous_id).sub
        (continuous_const.mul (continuous_id.pow 2))).add
          ((continuous_const.mul continuous_id).mul
            continuous_fourCellOddP11P1RationalUpperH)
    exact hcont.intervalIntegrable _ _
  exact (hVU.const_mul _).add hpoly

private theorem fourCellOddP11P1DualMajorant_integral_lt :
    (∫ x : ℝ in 0..3 / 5, fourCellOddP11P1LowerDualMajorant x) +
      (∫ x : ℝ in 3 / 5..1, fourCellOddP11P1UpperDualMajorant x) <
    (23 / 100 : ℝ) := by
  let cL : ℝ → ℝ := fun x ↦
    fourCellOddP11P1RationalLowerH x ^ 2 *
      fourCellOddP11P1LowerReciprocalMajorant (5 * x / 3)
  let mL : ℝ → ℝ := fun x ↦
    fourCellOddP11P1LowerReciprocalMajorant (5 * x / 3)
  let cU : ℝ → ℝ := fun x ↦
    x * fourCellOddP11P1RationalUpperH x ^ 2 *
      fourCellOddP11P1UpperReciprocalMajorant ((5 * x - 3) / 2)
  let mU : ℝ → ℝ := fun x ↦
    x * fourCellOddP11P1UpperReciprocalMajorant ((5 * x - 3) / 2)
  have hcL : Continuous cL := by
    dsimp only [cL]
    exact (continuous_fourCellOddP11P1RationalLowerH.pow 2).mul
      (continuous_fourCellOddP11P1LowerReciprocalMajorant.comp
        (by fun_prop))
  have hmL : Continuous mL := by
    dsimp only [mL]
    exact continuous_fourCellOddP11P1LowerReciprocalMajorant.comp (by fun_prop)
  have hcU : Continuous cU := by
    dsimp only [cU]
    exact (continuous_id.mul
      (continuous_fourCellOddP11P1RationalUpperH.pow 2)).mul
        (continuous_fourCellOddP11P1UpperReciprocalMajorant.comp
          (by fun_prop))
  have hmU : Continuous mU := by
    dsimp only [mU]
    exact continuous_id.mul
      (continuous_fourCellOddP11P1UpperReciprocalMajorant.comp (by fun_prop))
  let qL : ℝ → ℝ := fun x ↦
    (1 / 300 : ℝ) + (101 / 100) * cL x + (101 / 360000) * mL x
  let qU : ℝ → ℝ := fun x ↦
    (1 / 300 : ℝ) + (101 / 100) * cU x + (101 / 360000) * mU x
  have hqL : Continuous qL := by
    dsimp only [qL]
    exact (continuous_const.add (hcL.const_mul _)).add (hmL.const_mul _)
  have hqU : Continuous qU := by
    dsimp only [qU]
    exact (continuous_const.add (hcU.const_mul _)).add (hmU.const_mul _)
  have hdecompL : fourCellOddP11P1LowerDualMajorant = fun x ↦
      (x ^ 2 * fourCellOddP11SelectorLowerWeight x +
        2 * x * fourCellOddP11P1RationalLowerH x) + qL x := by
    funext x
    unfold fourCellOddP11P1LowerDualMajorant
    dsimp only [qL, cL, mL]
    ring
  have hdecompU : fourCellOddP11P1UpperDualMajorant = fun x ↦
      (x ^ 2 * fourCellOddP11SelectorUpperWeight x +
        2 * x * fourCellOddP11P1RationalUpperH x) + qU x := by
    funext x
    unfold fourCellOddP11P1UpperDualMajorant
    dsimp only [qU, cU, mU]
    ring
  have hqLint :
      (∫ x : ℝ in 0..3 / 5, qL x) =
        (1 / 300 : ℝ) * (3 / 5) +
          (101 / 100) * (∫ x : ℝ in 0..3 / 5, cL x) +
          (101 / 360000) * (∫ x : ℝ in 0..3 / 5, mL x) := by
    dsimp only [qL]
    have hconst : Continuous (fun _x : ℝ ↦ (1 / 300 : ℝ)) :=
      continuous_const
    have hc : Continuous (fun x : ℝ ↦ (101 / 100 : ℝ) * cL x) :=
      hcL.const_mul _
    have hm : Continuous (fun x : ℝ ↦ (101 / 360000 : ℝ) * mL x) :=
      hmL.const_mul _
    have houter := intervalIntegral.integral_add
      ((hconst.add hc).intervalIntegrable (0 : ℝ) (3 / 5) (μ := volume))
      (hm.intervalIntegrable (0 : ℝ) (3 / 5) (μ := volume))
    have hinner := intervalIntegral.integral_add
      (hconst.intervalIntegrable (0 : ℝ) (3 / 5) (μ := volume))
      (hc.intervalIntegrable (0 : ℝ) (3 / 5) (μ := volume))
    calc
      (∫ x : ℝ in 0..3 / 5,
          1 / 300 + 101 / 100 * cL x + 101 / 360000 * mL x) =
          (∫ x : ℝ in 0..3 / 5, 1 / 300 + 101 / 100 * cL x) +
            (∫ x : ℝ in 0..3 / 5, 101 / 360000 * mL x) := by
        simpa only [Pi.add_apply] using houter
      _ = ((∫ _x : ℝ in 0..3 / 5, (1 / 300 : ℝ)) +
            (∫ x : ℝ in 0..3 / 5, 101 / 100 * cL x)) +
            (∫ x : ℝ in 0..3 / 5, 101 / 360000 * mL x) := by
        rw [hinner]
      _ = _ := by
        repeat rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_const]
        norm_num
  have hqUint :
      (∫ x : ℝ in 3 / 5..1, qU x) =
        (1 / 300 : ℝ) * (2 / 5) +
          (101 / 100) * (∫ x : ℝ in 3 / 5..1, cU x) +
          (101 / 360000) * (∫ x : ℝ in 3 / 5..1, mU x) := by
    dsimp only [qU]
    have hconst : Continuous (fun _x : ℝ ↦ (1 / 300 : ℝ)) :=
      continuous_const
    have hc : Continuous (fun x : ℝ ↦ (101 / 100 : ℝ) * cU x) :=
      hcU.const_mul _
    have hm : Continuous (fun x : ℝ ↦ (101 / 360000 : ℝ) * mU x) :=
      hmU.const_mul _
    have houter := intervalIntegral.integral_add
      ((hconst.add hc).intervalIntegrable (3 / 5 : ℝ) 1 (μ := volume))
      (hm.intervalIntegrable (3 / 5 : ℝ) 1 (μ := volume))
    have hinner := intervalIntegral.integral_add
      (hconst.intervalIntegrable (3 / 5 : ℝ) 1 (μ := volume))
      (hc.intervalIntegrable (3 / 5 : ℝ) 1 (μ := volume))
    calc
      (∫ x : ℝ in 3 / 5..1,
          1 / 300 + 101 / 100 * cU x + 101 / 360000 * mU x) =
          (∫ x : ℝ in 3 / 5..1, 1 / 300 + 101 / 100 * cU x) +
            (∫ x : ℝ in 3 / 5..1, 101 / 360000 * mU x) := by
        simpa only [Pi.add_apply] using houter
      _ = ((∫ _x : ℝ in 3 / 5..1, (1 / 300 : ℝ)) +
            (∫ x : ℝ in 3 / 5..1, 101 / 100 * cU x)) +
            (∫ x : ℝ in 3 / 5..1, 101 / 360000 * mU x) := by
        rw [hinner]
      _ = _ := by
        repeat rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_const]
        norm_num
  rw [hdecompL, hdecompU,
    intervalIntegral.integral_add intervalIntegrable_P1_lower_rational_base
      (hqL.intervalIntegrable _ _),
    intervalIntegral.integral_add intervalIntegrable_P1_upper_rational_base
      (hqU.intervalIntegrable _ _),
    hqLint, hqUint]
  have hbase := fourCellOddP11P1Rational_base_lt
  have hcost := fourCellOddP11P1RationalH_reciprocal_cost_lt
  have hmass := fourCellOddP11P1Reciprocal_majorant_mass_lt
  dsimp only [cL, cU] at hcost ⊢
  dsimp only [mL, mU] at hmass ⊢
  nlinarith

private theorem intervalIntegrable_fourCellOddP11P1LowerDualMajorant :
    IntervalIntegrable fourCellOddP11P1LowerDualMajorant
      volume 0 (3 / 5) := by
  have htail : Continuous (fun x : ℝ ↦
      (1 / 300 : ℝ) +
        (101 / 100) * fourCellOddP11P1RationalLowerH x ^ 2 *
          fourCellOddP11P1LowerReciprocalMajorant (5 * x / 3) +
        (101 / 360000) *
          fourCellOddP11P1LowerReciprocalMajorant (5 * x / 3)) := by
    exact (continuous_const.add
      (((continuous_const.mul
        (continuous_fourCellOddP11P1RationalLowerH.pow 2)).mul
          (continuous_fourCellOddP11P1LowerReciprocalMajorant.comp
            (by fun_prop))))).add
      (continuous_const.mul
        (continuous_fourCellOddP11P1LowerReciprocalMajorant.comp
          (by fun_prop)))
  rw [show fourCellOddP11P1LowerDualMajorant = fun x ↦
      (x ^ 2 * fourCellOddP11SelectorLowerWeight x +
        2 * x * fourCellOddP11P1RationalLowerH x) +
      ((1 / 300 : ℝ) +
        (101 / 100) * fourCellOddP11P1RationalLowerH x ^ 2 *
          fourCellOddP11P1LowerReciprocalMajorant (5 * x / 3) +
        (101 / 360000) *
          fourCellOddP11P1LowerReciprocalMajorant (5 * x / 3)) by
    funext x
    unfold fourCellOddP11P1LowerDualMajorant
    ring]
  exact intervalIntegrable_P1_lower_rational_base.add
    (htail.intervalIntegrable _ _)

private theorem intervalIntegrable_fourCellOddP11P1UpperDualMajorant :
    IntervalIntegrable fourCellOddP11P1UpperDualMajorant
      volume (3 / 5) 1 := by
  have htail : Continuous (fun x : ℝ ↦
      (1 / 300 : ℝ) +
        (101 / 100) * x * fourCellOddP11P1RationalUpperH x ^ 2 *
          fourCellOddP11P1UpperReciprocalMajorant ((5 * x - 3) / 2) +
        (101 / 360000) * x *
          fourCellOddP11P1UpperReciprocalMajorant ((5 * x - 3) / 2)) := by
    exact (continuous_const.add
      ((((continuous_const.mul continuous_id).mul
        (continuous_fourCellOddP11P1RationalUpperH.pow 2)).mul
          (continuous_fourCellOddP11P1UpperReciprocalMajorant.comp
            (by fun_prop))))).add
      ((continuous_const.mul continuous_id).mul
        (continuous_fourCellOddP11P1UpperReciprocalMajorant.comp
          (by fun_prop)))
  rw [show fourCellOddP11P1UpperDualMajorant = fun x ↦
      (x ^ 2 * fourCellOddP11SelectorUpperWeight x +
        2 * x * fourCellOddP11P1RationalUpperH x) +
      ((1 / 300 : ℝ) +
        (101 / 100) * x * fourCellOddP11P1RationalUpperH x ^ 2 *
          fourCellOddP11P1UpperReciprocalMajorant ((5 * x - 3) / 2) +
        (101 / 360000) * x *
          fourCellOddP11P1UpperReciprocalMajorant ((5 * x - 3) / 2)) by
    funext x
    unfold fourCellOddP11P1UpperDualMajorant
    ring]
  exact intervalIntegrable_P1_upper_rational_base.add
    (htail.intervalIntegrable _ _)

private theorem fourCellOddP11P1SelectorDual_control :
    IntervalIntegrable (fun x : ℝ ↦
      fourCellOddP11P1LowerSelectorResidual x ^ 2 /
        fourCellOddP11SelectorLowerWeight x) volume 0 (3 / 5) ∧
    IntervalIntegrable (fun x : ℝ ↦
      fourCellOddP11P1UpperSelectorResidual x ^ 2 /
        fourCellOddP11SelectorUpperWeight x) volume (3 / 5) 1 ∧
    fourCellOddP11P1SelectorDual ≤ (23 / 100 : ℝ) := by
  let fL : ℝ → ℝ := fun x ↦
    fourCellOddP11P1LowerSelectorResidual x ^ 2 /
      fourCellOddP11SelectorLowerWeight x
  let fU : ℝ → ℝ := fun x ↦
    fourCellOddP11P1UpperSelectorResidual x ^ 2 /
      fourCellOddP11SelectorUpperWeight x
  let μL : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (3 / 5))
  let μU : Measure ℝ := volume.restrict (Ioc (3 / 5 : ℝ) 1)
  have hRfull : IntervalIntegrable fourCellOddP11P1RegularRepresenter
      volume (-1) 1 := by
    have h := intervalIntegrable_mul_P1RegularRepresenter
      (fun _x : ℝ ↦ 1) continuous_const
    simpa only [one_mul] using h
  have hRL : IntervalIntegrable fourCellOddP11P1RegularRepresenter
      volume 0 (3 / 5) := by
    apply hRfull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hRU : IntervalIntegrable fourCellOddP11P1RegularRepresenter
      volume (3 / 5) 1 := by
    apply hRfull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hRL hRU
  have hRmeasL : AEStronglyMeasurable fourCellOddP11P1RegularRepresenter μL := by
    simpa only [μL] using hRL.aestronglyMeasurable
  have hRmeasU : AEStronglyMeasurable fourCellOddP11P1RegularRepresenter μU := by
    simpa only [μU] using hRU.aestronglyMeasurable
  have hVglobal : Measurable yoshidaEndpointPotential := by
    unfold yoshidaEndpointPotential
    exact (Real.measurable_log.comp
      (measurable_const.sub (measurable_id.pow_const 2))).neg.div_const 2
  have hsel : Continuous fourCellOddP11P1Selector := by
    unfold fourCellOddP11P1Selector
    exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
      2 (3 / 2) (1 / 5) (3 / 4) (7 / 10)).continuous
  have hfLmeas : AEStronglyMeasurable fL μL := by
    have hx : AEStronglyMeasurable (fun x : ℝ ↦ x) μL :=
      continuous_id.aestronglyMeasurable
    have hWglobal : Measurable fourCellOddP11SelectorLowerWeight := by
      unfold fourCellOddP11SelectorLowerWeight
      exact (hVglobal.const_mul (93 / 50 : ℝ)).const_add (27 / 250 : ℝ)
    have hW : AEStronglyMeasurable fourCellOddP11SelectorLowerWeight μL :=
      hWglobal.aestronglyMeasurable
    have hH : AEStronglyMeasurable fourCellOddP11P1ExactLowerH μL := by
      have hraw := (((hRmeasL.const_mul
        (-(2 * fourCellOperatorHalfWidth))).sub
          hsel.aestronglyMeasurable).sub (hx.const_mul (27 / 250 : ℝ)))
      apply hraw.congr
      exact Filter.Eventually.of_forall fun x ↦ by
        unfold fourCellOddP11P1ExactLowerH
        simp only [Pi.sub_apply]
        ring
    have hG : AEStronglyMeasurable
        fourCellOddP11P1LowerSelectorResidual μL := by
      rw [show fourCellOddP11P1LowerSelectorResidual = fun x ↦
          x * fourCellOddP11SelectorLowerWeight x +
            fourCellOddP11P1ExactLowerH x by
        funext x
        exact fourCellOddP11P1LowerResidual_eq_weight_add_H x]
      exact (hx.mul hW).add hH
    dsimp only [fL]
    simpa only [div_eq_mul_inv] using
      (hG.pow 2).mul hWglobal.inv.aestronglyMeasurable
  have hfUmeas : AEStronglyMeasurable fU μU := by
    have hx : AEStronglyMeasurable (fun x : ℝ ↦ x) μU :=
      continuous_id.aestronglyMeasurable
    have hWglobal : Measurable fourCellOddP11SelectorUpperWeight := by
      unfold fourCellOddP11SelectorUpperWeight
      exact ((hVglobal.const_mul (93 / 50 : ℝ)).add
        (measurable_const.div measurable_id)).sub measurable_const
    have hW : AEStronglyMeasurable fourCellOddP11SelectorUpperWeight μU :=
      hWglobal.aestronglyMeasurable
    have hendpoint : AEStronglyMeasurable
        (fun x : ℝ ↦ Real.sqrt 2 * Real.log 2 * (8 / 5 - x)) μU :=
      (by fun_prop : Continuous (fun x : ℝ ↦
        Real.sqrt 2 * Real.log 2 * (8 / 5 - x))).aestronglyMeasurable
    have hlinear : AEStronglyMeasurable
        (fun x : ℝ ↦ (6 / 5 : ℝ) - (57 / 25) * x) μU :=
      (by fun_prop : Continuous (fun x : ℝ ↦
        (6 / 5 : ℝ) - (57 / 25) * x)).aestronglyMeasurable
    have hH : AEStronglyMeasurable fourCellOddP11P1ExactUpperH μU := by
      simpa only [fourCellOddP11P1ExactUpperH] using
        (((hendpoint.sub
          (hRmeasU.const_mul (2 * fourCellOperatorHalfWidth))).sub
            hsel.aestronglyMeasurable).sub hlinear)
    have hG : AEStronglyMeasurable
        fourCellOddP11P1UpperSelectorResidual μU := by
      apply ((hx.mul hW).add hH).congr
      have hne : ∀ᵐ x ∂μU, x ≠ 0 := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hxmem
        linarith [hxmem.1]
      filter_upwards [hne] with x hxne
      exact (fourCellOddP11P1UpperResidual_eq_weight_add_H hxne).symm
    dsimp only [fU]
    simpa only [div_eq_mul_inv] using
      (hG.pow 2).mul hWglobal.inv.aestronglyMeasurable
  have hboundL : ∀ᵐ x ∂μL, 0 ≤ fL x ∧
      fL x ≤ fourCellOddP11P1LowerDualMajorant x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hW := fourCellOddP11SelectorLowerWeight_pos ⟨hx.1.le, hx.2⟩
    exact ⟨div_nonneg (sq_nonneg _) hW.le,
      lowerSelectorDualIntegrand_le_majorant hx.1.le hx.2⟩
  have hneOne : ∀ᵐ x ∂μU, x ≠ 1 :=
    (MeasureTheory.Measure.ae_ne volume (1 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)
  have hboundU : ∀ᵐ x ∂μU, 0 ≤ fU x ∧
      fU x ≤ fourCellOddP11P1UpperDualMajorant x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hneOne] with x hx hxne
    have hxlt : x < 1 := lt_of_le_of_ne hx.2 hxne
    have hW := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 50)
      (one_fiftieth_le_fourCellOddP11SelectorUpperWeight hx.1 hxlt)
    exact ⟨div_nonneg (sq_nonneg _) hW.le,
      upperSelectorDualIntegrand_le_majorant hx.1 hxlt⟩
  have hL := intervalIntegrable_and_integral_le_of_ae_nonneg_le
    (by norm_num : (0 : ℝ) ≤ 3 / 5) fL
    fourCellOddP11P1LowerDualMajorant
    intervalIntegrable_fourCellOddP11P1LowerDualMajorant
    (by simpa only [μL] using hfLmeas)
    (by simpa only [μL] using hboundL)
  have hU := intervalIntegrable_and_integral_le_of_ae_nonneg_le
    (by norm_num : (3 / 5 : ℝ) ≤ 1) fU
    fourCellOddP11P1UpperDualMajorant
    intervalIntegrable_fourCellOddP11P1UpperDualMajorant
    (by simpa only [μU] using hfUmeas)
    (by simpa only [μU] using hboundU)
  have hsum := add_le_add hL.2 hU.2
  have hmaj := fourCellOddP11P1DualMajorant_integral_lt
  have hdual : fourCellOddP11P1SelectorDual ≤ (23 / 100 : ℝ) := by
    unfold fourCellOddP11P1SelectorDual
    dsimp only [fL, fU] at hsum
    linarith
  simpa only [fL, fU] using And.intro hL.1 (And.intro hU.1 hdual)

/-- The concrete degree-`< 11` selector costs at most `23/100` against the
exact two-strip multiplication density.  The proof uses one global
degree-sixteen endpoint envelope and exact rational integrals; no interval
mesh or exhaustive evaluation enters the certificate. -/
theorem fourCellOddP11P1SelectorDual_le :
    fourCellOddP11P1SelectorDual ≤ (23 / 100 : ℝ) :=
  fourCellOddP11P1SelectorDual_control.2.2

private theorem memLp_div_sqrt_of_integrable_sq_div
    (G W : ℝ → ℝ) (a b : ℝ)
    (hG : AEStronglyMeasurable G (volume.restrict (Ioc a b)))
    (hW : Measurable W)
    (hWpos : ∀ᵐ x ∂volume.restrict (Ioc a b), 0 < W x)
    (hInt : Integrable (fun x ↦ G x ^ 2 / W x)
      (volume.restrict (Ioc a b))) :
    MemLp (fun x ↦ G x / Real.sqrt (W x)) 2
      (volume.restrict (Ioc a b)) := by
  have hsqrt : Measurable (fun x ↦ Real.sqrt (W x)) :=
    hW.sqrt
  have hmeas : AEStronglyMeasurable
      (fun x ↦ G x / Real.sqrt (W x))
      (volume.restrict (Ioc a b)) := by
    simpa only [div_eq_mul_inv] using
      hG.mul hsqrt.inv.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  apply hInt.congr
  filter_upwards [hWpos] with x hx
  rw [Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hx.le]

private theorem memLp_sqrt_mul_of_integrable_weighted_sq
    (r W : ℝ → ℝ) (a b : ℝ)
    (hr : AEStronglyMeasurable r (volume.restrict (Ioc a b)))
    (hW : Measurable W)
    (hWpos : ∀ᵐ x ∂volume.restrict (Ioc a b), 0 < W x)
    (hInt : Integrable (fun x ↦ W x * r x ^ 2)
      (volume.restrict (Ioc a b))) :
    MemLp (fun x ↦ Real.sqrt (W x) * r x) 2
      (volume.restrict (Ioc a b)) := by
  have hsqrt : Measurable (fun x ↦ Real.sqrt (W x)) :=
    hW.sqrt
  have hmeas : AEStronglyMeasurable
      (fun x ↦ Real.sqrt (W x) * r x)
      (volume.restrict (Ioc a b)) :=
    hsqrt.aestronglyMeasurable.mul hr
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  apply hInt.congr
  filter_upwards [hWpos] with x hx
  rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hx.le]

private theorem intervalIntegrable_lowerWeight_mul_sq
    (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable (fun x ↦
      fourCellOddP11SelectorLowerWeight x * r x ^ 2)
      volume 0 (3 / 5) := by
  have hmass : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2)
      volume 0 (3 / 5) := (hr.pow 2).intervalIntegrable _ _
  have hpotentialFull := intervalIntegrable_endpointPotential_mul_sq r hr
  have hpotential : IntervalIntegrable (fun x : ℝ ↦
      yoshidaEndpointPotential x * r x ^ 2) volume 0 (3 / 5) := by
    apply hpotentialFull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [show (fun x ↦ fourCellOddP11SelectorLowerWeight x * r x ^ 2) =
      fun x ↦ (27 / 250 : ℝ) * r x ^ 2 +
        (93 / 50) * (yoshidaEndpointPotential x * r x ^ 2) by
    funext x
    unfold fourCellOddP11SelectorLowerWeight
    ring]
  exact (hmass.const_mul _).add (hpotential.const_mul _)

private theorem intervalIntegrable_upperWeight_mul_sq
    (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable (fun x ↦
      fourCellOddP11SelectorUpperWeight x * r x ^ 2)
      volume (3 / 5) 1 := by
  have hmass : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2)
      volume (3 / 5) 1 := (hr.pow 2).intervalIntegrable _ _
  have hpotentialFull := intervalIntegrable_endpointPotential_mul_sq r hr
  have hpotential : IntervalIntegrable (fun x : ℝ ↦
      yoshidaEndpointPotential x * r x ^ 2) volume (3 / 5) 1 := by
    apply hpotentialFull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hdivCont : ContinuousOn (fun x : ℝ ↦ r x ^ 2 / x)
      (Icc (3 / 5 : ℝ) 1) := by
    apply ContinuousOn.div (hr.pow 2).continuousOn continuous_id.continuousOn
    intro x hx
    simp only [id_eq]
    linarith [hx.1]
  have hdiv : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2 / x)
      volume (3 / 5) 1 := by
    have hcontU : ContinuousOn (fun x : ℝ ↦ r x ^ 2 / x)
        (uIcc (3 / 5 : ℝ) 1) := by
      rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)]
      exact hdivCont
    exact hcontU.intervalIntegrable
  have heq : (fun x ↦ fourCellOddP11SelectorUpperWeight x * r x ^ 2) =
      fun x ↦ (93 / 50 : ℝ) *
          (yoshidaEndpointPotential x * r x ^ 2) +
        (6 / 5) * (r x ^ 2 / x) - (57 / 25) * r x ^ 2 := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [fourCellOddP11SelectorUpperWeight]
      ring
    · unfold fourCellOddP11SelectorUpperWeight
      field_simp [hx]
  rw [heq]
  exact ((hpotential.const_mul _).add (hdiv.const_mul _)).sub
    (hmass.const_mul _)

/-- The exact row is lower on the lower strip and gains the affine endpoint
term only on the upper strip. -/
private def fourCellOddP11P1PiecewiseRepresenter (x : ℝ) : ℝ :=
  if x ≤ 3 / 5 then fourCellOddP11P1LowerRepresenter x
  else fourCellOddP11P1UpperRepresenter x

/-- Quantitative weighted Cauchy for the pure degree-one extension row. -/
theorem fourCellOddCoreLocalBilinear_P1_P11Plus_sq_le_23_exactTailWeight
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    fourCellOddCoreLocalBilinear centeredP1 r ^ 2 ≤
      (23 / 100 : ℝ) * fourCellOddP1ExactTailWeight r := by
  let F := fourCellOddP11P1PiecewiseRepresenter
  let q := fourCellOddP11P1Selector
  let μL : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (3 / 5))
  let μU : Measure ℝ := volume.restrict (Ioc (3 / 5 : ℝ) 1)
  have hV : Measurable yoshidaEndpointPotential := by
    unfold yoshidaEndpointPotential
    exact (Real.measurable_log.comp
      (measurable_const.sub (measurable_id.pow_const 2))).neg.div_const 2
  have hWLmeas : Measurable fourCellOddP11SelectorLowerWeight := by
    unfold fourCellOddP11SelectorLowerWeight
    exact (hV.const_mul (93 / 50 : ℝ)).const_add (27 / 250 : ℝ)
  have hWUmeas : Measurable fourCellOddP11SelectorUpperWeight := by
    unfold fourCellOddP11SelectorUpperWeight
    exact ((hV.const_mul (93 / 50 : ℝ)).add
      (measurable_const.div measurable_id)).sub measurable_const
  have hWLpos : ∀ᵐ x ∂μL, 0 < fourCellOddP11SelectorLowerWeight x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact fourCellOddP11SelectorLowerWeight_pos ⟨hx.1.le, hx.2⟩
  have hneOne : ∀ᵐ x ∂μU, x ≠ 1 :=
    (MeasureTheory.Measure.ae_ne volume (1 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)
  have hWUpos : ∀ᵐ x ∂μU, 0 < fourCellOddP11SelectorUpperWeight x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hneOne] with x hx hxne
    have hxlt : x < 1 := lt_of_le_of_ne hx.2 hxne
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 50)
      (one_fiftieth_le_fourCellOddP11SelectorUpperWeight hx.1 hxlt)
  have hRfull : IntervalIntegrable fourCellOddP11P1RegularRepresenter
      volume (-1) 1 := by
    have h := intervalIntegrable_mul_P1RegularRepresenter
      (fun _x : ℝ ↦ 1) continuous_const
    simpa only [one_mul] using h
  have hRL : IntervalIntegrable fourCellOddP11P1RegularRepresenter
      volume 0 (3 / 5) := by
    apply hRfull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hRU : IntervalIntegrable fourCellOddP11P1RegularRepresenter
      volume (3 / 5) 1 := by
    apply hRfull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hRL hRU
  have hRmeasL : AEStronglyMeasurable fourCellOddP11P1RegularRepresenter μL := by
    simpa only [μL] using hRL.aestronglyMeasurable
  have hRmeasU : AEStronglyMeasurable fourCellOddP11P1RegularRepresenter μU := by
    simpa only [μU] using hRU.aestronglyMeasurable
  have hsel : Continuous fourCellOddP11P1Selector := by
    unfold fourCellOddP11P1Selector
    exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
      2 (3 / 2) (1 / 5) (3 / 4) (7 / 10)).continuous
  have hGL : AEStronglyMeasurable fourCellOddP11P1LowerSelectorResidual μL := by
    have hx : AEStronglyMeasurable (fun x : ℝ ↦ x) μL :=
      continuous_id.aestronglyMeasurable
    have hW : AEStronglyMeasurable fourCellOddP11SelectorLowerWeight μL :=
      hWLmeas.aestronglyMeasurable
    have hraw := (((hRmeasL.const_mul
      (-(2 * fourCellOperatorHalfWidth))).sub
        hsel.aestronglyMeasurable).sub (hx.const_mul (27 / 250 : ℝ)))
    have hH : AEStronglyMeasurable fourCellOddP11P1ExactLowerH μL := by
      apply hraw.congr
      exact Filter.Eventually.of_forall fun x ↦ by
        unfold fourCellOddP11P1ExactLowerH
        simp only [Pi.sub_apply]
        ring
    rw [show fourCellOddP11P1LowerSelectorResidual = fun x ↦
        x * fourCellOddP11SelectorLowerWeight x +
          fourCellOddP11P1ExactLowerH x by
      funext x
      exact fourCellOddP11P1LowerResidual_eq_weight_add_H x]
    exact (hx.mul hW).add hH
  have hGU : AEStronglyMeasurable fourCellOddP11P1UpperSelectorResidual μU := by
    have hx : AEStronglyMeasurable (fun x : ℝ ↦ x) μU :=
      continuous_id.aestronglyMeasurable
    have hW : AEStronglyMeasurable fourCellOddP11SelectorUpperWeight μU :=
      hWUmeas.aestronglyMeasurable
    have hendpoint : AEStronglyMeasurable
        (fun x : ℝ ↦ Real.sqrt 2 * Real.log 2 * (8 / 5 - x)) μU :=
      (by fun_prop : Continuous (fun x : ℝ ↦
        Real.sqrt 2 * Real.log 2 * (8 / 5 - x))).aestronglyMeasurable
    have hlinear : AEStronglyMeasurable
        (fun x : ℝ ↦ (6 / 5 : ℝ) - (57 / 25) * x) μU :=
      (by fun_prop : Continuous (fun x : ℝ ↦
        (6 / 5 : ℝ) - (57 / 25) * x)).aestronglyMeasurable
    have hH : AEStronglyMeasurable fourCellOddP11P1ExactUpperH μU := by
      simpa only [fourCellOddP11P1ExactUpperH] using
        (((hendpoint.sub
          (hRmeasU.const_mul (2 * fourCellOperatorHalfWidth))).sub
            hsel.aestronglyMeasurable).sub hlinear)
    apply ((hx.mul hW).add hH).congr
    have hne : ∀ᵐ x ∂μU, x ≠ 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hxmem
      linarith [hxmem.1]
    filter_upwards [hne] with x hxne
    exact (fourCellOddP11P1UpperResidual_eq_weight_add_H hxne).symm
  have hIntL := fourCellOddP11P1SelectorDual_control.1
  have hIntU := fourCellOddP11P1SelectorDual_control.2.1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hIntL hIntU
  have hdualL₀ := memLp_div_sqrt_of_integrable_sq_div
    fourCellOddP11P1LowerSelectorResidual fourCellOddP11SelectorLowerWeight
    0 (3 / 5) (by simpa only [μL] using hGL) hWLmeas
    (by simpa only [μL] using hWLpos) hIntL
  have hdualU₀ := memLp_div_sqrt_of_integrable_sq_div
    fourCellOddP11P1UpperSelectorResidual fourCellOddP11SelectorUpperWeight
    (3 / 5) 1 (by simpa only [μU] using hGU) hWUmeas
    (by simpa only [μU] using hWUpos) hIntU
  have hdualL : MemLp (fun x ↦
      fourCellOddP11SelectorResidual F q x /
        Real.sqrt (fourCellOddP11SelectorLowerWeight x)) 2 μL := by
    apply MemLp.ae_eq ?_ (by simpa only [μL] using hdualL₀)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    unfold fourCellOddP11SelectorResidual F q
      fourCellOddP11P1PiecewiseRepresenter
      fourCellOddP11P1LowerSelectorResidual
    rw [if_pos hx.2]
  have hdualU : MemLp (fun x ↦
      fourCellOddP11SelectorResidual F q x /
        Real.sqrt (fourCellOddP11SelectorUpperWeight x)) 2 μU := by
    apply MemLp.ae_eq ?_ (by simpa only [μU] using hdualU₀)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    unfold fourCellOddP11SelectorResidual F q
      fourCellOddP11P1PiecewiseRepresenter
      fourCellOddP11P1UpperSelectorResidual
    rw [if_neg (not_le_of_gt hx.1)]
  have hweightedL := intervalIntegrable_lowerWeight_mul_sq r hr.continuous
  have hweightedU := intervalIntegrable_upperWeight_mul_sq r hr.continuous
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hweightedL
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hweightedU
  have hprimalL := memLp_sqrt_mul_of_integrable_weighted_sq r
    fourCellOddP11SelectorLowerWeight 0 (3 / 5)
    hr.continuous.aestronglyMeasurable hWLmeas
    (by simpa only [μL] using hWLpos) hweightedL
  have hprimalU := memLp_sqrt_mul_of_integrable_weighted_sq r
    fourCellOddP11SelectorUpperWeight (3 / 5) 1
    hr.continuous.aestronglyMeasurable hWUmeas
    (by simpa only [μU] using hWUpos) hweightedU
  have hrow := fourCellOddCoreLocalBilinear_P1_P11Plus_eq_selectorResiduals
    r hr hodd h1 h3 h5 h7 h9
  have hpairL :
      (∫ x : ℝ in 0..3 / 5,
        fourCellOddP11SelectorResidual F q x * r x) =
      ∫ x : ℝ in 0..3 / 5,
        fourCellOddP11P1LowerSelectorResidual x * r x := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall fun x hx ↦ by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
      unfold fourCellOddP11SelectorResidual F q
        fourCellOddP11P1PiecewiseRepresenter
        fourCellOddP11P1LowerSelectorResidual
      rw [if_pos hx.2]
  have hpairU :
      (∫ x : ℝ in 3 / 5..1,
        fourCellOddP11SelectorResidual F q x * r x) =
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddP11P1UpperSelectorResidual x * r x := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall fun x hx ↦ by
      rw [uIoc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
      unfold fourCellOddP11SelectorResidual F q
        fourCellOddP11P1PiecewiseRepresenter
        fourCellOddP11P1UpperSelectorResidual
      rw [if_neg (not_le_of_gt hx.1)]
  have hpair : fourCellOddCoreLocalBilinear centeredP1 r =
      (∫ x : ℝ in 0..3 / 5,
        fourCellOddP11SelectorResidual F q x * r x) +
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddP11SelectorResidual F q x * r x := by
    rw [hpairL, hpairU]
    exact hrow
  have hdualEq : fourCellOddP11SelectorDual F q =
      fourCellOddP11P1SelectorDual := by
    unfold fourCellOddP11SelectorDual fourCellOddP11P1SelectorDual
    congr 1
    · apply intervalIntegral.integral_congr_ae
      exact Filter.Eventually.of_forall fun x hx ↦ by
        rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
        unfold fourCellOddP11SelectorResidual F q
          fourCellOddP11P1PiecewiseRepresenter
          fourCellOddP11P1LowerSelectorResidual
        rw [if_pos hx.2]
    · apply intervalIntegral.integral_congr_ae
      exact Filter.Eventually.of_forall fun x hx ↦ by
        rw [uIoc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
        unfold fourCellOddP11SelectorResidual F q
          fourCellOddP11P1PiecewiseRepresenter
          fourCellOddP11P1UpperSelectorResidual
        rw [if_neg (not_le_of_gt hx.1)]
  have hcauchy := sq_pairing_le_selectorDual_mul_weightedReserve
    F q r (fourCellOddCoreLocalBilinear centeredP1 r)
    hpair hdualL hprimalL hdualU hprimalU
  rw [hdualEq,
    fourCellOddP11SelectorWeightedReserve_eq_exactTailWeight r hr.continuous]
    at hcauchy
  have hreserveNonneg : 0 ≤ fourCellOddP11SelectorWeightedReserve r := by
    unfold fourCellOddP11SelectorWeightedReserve
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    apply add_nonneg
    · apply integral_nonneg_of_ae
      filter_upwards [hWLpos] with x hx
      exact mul_nonneg hx.le (sq_nonneg _)
    · apply integral_nonneg_of_ae
      filter_upwards [hWUpos] with x hx
      exact mul_nonneg hx.le (sq_nonneg _)
  have hweightNonneg : 0 ≤ fourCellOddP1ExactTailWeight r := by
    rw [← fourCellOddP11SelectorWeightedReserve_eq_exactTailWeight
      r hr.continuous]
    exact hreserveNonneg
  have hdualMul := mul_le_mul_of_nonneg_right
    fourCellOddP11P1SelectorDual_le hweightNonneg
  exact hcauchy.trans hdualMul

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11P1TailSchurStructural
