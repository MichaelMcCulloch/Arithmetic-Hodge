import ArithmeticHodge.Analysis.YoshidaFourCellOddP11ThreeHalvesClosureStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedRegularRemainderStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5CleanSharpStructural

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

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11P1TailSchurStructural
