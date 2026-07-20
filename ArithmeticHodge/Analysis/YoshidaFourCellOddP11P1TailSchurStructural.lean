import ArithmeticHodge.Analysis.YoshidaFourCellOddP11ThreeHalvesClosureStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedRegularRemainderStructural

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
