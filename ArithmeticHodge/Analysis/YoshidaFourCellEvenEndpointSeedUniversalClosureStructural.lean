import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCombinedNormStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCoshBorderCompletionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRankResidualBound

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped Interval

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedUniversalClosureStructural

noncomputable section

open YoshidaConstantBounds
open CenteredEndpointCorrelation
open ShiftedLegendreLogEnergyOrthogonalProjection
open UnitIntervalLogEnergyAffine
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicRankResidualBound
open YoshidaFactorTwoPhaseIntrinsicNineCanonicalProjectionStructural
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFourCellEvenEndpointCoshSchurStructural
open YoshidaFourCellEvenEndpointCapacityCauchyStructural
open YoshidaFourCellEvenEndpointSeedCapacityCrossStructural
open YoshidaFourCellEvenEndpointSeedCombinedNormStructural
open YoshidaFourCellEvenEndpointSeedCoshBorderCompletionStructural
open YoshidaFourCellEvenEndpointSeedCutoffEightBridgeStructural
open YoshidaFourCellEvenEndpointSeedRegularRemainderStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellEvenZeroCoshCoupledCoreStructural
open YoshidaFourCellEvenZeroCoshRegularStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# Universal endpoint-seed low--tail closure

The canonical cutoff-eight residual need not itself have zero wide-cosh
moment.  Consequently the already-closed tail Schur theorem cannot simply be
applied to that residual.  This file instead keeps the tail row as a genuine
Riesz functional.  Its squared norm is bounded before any zero-cosh
assumption is used, and a sharp scalar Young split removes that functional
from the remaining universal obligation.

The resulting free-parameter Young estimate is deliberately diagnostic.  It
shows exactly how an unweighted tail norm trades against the very thin finite
row margin, without asserting that a fixed coarse split closes the universal
Schur determinant.  A final proof needs a weighted/harmonic tail estimate (or
an equivalent coupled block argument) rather than another fixed mass charge.
-/

/-- The rational squared-norm budget retained by the canonical complete
endpoint-tail representer before weakening the fixed `1/80` seed reserve to
the actual seed bracket. -/
def fourCellEvenEndpointSeedCanonicalTailNormBudget : ℝ :=
  5221 / 19600000

/-- The complete endpoint-seed row carried by a genuine `P8+` residual. -/
def fourCellEvenEndpointSeedCanonicalTailRow (r : ℝ → ℝ) : ℝ :=
  fourCellEvenEndpointCapacityPolarization
      fourCellEvenEndpointCoshSeed r -
    2 * fourCellOperatorHalfWidth *
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          factorTwoCenteredCorrelationBilinear
            fourCellEvenEndpointCoshSeed r t)

/-- The explicit finite row in the canonical cutoff-eight decomposition. -/
def fourCellEvenEndpointSeedCanonicalLowRow
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ :=
  fourCellEvenEndpointSeedP0246CompleteLowRow
    (factorTwoCanonicalLegendreCoefficient w hw 0)
    (factorTwoCanonicalLegendreCoefficient w hw 2)
    (factorTwoCanonicalLegendreCoefficient w hw 4)
    (factorTwoCanonicalLegendreCoefficient w hw 6)

/-- The centered squared mass of the canonical `P8+` residual. -/
def fourCellEvenEndpointSeedCanonicalTailMass
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ :=
  ∫ x : ℝ in -1..1, centeredLegendreHigherResidual w hw 8 x ^ 2

/-- Remove an arbitrary additional low polynomial from the canonical
cutoff-eight endpoint representer.  On a `P₁₄+` tail every polynomial of
degree below fourteen is annihilated, so this selector can absorb the exact
`P₈/P₁₀/P₁₂` representer coordinates before Cauchy--Schwarz is applied. -/
def fourCellEvenEndpointSeedTailFourteenRepresenter
    (q : ℝ[X]) (x : ℝ) : ℝ :=
  fourCellEvenEndpointSeedProjectedTailRowRepresenter
      fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial x -
    centeredPolynomialLift q x

/-- The centered Riesz representer of the positive-half wide-cosh
coordinate on even profiles. -/
def fourCellEvenHalfWideCoshRepresenter (x : ℝ) : ℝ :=
  Real.cosh ((fourCellOperatorHalfWidth / 2) * x) / 2

/-- The quadratic Taylor selector for the half-wide-cosh direction, written
in the unit-interval polynomial coordinate used by
`centeredPolynomialLift`.  Its pullback is exactly
`(1 + (λx)² / 2) / 2`, where `λ = fourCellOperatorHalfWidth / 2`. -/
def fourCellEvenHalfWideCoshQuadraticSelectorPolynomial : ℝ[X] :=
  Polynomial.C (1 / 2 : ℝ) +
    Polynomial.C ((fourCellOperatorHalfWidth / 2) ^ 2 / 4) *
      (2 • Polynomial.X - Polynomial.C 1) ^ 2

theorem natDegree_fourCellEvenHalfWideCoshQuadraticSelectorPolynomial_lt_fourteen :
    fourCellEvenHalfWideCoshQuadraticSelectorPolynomial.natDegree < 14 := by
  unfold fourCellEvenHalfWideCoshQuadraticSelectorPolynomial
  compute_degree
  norm_num

theorem centeredPolynomialLift_halfWideCoshQuadraticSelector_eq
    (x : ℝ) :
    centeredPolynomialLift
        fourCellEvenHalfWideCoshQuadraticSelectorPolynomial x =
      (1 + ((fourCellOperatorHalfWidth / 2) * x) ^ 2 / 2) / 2 := by
  unfold centeredPolynomialLift
    fourCellEvenHalfWideCoshQuadraticSelectorPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_smul,
    Polynomial.eval_X]
  ring

/-- Uniform error of the concrete quadratic cosh selector.  The estimate is
Taylor-structural and uses the whole interval at once; no mode list or sample
grid enters. -/
theorem abs_fourCellEvenHalfWideCoshRepresenter_sub_quadraticSelector_lt
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |fourCellEvenHalfWideCoshRepresenter x -
        centeredPolynomialLift
          fourCellEvenHalfWideCoshQuadraticSelectorPolynomial x| <
      (1 / 10000 : ℝ) := by
  let lambda : ℝ := fourCellOperatorHalfWidth / 2
  let z : ℝ := lambda * x
  have hlambda0 : 0 ≤ lambda := by
    dsimp only [lambda]
    unfold fourCellOperatorHalfWidth
    positivity
  have hlambda : lambda < (217 / 1000 : ℝ) := by
    have hlog := strict_log_two_bounds.2
    dsimp only [lambda]
    unfold fourCellOperatorHalfWidth
    nlinarith
  have hxAbs : |x| ≤ 1 := abs_le.mpr hx
  have hzAbs : |z| < (217 / 1000 : ℝ) := by
    dsimp only [z]
    rw [abs_mul, abs_of_nonneg hlambda0]
    calc
      lambda * |x| ≤ lambda * 1 :=
        mul_le_mul_of_nonneg_left hxAbs hlambda0
      _ = lambda := by ring
      _ < 217 / 1000 := hlambda
  have hu0 : 0 ≤ |z| ^ 2 / 2 := by positivity
  have huHalf : |z| ^ 2 / 2 < (1 / 2 : ℝ) := by
    have hzSq : |z| ^ 2 < (217 / 1000 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hzAbs (abs_nonneg z) (by norm_num)
    nlinarith
  have hu1 : |z| ^ 2 / 2 < (1 : ℝ) := huHalf.trans (by norm_num)
  have hexp : Real.exp (|z| ^ 2 / 2) ≤
      1 / (1 - |z| ^ 2 / 2) :=
    Real.exp_bound_div_one_sub_of_interval hu0 hu1
  have hfrac : 1 / (1 - |z| ^ 2 / 2) < (2 : ℝ) := by
    rw [div_lt_iff₀ (sub_pos.mpr hu1)]
    nlinarith only [huHalf]
  have hcosh : Real.cosh |z| < (2 : ℝ) :=
    (Real.cosh_le_exp_half_sq |z|).trans_lt (hexp.trans_lt hfrac)
  have htaylor := abs_cosh_sub_quadratic_le z
  have hproduct : Real.cosh |z| * |z| ^ 4 / 24 <
      (1 / 5000 : ℝ) := by
    have hzPow : |z| ^ 4 < (217 / 1000 : ℝ) ^ 4 :=
      pow_lt_pow_left₀ hzAbs (abs_nonneg z) (by norm_num)
    have hcosh0 : 0 ≤ Real.cosh |z| := (Real.cosh_pos _).le
    have hzPow0 : 0 ≤ |z| ^ 4 := pow_nonneg (abs_nonneg z) 4
    have hmulLeft : Real.cosh |z| * |z| ^ 4 ≤
        2 * |z| ^ 4 := mul_le_mul_of_nonneg_right hcosh.le hzPow0
    have hmulRight : (2 : ℝ) * |z| ^ 4 <
        2 * (217 / 1000 : ℝ) ^ 4 :=
      mul_lt_mul_of_pos_left hzPow (by norm_num)
    have hrat : (2 : ℝ) * (217 / 1000 : ℝ) ^ 4 / 24 <
        1 / 5000 := by norm_num
    exact (div_le_div_of_nonneg_right hmulLeft (by norm_num)).trans_lt
      ((div_lt_div_of_pos_right hmulRight (by norm_num)).trans hrat)
  have hresidual : |Real.cosh z - 1 - z ^ 2 / 2| <
      (1 / 5000 : ℝ) := htaylor.trans_lt hproduct
  rw [centeredPolynomialLift_halfWideCoshQuadraticSelector_eq]
  unfold fourCellEvenHalfWideCoshRepresenter
  dsimp only [z, lambda] at hresidual ⊢
  rw [show Real.cosh ((fourCellOperatorHalfWidth / 2) * x) / 2 -
      (1 + ((fourCellOperatorHalfWidth / 2) * x) ^ 2 / 2) / 2 =
        (Real.cosh ((fourCellOperatorHalfWidth / 2) * x) - 1 -
          ((fourCellOperatorHalfWidth / 2) * x) ^ 2 / 2) / 2 by ring,
    abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

/-- The actual `P₁₄+` cosh pivot is tiny after the concrete quadratic
selector is removed.  This turns the cosh border into a perturbative scalar,
without evaluating any Legendre coefficient. -/
theorem integral_halfWideCosh_sub_quadraticSelector_sq_le :
    (∫ x : ℝ in -1..1,
      (fourCellEvenHalfWideCoshRepresenter x -
        centeredPolynomialLift
          fourCellEvenHalfWideCoshQuadraticSelectorPolynomial x) ^ 2) ≤
      (1 / 50000000 : ℝ) := by
  let f : ℝ → ℝ := fun x ↦
    (fourCellEvenHalfWideCoshRepresenter x -
      centeredPolynomialLift
        fourCellEvenHalfWideCoshQuadraticSelectorPolynomial x) ^ 2
  have hf : Continuous f := by
    dsimp only [f, fourCellEvenHalfWideCoshRepresenter,
      centeredPolynomialLift,
      fourCellEvenHalfWideCoshQuadraticSelectorPolynomial]
    fun_prop
  have hconst : IntervalIntegrable (fun _x : ℝ ↦ (1 / 100000000 : ℝ))
      volume (-1) 1 := Continuous.intervalIntegrable continuous_const _ _
  have hmono : (∫ x : ℝ in -1..1, f x) ≤
      ∫ _x : ℝ in -1..1, (1 / 100000000 : ℝ) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hf.intervalIntegrable _ _) hconst
    intro x hx
    have herr :=
      abs_fourCellEvenHalfWideCoshRepresenter_sub_quadraticSelector_lt
        hx
    have habs0 : 0 ≤ |fourCellEvenHalfWideCoshRepresenter x -
        centeredPolynomialLift
          fourCellEvenHalfWideCoshQuadraticSelectorPolynomial x| :=
      abs_nonneg _
    have hsq := pow_lt_pow_left₀ herr habs0 (n := 2) (by norm_num)
    calc
      f x = |fourCellEvenHalfWideCoshRepresenter x -
          centeredPolynomialLift
            fourCellEvenHalfWideCoshQuadraticSelectorPolynomial x| ^ 2 := by
        dsimp only [f]
        rw [sq_abs]
      _ ≤ (1 / 10000 : ℝ) ^ 2 := hsq.le
      _ = 1 / 100000000 := by norm_num
  dsimp only [f] at hmono ⊢
  calc
    _ ≤ ∫ _x : ℝ in -1..1, (1 / 100000000 : ℝ) := hmono
    _ = 1 / 50000000 := by norm_num

/-- Simultaneously remove a finite polynomial selector and an arbitrary
multiple of the wide-cosh constraint from the `P₁₄+` row representer. -/
def fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter
    (q : ℝ[X]) (s : ℝ) (x : ℝ) : ℝ :=
  fourCellEvenEndpointSeedTailFourteenRepresenter q x -
    s * fourCellEvenHalfWideCoshRepresenter x

/-- The true cosh direction in the `P₁₄+` quotient.  An arbitrary low
polynomial is removed from the half-cosh representer before its scalar border
is formed.  This matters: the full half-cosh norm contains a large constant
coordinate that every genuine `P₁₄+` tail already annihilates. -/
def fourCellEvenEndpointSeedTailFourteenPolynomialCoshRepresenter
    (q p : ℝ[X]) (s : ℝ) (x : ℝ) : ℝ :=
  fourCellEvenEndpointSeedTailFourteenRepresenter q x -
    s * (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift p x)

private theorem memLp_centeredPolynomialLift_two_restrict
    (q : ℝ[X]) :
    MemLp (centeredPolynomialLift q) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hq : Continuous (centeredPolynomialLift q) := by
    unfold centeredPolynomialLift
    fun_prop
  have hmeas : AEStronglyMeasurable (centeredPolynomialLift q)
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    hq.aestronglyMeasurable.restrict
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hcompact : IntegrableOn
      (fun x : ℝ ↦ ‖centeredPolynomialLift q x‖ ^ 2)
      (Icc (-1 : ℝ) 1) :=
    (hq.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact hcompact.mono_set Ioc_subset_Icc_self

private theorem memLp_fourCellEvenHalfWideCoshRepresenter_two_restrict :
    MemLp fourCellEvenHalfWideCoshRepresenter 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hcosh : Continuous fourCellEvenHalfWideCoshRepresenter := by
    unfold fourCellEvenHalfWideCoshRepresenter
    fun_prop
  have hmeas : AEStronglyMeasurable fourCellEvenHalfWideCoshRepresenter
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    hcosh.aestronglyMeasurable.restrict
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hcompact : IntegrableOn
      (fun x : ℝ ↦ ‖fourCellEvenHalfWideCoshRepresenter x‖ ^ 2)
      (Icc (-1 : ℝ) 1) :=
    (hcosh.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact hcompact.mono_set Ioc_subset_Icc_self

private theorem memLp_fourCellEvenEndpointSeedTailFourteenRepresenter_two_restrict
    (q : ℝ[X]) :
    MemLp (fourCellEvenEndpointSeedTailFourteenRepresenter q) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hG₀ :=
    memLp_fourCellEvenEndpointSeedProjectedTailRowRepresenter
      fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial
  have hP := memLp_centeredPolynomialLift_two_restrict q
  simpa only [fourCellEvenEndpointSeedTailFourteenRepresenter] using hG₀.sub hP

private theorem
    memLp_fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter_two_restrict
    (q : ℝ[X]) (s : ℝ) :
    MemLp (fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hG :=
    memLp_fourCellEvenEndpointSeedTailFourteenRepresenter_two_restrict q
  have hH := memLp_fourCellEvenHalfWideCoshRepresenter_two_restrict
  simpa only [fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
      hG.sub (hH.const_smul s)

private theorem intervalIntegrable_sq_of_memLp_two_restrict
    (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-1 : ℝ) 1))) :
    IntervalIntegrable (fun x : ℝ ↦ f x ^ 2) volume (-1) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  apply (hf.integrable_norm_pow (by norm_num)).congr
  filter_upwards with x
  rw [Real.norm_eq_abs, sq_abs]

theorem centeredRawLogEnergy_nonnegative (u : ℝ → ℝ) :
    0 ≤ centeredRawLogEnergy u := by
  unfold centeredRawLogEnergy
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x _hx
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro y _hy
  exact div_nonneg (sq_nonneg _) (abs_nonneg _)

/-- The four-cell regular correlation costs at most one quarter of centered
mass without any cosh or modal hypothesis.  This deliberately crude estimate
is used only above the fourteenth harmonic, where the singular diagonal has
ample room. -/
theorem fourCellRegularCorrelation_le_one_fourth_mass
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation w t) ≤
      (1 / 4 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let C : ℝ → ℝ := centeredEndpointCorrelation w
  let q : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t)
  have hC : Continuous C := by
    simpa only [C] using
      continuous_centeredEndpointCorrelation_of_continuous w hw
  have hqMeas : Measurable q := by
    dsimp only [q]
    exact measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)
  have hqBound : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ 1 / 4 := by
    intro t ht
    have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
      unfold fourCellOperatorHalfWidth
      positivity
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg ha0 ht.1
    have hargUpper : fourCellOperatorHalfWidth * t ≤
        5 * Real.log 2 / 4 := by
      calc
        fourCellOperatorHalfWidth * t ≤
            fourCellOperatorHalfWidth * 2 :=
          mul_le_mul_of_nonneg_left ht.2 ha0
        _ = 5 * Real.log 2 / 4 := by
          unfold fourCellOperatorHalfWidth
          ring
    have hq0 :=
      yoshidaRegularKernel_nonneg_fourCellRange harg0 hargUpper
    have hq1 := yoshidaRegularKernel_le_quarter harg0
    dsimp only [q]
    rw [abs_of_nonneg hq0]
    exact hq1
  have hqC : IntervalIntegrable (fun t ↦ q t * C t) volume 0 2 :=
    intervalIntegrable_boundedLag_mul_continuous q C hqMeas hC (1 / 4)
      hqBound
  have habs : IntervalIntegrable (fun t ↦ |q t * C t|) volume 0 2 :=
    hqC.abs
  have hmajor : IntervalIntegrable (fun t ↦ (1 / 4 : ℝ) * |C t|)
      volume 0 2 := (hC.abs.intervalIntegrable _ _).const_mul (1 / 4)
  have hmono : (∫ t : ℝ in 0..2, |q t * C t|) ≤
      ∫ t : ℝ in 0..2, (1 / 4 : ℝ) * |C t| := by
    apply intervalIntegral.integral_mono_on (by norm_num) habs hmajor
    intro t ht
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hqBound t ht) (abs_nonneg (C t))
  rw [intervalIntegral.integral_const_mul] at hmono
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (by norm_num : (0 : ℝ) ≤ 2) (f := fun t ↦ q t * C t)
      (μ := volume)
  have hL1 := integral_abs_centeredEndpointCorrelation_le_energy w hw
  have hself := le_abs_self (∫ t : ℝ in 0..2, q t * C t)
  simp only [Real.norm_eq_abs] at hnorm
  dsimp only [q, C] at hself hnorm hmono ⊢
  linarith

/-- After restoring the physical four-cell width, the unrestricted regular
loss is still below `217/1000` of mass. -/
theorem two_mul_fourCellWidth_mul_regularCorrelation_le_217_div_1000_mass
    (w : ℝ → ℝ) (hw : Continuous w) :
    2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation w t) ≤
      (217 / 1000 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let I : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation w t
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  have hI : I ≤ (1 / 4 : ℝ) * M := by
    simpa only [I, M] using fourCellRegularCorrelation_le_one_fourth_mass w hw
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hwidth0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hwidth : 2 * fourCellOperatorHalfWidth < (867 / 1000 : ℝ) := by
    have hlog := strict_log_two_bounds.2
    unfold fourCellOperatorHalfWidth
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hI hwidth0
  have hquarterM : 0 ≤ (1 / 4 : ℝ) * M := by positivity
  have hwidthScaled :=
    mul_le_mul_of_nonneg_right hwidth.le hquarterM
  dsimp only [I, M] at hscaled ⊢
  calc
    _ ≤ 2 * fourCellOperatorHalfWidth *
        ((1 / 4 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2)) := hscaled
    _ ≤ (867 / 1000 : ℝ) *
        ((1 / 4 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2)) :=
      hwidthScaled
    _ ≤ (217 / 1000 : ℝ) *
        (∫ x : ℝ in -1..1, w x ^ 2) := by
      dsimp only [M] at hM
      nlinarith only [hM]

/-- A genuine even `P₁₄+` tail retains two fifths of its raw
logarithmic energy in the complete polar-free operator.  The infinite block
is therefore quantitatively closed independently of the low bordered
certificate. -/
theorem two_fifths_rawEnergy_le_fourCellEvenPolarFreeOperator_of_tailFourteen
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (heven : Function.Even r)
    (hlow : centeredLegendreMomentsVanishBelow r 14) :
    (2 / 5 : ℝ) * (centeredRawLogEnergy r / 4) ≤
      fourCellEvenPolarFreeOperator r := by
  let M : ℝ := ∫ x : ℝ in -1..1, r x ^ 2
  let E : ℝ := centeredRawLogEnergy r / 4
  let S : ℝ := Real.log (2 * fourCellOperatorHalfWidth) +
    Real.eulerMascheroniConstant + Real.log Real.pi
  let I : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation r t
  let B : ℝ := fourCellEvenEndpointCapacityQuadratic r
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hB : 0 ≤ B := by
    simpa only [B] using
      fourCellEvenEndpointCapacityQuadratic_nonnegative r hr heven
  have hraw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    r hr hlocal 14 hlow
  have hgap : (1171733 / 360360 : ℝ) * M ≤ E := by
    norm_num [harmonic, Finset.sum_range_succ] at hraw
    simpa only [M, E, factorTwoIntrinsicEnergy] using hraw
  have hscalar : S * M ≤ (15787 / 10000 : ℝ) * M :=
    mul_le_mul_of_nonneg_right
      fourCellEndpointScalar_lt_15787_div_10000.le hM
  have hregular : 2 * fourCellOperatorHalfWidth * I ≤
      (217 / 1000 : ℝ) * M := by
    simpa only [I, M] using
      two_mul_fourCellWidth_mul_regularCorrelation_le_217_div_1000_mass
        r hr
  have hnormal :=
    fourCellEvenPolarFreeOperator_eq_coupledCore_sub_scalar_sub_regular_of_even
      r hr hlocal heven
  have hcore : fourCellEvenZeroCoshCoupledCore r = E + B := by
    dsimp only [E, B]
    unfold fourCellEvenZeroCoshCoupledCore
      fourCellEvenEndpointCapacityQuadratic
    ring
  have hbudget :
      (15787 / 10000 : ℝ) * M + (217 / 1000 : ℝ) * M ≤
        (3 / 5 : ℝ) * E := by
    linarith only [hgap, hM]
  rw [hnormal, hcore]
  change (2 / 5 : ℝ) * E ≤ E + B - S * M -
    2 * fourCellOperatorHalfWidth * I
  linarith only [hscalar, hregular, hB, hbudget]

private theorem natDegree_sub_smul_lt_fourteen
    (q p : ℝ[X]) (s : ℝ)
    (hq : q.natDegree < 14) (hp : p.natDegree < 14) :
    (q - s • p).natDegree < 14 := by
  have hsp : (s • p).natDegree < 14 :=
    (Polynomial.natDegree_smul_le s p).trans_lt hp
  exact lt_of_le_of_lt (Polynomial.natDegree_sub_le q (s • p))
    (max_lt hq hsp)

/-- Reparameterizing the polynomial selector turns the ambient half-cosh
direction into its class modulo degree-`<14` polynomials. -/
theorem fourCellEvenEndpointSeedTailFourteenPolynomialCoshRepresenter_eq_constrained
    (q p : ℝ[X]) (s x : ℝ) :
    fourCellEvenEndpointSeedTailFourteenPolynomialCoshRepresenter q p s x =
      fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter
        (q - s • p) s x := by
  unfold fourCellEvenEndpointSeedTailFourteenPolynomialCoshRepresenter
    fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter
    fourCellEvenEndpointSeedTailFourteenRepresenter centeredPolynomialLift
  simp only [Polynomial.eval_sub, Polynomial.eval_smul, smul_eq_mul]
  ring

/-- The complete projected endpoint row is genuinely linear on continuous
tails.  Keeping this identity at the row level lets us move finitely many
dangerous low-tail harmonics into the coupled finite block without applying
a triangle inequality. -/
theorem fourCellEvenEndpointSeedCanonicalTailRow_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellEvenEndpointSeedCanonicalTailRow (u + v) =
      fourCellEvenEndpointSeedCanonicalTailRow u +
        fourCellEvenEndpointSeedCanonicalTailRow v := by
  have hseed : Continuous fourCellEvenEndpointCoshSeed :=
    fourCellEvenEndpointCoshSeed_continuous
  have hcapacity := fourCellEvenEndpointCapacityPolarization_add_right
    fourCellEvenEndpointCoshSeed u v hseed hu hv
  have hmassU : IntervalIntegrable
      (fun x : ℝ ↦ fourCellEvenEndpointCoshSeed x * u x)
      volume (-1) 1 := (hseed.mul hu).intervalIntegrable _ _
  have hmassV : IntervalIntegrable
      (fun x : ℝ ↦ fourCellEvenEndpointCoshSeed x * v x)
      volume (-1) 1 := (hseed.mul hv).intervalIntegrable _ _
  have hmassAdd :
      (∫ x : ℝ in -1..1,
          fourCellEvenEndpointCoshSeed x * (u + v) x) =
        (∫ x : ℝ in -1..1,
          fourCellEvenEndpointCoshSeed x * u x) +
          ∫ x : ℝ in -1..1,
            fourCellEvenEndpointCoshSeed x * v x := by
    rw [show (fun x : ℝ ↦
        fourCellEvenEndpointCoshSeed x * (u + v) x) =
      fun x ↦ fourCellEvenEndpointCoshSeed x * u x +
        fourCellEvenEndpointCoshSeed x * v x by
      funext x
      simp only [Pi.add_apply]
      ring,
      intervalIntegral.integral_add hmassU hmassV]
  have hsigned := fourCellEvenSignedMassRegularPolarization_add_right
    fourCellEvenEndpointCoshSeed u v hseed hu hv
  unfold fourCellEvenSignedMassRegularPolarization at hsigned
  rw [hmassAdd] at hsigned
  unfold fourCellEvenEndpointSeedCanonicalTailRow
  rw [hcapacity]
  linear_combination -hsigned

/-- The finite row through degree twelve.  It is written as the old
`P₀/P₂/P₄/P₆` row plus the exact `P₈/P₁₀/P₁₂` slice, so no individual mode
is estimated or enumerated. -/
def fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ :=
  fourCellEvenEndpointSeedCanonicalLowRow w hw +
    fourCellEvenEndpointSeedCanonicalTailRow
      (centeredLegendreHigherResidual w hw 8 -
        centeredLegendreHigherResidual w hw 14)

/-- The added `8..13` slice is literally the difference of two finite
Legendre projections.  This certifies that the new low row is genuinely
finite-dimensional rather than merely named that way. -/
theorem centeredLegendreHigherResidual_eight_sub_fourteen_eq_lowProjection_sub
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredLegendreHigherResidual w hw 8 -
        centeredLegendreHigherResidual w hw 14 =
      centeredLegendreLowProjection w hw 14 -
        centeredLegendreLowProjection w hw 8 := by
  funext x
  unfold centeredLegendreHigherResidual
  simp only [Pi.sub_apply]
  ring

theorem fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow_eq_finiteProjection
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw =
      fourCellEvenEndpointSeedCanonicalLowRow w hw +
        fourCellEvenEndpointSeedCanonicalTailRow
          (centeredLegendreLowProjection w hw 14 -
            centeredLegendreLowProjection w hw 8) := by
  unfold fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow
  rw [centeredLegendreHigherResidual_eight_sub_fourteen_eq_lowProjection_sub]

/-- The endpoint-seed row splits exactly into a finite block through
`P₁₂` and a genuine `P₁₄+` tail.  This is the structural cutoff at which the
harmonic estimate below applies; no Young loss has yet been taken. -/
theorem fourCellEvenEndpointSeedRow_eq_canonicalLowThroughTwelve_add_tailFourteen
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0) :
    fourCellEvenEndpointSeedRow w =
      fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw +
        fourCellEvenEndpointSeedCanonicalTailRow
          (centeredLegendreHigherResidual w hw 14) := by
  let r₈ : ℝ → ℝ := centeredLegendreHigherResidual w hw 8
  let r₁₄ : ℝ → ℝ := centeredLegendreHigherResidual w hw 14
  let m : ℝ → ℝ := r₈ - r₁₄
  have hr₈ : Continuous r₈ := by
    simpa only [r₈] using continuous_centeredLegendreHigherResidual w hw 8
  have hr₁₄ : Continuous r₁₄ := by
    simpa only [r₁₄] using continuous_centeredLegendreHigherResidual w hw 14
  have hm : Continuous m := by
    simpa only [m] using hr₈.sub hr₁₄
  have hsplit : m + r₁₄ = r₈ := by
    funext x
    dsimp only [m]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have htailAdd :=
    fourCellEvenEndpointSeedCanonicalTailRow_add m r₁₄ hm hr₁₄
  rw [hsplit] at htailAdd
  have hrow := fourCellEvenEndpointSeedRow_eq_canonicalCutoffEightLow_add_tail
    w hw hlocal heven hzero
  have hrow' : fourCellEvenEndpointSeedRow w =
      fourCellEvenEndpointSeedCanonicalLowRow w hw +
        fourCellEvenEndpointSeedCanonicalTailRow r₈ := by
    dsimp only [r₈, fourCellEvenEndpointSeedCanonicalLowRow,
      fourCellEvenEndpointSeedCanonicalTailRow]
    simpa only [sub_eq_add_neg, add_assoc] using hrow
  dsimp only [fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow]
  dsimp only [m, r₈, r₁₄] at htailAdd
  rw [hrow', htailAdd]
  ring

/-- The canonical combined representer satisfies the sharper rational norm
bound used before the final multiplication by the seed pivot. -/
theorem integral_endpointSeedProjectedTailRowRepresenter_canonical_sq_le_rational :
    (∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedProjectedTailRowRepresenter
        fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial x ^ 2) ≤
      fourCellEvenEndpointSeedCanonicalTailNormBudget := by
  let a : ℝ := fourCellOperatorHalfWidth
  let A : ℝ → ℝ := fourCellEvenEndpointSeedProjectedCapacityRepresenter
  let E : ℝ → ℝ := fourCellEndpointSeedRegularRemainderRepresenter
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlogUpper : Real.log 2 ≤ (6932 / 10000 : ℝ) :=
    strict_log_two_bounds.2.le
  have hlogSq : Real.log 2 ^ 2 ≤ (6932 / 10000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlog0 hlogUpper 2
  have haSq : a ^ 2 ≤ (19 / 100 : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hlogSq
      (by norm_num : (0 : ℝ) ≤ 25 / 64)
    calc
      a ^ 2 = (25 / 64 : ℝ) * Real.log 2 ^ 2 := by
        dsimp only [a]
        unfold fourCellOperatorHalfWidth
        ring
      _ ≤ (25 / 64 : ℝ) * (6932 / 10000 : ℝ) ^ 2 := hscaled
      _ ≤ (19 / 100 : ℝ) := by norm_num
  have hA : MemLp A 2 (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [A] using memLp_fourCellEvenEndpointSeedProjectedCapacityRepresenter
  have hE : MemLp E 2 (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [E] using memLp_fourCellEndpointSeedRegularRemainderRepresenter
  have hAnorm : (∫ x : ℝ in -1..1, A x ^ 2) ≤ (21 / 100000 : ℝ) := by
    simpa only [A] using integral_endpointSeedProjectedCapacityRepresenter_sq_le
  have hEnorm : (∫ x : ℝ in -1..1, E x ^ 2) ≤ (1 / 245000 : ℝ) := by
    simpa only [E] using
      integral_fourCellEndpointSeedRegularRemainderRepresenter_sq_le
  have hEnonneg : 0 ≤ ∫ x : ℝ in -1..1, E x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hyoung := integral_sub_const_mul_sq_le_five_four_add_five
    A E a hA hE
  have hAterm :
      (5 / 4 : ℝ) * (∫ x : ℝ in -1..1, A x ^ 2) ≤
        (5 / 4 : ℝ) * (21 / 100000) :=
    mul_le_mul_of_nonneg_left hAnorm (by norm_num)
  have hEterm :
      5 * a ^ 2 * (∫ x : ℝ in -1..1, E x ^ 2) ≤
        5 * (19 / 100 : ℝ) * (1 / 245000) := by
    calc
      5 * a ^ 2 * (∫ x : ℝ in -1..1, E x ^ 2) ≤
          5 * (19 / 100 : ℝ) * (∫ x : ℝ in -1..1, E x ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left haSq (by norm_num)) hEnonneg
      _ ≤ 5 * (19 / 100 : ℝ) * (1 / 245000) :=
        mul_le_mul_of_nonneg_left hEnorm (by norm_num)
  have hpointwise : ∀ x ∈ Icc (-1 : ℝ) 1,
      fourCellEvenEndpointSeedProjectedTailRowRepresenter
          fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial x =
        A x - a * E x := by
    intro x hx
    dsimp only [A, a, E]
    rw [endpointSeedProjectedTailRowRepresenter_canonical_eq,
      fourCellEvenEndpointSeedRegularTailRepresenter_sub_selector_eq_remainder
        hx]
  calc
    (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedProjectedTailRowRepresenter
          fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial x ^ 2) =
      ∫ x : ℝ in -1..1, (A x - a * E x) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
        change
          fourCellEvenEndpointSeedProjectedTailRowRepresenter
              fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial x ^ 2 =
            (A x - a * E x) ^ 2
        rw [hpointwise x hx]
    _ ≤ (5 / 4 : ℝ) * (∫ x : ℝ in -1..1, A x ^ 2) +
        5 * a ^ 2 * (∫ x : ℝ in -1..1, E x ^ 2) := hyoung
    _ ≤ (5 / 4 : ℝ) * (21 / 100000) +
        5 * (19 / 100 : ℝ) * (1 / 245000) :=
      add_le_add hAterm hEterm
    _ = fourCellEvenEndpointSeedCanonicalTailNormBudget := by
      norm_num [fourCellEvenEndpointSeedCanonicalTailNormBudget]

/-- The zero additional selector recovers the already-certified canonical
representer as a valid cutoff-fourteen dual bound. -/
theorem integral_endpointSeedTailFourteenRepresenter_zero_sq_le_rational :
    (∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenRepresenter 0 x ^ 2) ≤
      fourCellEvenEndpointSeedCanonicalTailNormBudget := by
  simpa only [fourCellEvenEndpointSeedTailFourteenRepresenter,
    centeredPolynomialLift, Polynomial.eval_zero, sub_zero] using
      integral_endpointSeedProjectedTailRowRepresenter_canonical_sq_le_rational

/-- Cauchy closure of the complete endpoint tail row, with no zero-cosh or
endpoint-trace hypothesis on the tail itself. -/
theorem fourCellEvenEndpointSeedCanonicalTailRow_sq_le_rational_mass
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlow : centeredLegendreMomentsVanishBelow r 8) :
    fourCellEvenEndpointSeedCanonicalTailRow r ^ 2 ≤
      fourCellEvenEndpointSeedCanonicalTailNormBudget *
        (∫ x : ℝ in -1..1, r x ^ 2) := by
  simpa only [fourCellEvenEndpointSeedCanonicalTailRow] using
    fourCellEvenEndpointSeedTailRow_sq_le_mass_of_projectedRepresenterNorm
      r hr hlow fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial
      natDegree_fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial_lt_eight
      (memLp_fourCellEvenEndpointSeedProjectedTailRowRepresenter
        fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial)
      fourCellEvenEndpointSeedCanonicalTailNormBudget
      integral_endpointSeedProjectedTailRowRepresenter_canonical_sq_le_rational

/-- Exact pairing identity after any additional degree-`< 14` selector is
removed.  This is the equality underlying the refined Cauchy theorem below. -/
theorem fourCellEvenEndpointSeedCanonicalTailRow_eq_tailFourteenRepresenterPairing
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlow : centeredLegendreMomentsVanishBelow r 14)
    (q : ℝ[X]) (hq : q.natDegree < 14) :
    fourCellEvenEndpointSeedCanonicalTailRow r =
      ∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenRepresenter q x * r x := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  let G₀ : ℝ → ℝ :=
    fourCellEvenEndpointSeedProjectedTailRowRepresenter
      fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial
  let P : ℝ → ℝ := centeredPolynomialLift q
  have hlowEight : centeredLegendreMomentsVanishBelow r 8 := by
    intro n hn
    exact hlow n (by omega)
  have hG₀ : MemLp G₀ 2 μ := by
    simpa only [G₀, μ] using
      memLp_fourCellEvenEndpointSeedProjectedTailRowRepresenter
        fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial
  have hP : MemLp P 2 μ := by
    simpa only [P, μ] using memLp_centeredPolynomialLift_two_restrict q
  have hrMeas : AEStronglyMeasurable r μ :=
    hr.aestronglyMeasurable.restrict
  have hrLp : MemLp r 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hrMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖r x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hr.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hG₀r : IntervalIntegrable (fun x : ℝ ↦ G₀ x * r x)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact (hrLp.mul' hG₀ : MemLp (fun x : ℝ ↦ G₀ x * r x) 1 μ).integrable
      (by norm_num)
  have hPr : IntervalIntegrable (fun x : ℝ ↦ P x * r x)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact (hrLp.mul' hP : MemLp (fun x : ℝ ↦ P x * r x) 1 μ).integrable
      (by norm_num)
  have hpoly : (∫ x : ℝ in -1..1, P x * r x) = 0 := by
    simpa only [P] using
      intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
        q r hr hlow hq
  have hbase :=
    fourCellEvenEndpointSeedTailRow_eq_projectedRepresenterPairing
      r hr hlowEight
      fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial
      natDegree_fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial_lt_eight
  change fourCellEvenEndpointSeedCanonicalTailRow r = _ at hbase
  calc
    fourCellEvenEndpointSeedCanonicalTailRow r =
        ∫ x : ℝ in -1..1, G₀ x * r x := by
      simpa only [G₀] using hbase
    _ = (∫ x : ℝ in -1..1, G₀ x * r x) -
        ∫ x : ℝ in -1..1, P x * r x := by rw [hpoly, sub_zero]
    _ = ∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenRepresenter q x * r x := by
      rw [← intervalIntegral.integral_sub hG₀r hPr]
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [G₀, P,
        fourCellEvenEndpointSeedTailFourteenRepresenter]
      ring

/-- On an even profile the half-cosh representer pairs to exactly the
positive-half wide-cosh coordinate. -/
theorem integral_fourCellEvenHalfWideCoshRepresenter_mul_eq_positiveCoshMoment
    (r : ℝ → ℝ) (hr : Continuous r) (heven : Function.Even r) :
    (∫ x : ℝ in -1..1,
      fourCellEvenHalfWideCoshRepresenter x * r x) =
      fourCellPositiveCoshMoment r (fourCellOperatorHalfWidth / 2) := by
  have hcenter := centeredCoshMoment_eq_two_mul_positive_of_even
    r hr heven (fourCellOperatorHalfWidth / 2)
  calc
    (∫ x : ℝ in -1..1,
        fourCellEvenHalfWideCoshRepresenter x * r x) =
        (1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
          Real.cosh ((fourCellOperatorHalfWidth / 2) * x) * r x := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _hx
      unfold fourCellEvenHalfWideCoshRepresenter
      ring
    _ = fourCellPositiveCoshMoment r
          (fourCellOperatorHalfWidth / 2) := by
      unfold centeredCoshMoment at hcenter
      linarith

/-- Exact constrained tail pairing.  A multiple of the wide-cosh
representer is removed from the Riesz density and reappears only as the
corresponding scalar coordinate. -/
theorem fourCellEvenEndpointSeedCanonicalTailRow_eq_constrainedPairing_add_cosh
    (r : ℝ → ℝ) (hr : Continuous r) (heven : Function.Even r)
    (hlow : centeredLegendreMomentsVanishBelow r 14)
    (q : ℝ[X]) (hq : q.natDegree < 14) (s : ℝ) :
    fourCellEvenEndpointSeedCanonicalTailRow r =
      (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s x *
          r x) +
        s * fourCellPositiveCoshMoment r
          (fourCellOperatorHalfWidth / 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  let G : ℝ → ℝ := fourCellEvenEndpointSeedTailFourteenRepresenter q
  let H : ℝ → ℝ := fourCellEvenHalfWideCoshRepresenter
  have hG₀ : MemLp
      (fourCellEvenEndpointSeedProjectedTailRowRepresenter
        fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial) 2 μ := by
    simpa only [μ] using
      memLp_fourCellEvenEndpointSeedProjectedTailRowRepresenter
        fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial
  have hP : MemLp (centeredPolynomialLift q) 2 μ := by
    simpa only [μ] using memLp_centeredPolynomialLift_two_restrict q
  have hG : MemLp G 2 μ := by
    simpa only [G, fourCellEvenEndpointSeedTailFourteenRepresenter] using
      hG₀.sub hP
  have hrMeas : AEStronglyMeasurable r μ :=
    hr.aestronglyMeasurable.restrict
  have hrLp : MemLp r 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hrMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖r x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hr.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hGr : IntervalIntegrable (fun x : ℝ ↦ G x * r x)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact (hrLp.mul' hG : MemLp (fun x : ℝ ↦ G x * r x) 1 μ).integrable
      (by norm_num)
  have hHr : IntervalIntegrable (fun x : ℝ ↦ H x * r x)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [H, fourCellEvenHalfWideCoshRepresenter]
    fun_prop
  have hpair :=
    fourCellEvenEndpointSeedCanonicalTailRow_eq_tailFourteenRepresenterPairing
      r hr hlow q hq
  have hcosh :=
    integral_fourCellEvenHalfWideCoshRepresenter_mul_eq_positiveCoshMoment
      r hr heven
  rw [hpair]
  rw [show (fun x : ℝ ↦
      fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s x *
        r x) =
      fun x ↦ G x * r x - s * (H x * r x) by
    funext x
    dsimp only [G, H,
      fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter]
    ring,
    intervalIntegral.integral_sub hGr (hHr.const_mul s),
    intervalIntegral.integral_const_mul]
  rw [hcosh]
  ring

/-- Lossless finite--tail row decomposition after quotienting by the actual
zero-wide-cosh constraint.  The selector parameter `s` shifts the finite
`P₀..P₁₂` row and the infinite representer in opposite directions;
their sum is unchanged because the full profile has zero cosh coordinate.
This is the coupled alternative to any fixed Young allocation. -/
theorem fourCellEvenEndpointSeedRow_eq_coshConstrainedLowThroughTwelve_add_tailPairing
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (q : ℝ[X]) (hq : q.natDegree < 14) (s : ℝ) :
    fourCellEvenEndpointSeedRow w =
      (fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw -
        s * fourCellPositiveCoshMoment
          (centeredLegendreLowProjection w hw 14)
          (fourCellOperatorHalfWidth / 2)) +
        ∫ x : ℝ in -1..1,
          fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s x *
            centeredLegendreHigherResidual w hw 14 x := by
  let p : ℝ → ℝ := centeredLegendreLowProjection w hw 14
  let r : ℝ → ℝ := centeredLegendreHigherResidual w hw 14
  have hp : Continuous p := by
    simpa only [p] using continuous_centeredLegendreLowProjection w hw 14
  have hr : Continuous r := by
    simpa only [r] using continuous_centeredLegendreHigherResidual w hw 14
  have hpEven : Function.Even p := by
    simpa only [p] using centeredLegendreLowProjection_even w hw heven 14
  have hrEven : Function.Even r := by
    simpa only [r] using centeredLegendreHigherResidual_even w hw heven 14
  have hrGap : centeredLegendreMomentsVanishBelow r 14 := by
    simpa only [r] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 14
  have hsum : p + r = w := by
    simpa only [p, r] using
      centeredLegendreLowProjection_add_higherResidual w hw 14
  let lambda : ℝ := fourCellOperatorHalfWidth / 2
  have hpInt : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (lambda * x) * p x) volume 0 1 :=
    ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).mul hp)
      |>.intervalIntegrable _ _
  have hrInt : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (lambda * x) * r x) volume 0 1 :=
    ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).mul hr)
      |>.intervalIntegrable _ _
  have hCadd : fourCellPositiveCoshMoment (p + r) lambda =
      fourCellPositiveCoshMoment p lambda +
        fourCellPositiveCoshMoment r lambda := by
    unfold fourCellPositiveCoshMoment
    rw [show (fun x : ℝ ↦ Real.cosh (lambda * x) * (p + r) x) =
      fun x ↦ Real.cosh (lambda * x) * p x +
        Real.cosh (lambda * x) * r x by
      funext x
      simp only [Pi.add_apply]
      ring,
      intervalIntegral.integral_add hpInt hrInt]
  rw [hsum] at hCadd
  have hCzero : fourCellPositiveCoshMoment p lambda +
      fourCellPositiveCoshMoment r lambda = 0 := by
    dsimp only [lambda] at hCadd
    linarith only [hCadd, hzero]
  have hrow :=
    fourCellEvenEndpointSeedRow_eq_canonicalLowThroughTwelve_add_tailFourteen
      w hw hlocal heven hzero
  have htail :=
    fourCellEvenEndpointSeedCanonicalTailRow_eq_constrainedPairing_add_cosh
      r hr hrEven hrGap q hq s
  dsimp only [r] at htail
  rw [hrow, htail]
  dsimp only [p, r, lambda] at hCzero ⊢
  linear_combination s * hCzero

/-- Cauchy closure for the row density after quotienting by both the low
polynomial space and the wide-cosh constraint.  This estimate is deliberately
stated for the pairing itself: unlike the unconstrained tail-row estimate, it
does not put the removed cosh coordinate back into the infinite block. -/
theorem integral_endpointSeedTailFourteenConstrainedRepresenter_mul_sq_le_mass_of_norm
    (r : ℝ → ℝ) (hr : Continuous r)
    (q : ℝ[X]) (s C : ℝ)
    (hdual :
      (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s x ^ 2) ≤
          C) :
    (∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s x * r x) ^ 2 ≤
        C * (∫ x : ℝ in -1..1, r x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  let G : ℝ → ℝ :=
    fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s
  have hG : MemLp G 2 μ := by
    simpa only [G, μ] using
      memLp_fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter_two_restrict
        q s
  have hrMeas : AEStronglyMeasurable r μ :=
    hr.aestronglyMeasurable.restrict
  have hrLp : MemLp r 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hrMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖r x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hr.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hcauchy :=
    YoshidaEndpointWeightedCauchy.sq_integral_mul_le_weighted
      μ (fun _ : ℝ ↦ 1) G r (by simp)
        (by simpa only [div_one, Real.sqrt_one] using hG)
        (by simpa only [Real.sqrt_one, one_mul] using hrLp)
  have hcauchy' :
      (∫ x : ℝ in -1..1, G x * r x) ^ 2 ≤
        (∫ x : ℝ in -1..1, G x ^ 2) *
          (∫ x : ℝ in -1..1, r x ^ 2) := by
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa only [μ, div_one, one_mul] using hcauchy
  have hR : 0 ≤ ∫ x : ℝ in -1..1, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hdualScaled := mul_le_mul_of_nonneg_right hdual hR
  dsimp only [G] at hcauchy'
  exact hcauchy'.trans hdualScaled

/-- The quotient pairing is paid directly by the retained `P₁₄+`
singular logarithmic energy.  The wide-cosh constraint has already been
removed from its Riesz density, so its norm budget `C` is the norm in the
actual constrained tail quotient rather than in the ambient `L²` space. -/
theorem harmonic_fourteen_mul_endpointSeedTailFourteenConstrainedPairing_sq_le_raw_of_norm
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (hlow : centeredLegendreMomentsVanishBelow r 14)
    (q : ℝ[X]) (s C : ℝ) (hC : 0 ≤ C)
    (hdual :
      (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s x ^ 2) ≤
          C) :
    (harmonic 14 : ℝ) *
        (∫ x : ℝ in -1..1,
          fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s x * r x) ^ 2 ≤
      C * (centeredRawLogEnergy r / 4) := by
  have hpair :=
    integral_endpointSeedTailFourteenConstrainedRepresenter_mul_sq_le_mass_of_norm
      r hr q s C hdual
  have hraw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    r hr hlocal 14 hlow
  have hH : 0 ≤ (harmonic 14 : ℝ) := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hpairScaled := mul_le_mul_of_nonneg_left hpair hH
  have hrawScaled := mul_le_mul_of_nonneg_left hraw hC
  unfold factorTwoIntrinsicEnergy at hrawScaled
  nlinarith only [hpairScaled, hrawScaled]

/-- Exact quadratic norm of the cosh-quotiented tail density.  This is the
one-dimensional Gram border that remains after the polynomial quotient; its
three entries are kept as genuine inner products rather than independently
estimated absolute values. -/
theorem integral_endpointSeedTailFourteenConstrainedRepresenter_sq_eq_quadratic
    (q : ℝ[X]) (s : ℝ) :
    (∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s x ^ 2) =
      (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2) -
        2 * s * (∫ x : ℝ in -1..1,
          fourCellEvenEndpointSeedTailFourteenRepresenter q x *
            fourCellEvenHalfWideCoshRepresenter x) +
        s ^ 2 * (∫ x : ℝ in -1..1,
          fourCellEvenHalfWideCoshRepresenter x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  let G : ℝ → ℝ := fourCellEvenEndpointSeedTailFourteenRepresenter q
  let H : ℝ → ℝ := fourCellEvenHalfWideCoshRepresenter
  have hG : MemLp G 2 μ := by
    simpa only [G, μ] using
      memLp_fourCellEvenEndpointSeedTailFourteenRepresenter_two_restrict q
  have hH : MemLp H 2 μ := by
    simpa only [H, μ] using
      memLp_fourCellEvenHalfWideCoshRepresenter_two_restrict
  have hGsq : IntervalIntegrable (fun x : ℝ ↦ G x ^ 2)
      volume (-1) 1 := by
    exact intervalIntegrable_sq_of_memLp_two_restrict G
      (by simpa only [μ] using hG)
  have hHsq : IntervalIntegrable (fun x : ℝ ↦ H x ^ 2)
      volume (-1) 1 := by
    exact intervalIntegrable_sq_of_memLp_two_restrict H
      (by simpa only [μ] using hH)
  have hGH : IntervalIntegrable (fun x : ℝ ↦ G x * H x)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact (hH.mul' hG : MemLp (fun x : ℝ ↦ G x * H x) 1 μ).integrable
      (by norm_num)
  calc
    (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s x ^ 2) =
        ∫ x : ℝ in -1..1,
          G x ^ 2 - (2 * s) * (G x * H x) + s ^ 2 * H x ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [G, H,
        fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter]
      ring
    _ = (∫ x : ℝ in -1..1, G x ^ 2) -
          2 * s * (∫ x : ℝ in -1..1, G x * H x) +
          s ^ 2 * (∫ x : ℝ in -1..1, H x ^ 2) := by
      rw [intervalIntegral.integral_add
          (hGsq.sub (hGH.const_mul (2 * s))) (hHsq.const_mul (s ^ 2)),
        intervalIntegral.integral_sub hGsq (hGH.const_mul (2 * s)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ = (∫ x : ℝ in -1..1,
          fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2) -
        2 * s * (∫ x : ℝ in -1..1,
          fourCellEvenEndpointSeedTailFourteenRepresenter q x *
            fourCellEvenHalfWideCoshRepresenter x) +
        s ^ 2 * (∫ x : ℝ in -1..1,
          fourCellEvenHalfWideCoshRepresenter x ^ 2) := by
      dsimp only [G, H]

/-- Exact Gram expansion after also quotienting the cosh direction by an
arbitrary degree-bounded polynomial.  This is the norm relevant to a genuine
`P₁₄+` tail; no norm of an already-annihilated low cosh coordinate remains. -/
theorem integral_endpointSeedTailFourteenPolynomialCoshRepresenter_sq_eq_quadratic
    (q p : ℝ[X]) (s : ℝ) :
    (∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenPolynomialCoshRepresenter q p s x ^ 2) =
      (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2) -
        2 * s * (∫ x : ℝ in -1..1,
          fourCellEvenEndpointSeedTailFourteenRepresenter q x *
            (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift p x)) +
        s ^ 2 * (∫ x : ℝ in -1..1,
          (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift p x) ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  let G : ℝ → ℝ := fourCellEvenEndpointSeedTailFourteenRepresenter q
  let H : ℝ → ℝ := fourCellEvenHalfWideCoshRepresenter
  let P : ℝ → ℝ := centeredPolynomialLift p
  let J : ℝ → ℝ := fun x ↦ H x - P x
  have hG : MemLp G 2 μ := by
    simpa only [G, μ] using
      memLp_fourCellEvenEndpointSeedTailFourteenRepresenter_two_restrict q
  have hH : MemLp H 2 μ := by
    simpa only [H, μ] using
      memLp_fourCellEvenHalfWideCoshRepresenter_two_restrict
  have hP : MemLp P 2 μ := by
    simpa only [P, μ] using memLp_centeredPolynomialLift_two_restrict p
  have hJ : MemLp J 2 μ := by
    simpa only [J, Pi.sub_apply] using hH.sub hP
  have hGsq : IntervalIntegrable (fun x : ℝ ↦ G x ^ 2)
      volume (-1) 1 := by
    exact intervalIntegrable_sq_of_memLp_two_restrict G
      (by simpa only [μ] using hG)
  have hJsq : IntervalIntegrable (fun x : ℝ ↦ J x ^ 2)
      volume (-1) 1 := by
    exact intervalIntegrable_sq_of_memLp_two_restrict J
      (by simpa only [μ] using hJ)
  have hGJ : IntervalIntegrable (fun x : ℝ ↦ G x * J x)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact (hJ.mul' hG : MemLp (fun x : ℝ ↦ G x * J x) 1 μ).integrable
      (by norm_num)
  calc
    (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenPolynomialCoshRepresenter q p s x ^ 2) =
        ∫ x : ℝ in -1..1,
          G x ^ 2 - (2 * s) * (G x * J x) + s ^ 2 * J x ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [G, H, P, J,
        fourCellEvenEndpointSeedTailFourteenPolynomialCoshRepresenter]
      ring
    _ = (∫ x : ℝ in -1..1, G x ^ 2) -
          2 * s * (∫ x : ℝ in -1..1, G x * J x) +
          s ^ 2 * (∫ x : ℝ in -1..1, J x ^ 2) := by
      rw [intervalIntegral.integral_add
          (hGsq.sub (hGJ.const_mul (2 * s))) (hJsq.const_mul (s ^ 2)),
        intervalIntegral.integral_sub hGsq (hGJ.const_mul (2 * s)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ = (∫ x : ℝ in -1..1,
          fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2) -
        2 * s * (∫ x : ℝ in -1..1,
          fourCellEvenEndpointSeedTailFourteenRepresenter q x *
            (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift p x)) +
        s ^ 2 * (∫ x : ℝ in -1..1,
          (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift p x) ^ 2) := by
      dsimp only [G, H, P, J]

/-- Positivity of the reduced two-vector tail Gram.  This is the only fact
needed to handle a possibly degenerate polynomial-reduced cosh direction. -/
theorem sq_integral_endpointSeedTailFourteenRepresenter_mul_polynomialCosh_le_gram
    (q p : ℝ[X]) :
    (∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenRepresenter q x *
        (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift p x)) ^ 2 ≤
      (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2) *
        (∫ x : ℝ in -1..1,
          (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift p x) ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  let G : ℝ → ℝ := fourCellEvenEndpointSeedTailFourteenRepresenter q
  let J : ℝ → ℝ := fun x ↦
    fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift p x
  have hG : MemLp G 2 μ := by
    simpa only [G, μ] using
      memLp_fourCellEvenEndpointSeedTailFourteenRepresenter_two_restrict q
  have hH : MemLp fourCellEvenHalfWideCoshRepresenter 2 μ := by
    simpa only [μ] using
      memLp_fourCellEvenHalfWideCoshRepresenter_two_restrict
  have hP : MemLp (centeredPolynomialLift p) 2 μ := by
    simpa only [μ] using memLp_centeredPolynomialLift_two_restrict p
  have hJ : MemLp J 2 μ := by
    simpa only [J, Pi.sub_apply] using hH.sub hP
  have hcauchy :=
    YoshidaEndpointWeightedCauchy.sq_integral_mul_le_weighted
      μ (fun _ : ℝ ↦ 1) G J (by simp)
        (by simpa only [div_one, Real.sqrt_one] using hG)
        (by simpa only [Real.sqrt_one, one_mul] using hJ)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa only [μ, G, J, div_one, one_mul] using hcauchy

/-- The canonical endpoint row is almost orthogonal to the true cosh
direction in the `P₁₄+` quotient.  The estimate is a two-vector Gram
consequence of the canonical row budget and the quadratic Taylor remainder;
no cosh integral is numerically evaluated. -/
theorem abs_integral_endpointSeedTailFourteenRepresenter_zero_mul_quadraticCoshRemainder_le :
    |∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenRepresenter 0 x *
        (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift
          fourCellEvenHalfWideCoshQuadraticSelectorPolynomial x)| ≤
      (1 / 400000 : ℝ) := by
  let B : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenEndpointSeedTailFourteenRepresenter 0 x *
      (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift
        fourCellEvenHalfWideCoshQuadraticSelectorPolynomial x)
  let A : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenEndpointSeedTailFourteenRepresenter 0 x ^ 2
  let D : ℝ := ∫ x : ℝ in -1..1,
    (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift
      fourCellEvenHalfWideCoshQuadraticSelectorPolynomial x) ^ 2
  have hgram : B ^ 2 ≤ A * D := by
    simpa only [A, B, D] using
      sq_integral_endpointSeedTailFourteenRepresenter_mul_polynomialCosh_le_gram
        0 fourCellEvenHalfWideCoshQuadraticSelectorPolynomial
  have hA : A ≤ fourCellEvenEndpointSeedCanonicalTailNormBudget := by
    simpa only [A] using
      integral_endpointSeedTailFourteenRepresenter_zero_sq_le_rational
  have hD : D ≤ (1 / 50000000 : ℝ) := by
    simpa only [D] using integral_halfWideCosh_sub_quadraticSelector_sq_le
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hAD : A * D ≤
      fourCellEvenEndpointSeedCanonicalTailNormBudget *
        (1 / 50000000 : ℝ) := by
    exact mul_le_mul hA hD hD0
      (by
        norm_num [fourCellEvenEndpointSeedCanonicalTailNormBudget])
  have hBsq : B ^ 2 ≤ (1 / 400000 : ℝ) ^ 2 := by
    calc
      B ^ 2 ≤ A * D := hgram
      _ ≤ fourCellEvenEndpointSeedCanonicalTailNormBudget *
          (1 / 50000000 : ℝ) := hAD
      _ ≤ (1 / 400000 : ℝ) ^ 2 := by
        norm_num [fourCellEvenEndpointSeedCanonicalTailNormBudget]
  have habsSq : |B| ^ 2 ≤ (1 / 400000 : ℝ) ^ 2 := by
    simpa only [sq_abs] using hBsq
  have htarget : |B| ≤ (1 / 400000 : ℝ) := by
    nlinarith only [habsSq, abs_nonneg B]
  simpa only [B] using htarget

/-- A genuine `P₁₄+` cosh coordinate sees only the quadratic Taylor
remainder.  Its square is therefore controlled by the tiny quotient pivot
times tail mass, with no transcendental evaluation. -/
theorem positiveCoshMoment_sq_le_quadraticCoshRemainderNorm_mul_mass_of_tailFourteen
    (r : ℝ → ℝ) (hr : Continuous r) (heven : Function.Even r)
    (hlow : centeredLegendreMomentsVanishBelow r 14) :
    fourCellPositiveCoshMoment r (fourCellOperatorHalfWidth / 2) ^ 2 ≤
      (∫ x : ℝ in -1..1,
        (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift
          fourCellEvenHalfWideCoshQuadraticSelectorPolynomial x) ^ 2) *
        (∫ x : ℝ in -1..1, r x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  let H : ℝ → ℝ := fourCellEvenHalfWideCoshRepresenter
  let P : ℝ → ℝ :=
    centeredPolynomialLift fourCellEvenHalfWideCoshQuadraticSelectorPolynomial
  let J : ℝ → ℝ := fun x ↦ H x - P x
  have hH : MemLp H 2 μ := by
    simpa only [H, μ] using
      memLp_fourCellEvenHalfWideCoshRepresenter_two_restrict
  have hP : MemLp P 2 μ := by
    simpa only [P, μ] using
      memLp_centeredPolynomialLift_two_restrict
        fourCellEvenHalfWideCoshQuadraticSelectorPolynomial
  have hJ : MemLp J 2 μ := by
    simpa only [J, Pi.sub_apply] using hH.sub hP
  have hrMeas : AEStronglyMeasurable r μ :=
    hr.aestronglyMeasurable.restrict
  have hrLp : MemLp r 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hrMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖r x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hr.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hcauchy :=
    YoshidaEndpointWeightedCauchy.sq_integral_mul_le_weighted
      μ (fun _ : ℝ ↦ 1) J r (by simp)
        (by simpa only [div_one, Real.sqrt_one] using hJ)
        (by simpa only [Real.sqrt_one, one_mul] using hrLp)
  have hcauchy' :
      (∫ x : ℝ in -1..1, J x * r x) ^ 2 ≤
        (∫ x : ℝ in -1..1, J x ^ 2) *
          (∫ x : ℝ in -1..1, r x ^ 2) := by
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa only [μ, div_one, one_mul] using hcauchy
  have hpoly : (∫ x : ℝ in -1..1, P x * r x) = 0 := by
    simpa only [P] using
      intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
        fourCellEvenHalfWideCoshQuadraticSelectorPolynomial r hr hlow
          natDegree_fourCellEvenHalfWideCoshQuadraticSelectorPolynomial_lt_fourteen
  have hHcont : Continuous H := by
    dsimp only [H]
    unfold fourCellEvenHalfWideCoshRepresenter
    fun_prop
  have hPcont : Continuous P := by
    dsimp only [P]
    unfold centeredPolynomialLift
    fun_prop
  have hHr : IntervalIntegrable (fun x : ℝ ↦ H x * r x)
      volume (-1) 1 := (hHcont.mul hr).intervalIntegrable _ _
  have hPr : IntervalIntegrable (fun x : ℝ ↦ P x * r x)
      volume (-1) 1 := (hPcont.mul hr).intervalIntegrable _ _
  have hcosh :=
    integral_fourCellEvenHalfWideCoshRepresenter_mul_eq_positiveCoshMoment
      r hr heven
  have hpair : (∫ x : ℝ in -1..1, J x * r x) =
      fourCellPositiveCoshMoment r (fourCellOperatorHalfWidth / 2) := by
    rw [show (fun x : ℝ ↦ J x * r x) =
        fun x ↦ H x * r x - P x * r x by
      funext x
      dsimp only [J]
      ring,
      intervalIntegral.integral_sub hHr hPr, hpoly, sub_zero]
    simpa only [H] using hcosh
  rw [hpair] at hcauchy'
  simpa only [J, H, P] using hcauchy'

/-- Above the fourteenth harmonic, mass itself is dominated by the complete
polar-free tail operator.  This is the diagonal form of the spectral margin
behind the stronger two-fifths raw-energy reserve. -/
theorem tailFourteen_mass_le_fourCellEvenPolarFreeOperator
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (heven : Function.Even r)
    (hlow : centeredLegendreMomentsVanishBelow r 14) :
    (∫ x : ℝ in -1..1, r x ^ 2) ≤
      fourCellEvenPolarFreeOperator r := by
  let M : ℝ := ∫ x : ℝ in -1..1, r x ^ 2
  let E : ℝ := centeredRawLogEnergy r / 4
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hraw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    r hr hlocal 14 hlow
  have hgap : (1171733 / 360360 : ℝ) * M ≤ E := by
    norm_num [harmonic, Finset.sum_range_succ] at hraw
    simpa only [M, E, factorTwoIntrinsicEnergy] using hraw
  have htail :=
    two_fifths_rawEnergy_le_fourCellEvenPolarFreeOperator_of_tailFourteen
      r hr hlocal heven hlow
  have hMtoE : M ≤ (2 / 5 : ℝ) * E := by
    nlinarith only [hgap, hM]
  exact hMtoE.trans htail

/-- The wide-cosh coordinate of a `P₁₄+` tail costs at most one
fifty-millionth of its polar-free operator. -/
theorem tailFourteen_positiveCoshMoment_sq_le_one_div_fiftyMillion_polarFree
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (heven : Function.Even r)
    (hlow : centeredLegendreMomentsVanishBelow r 14) :
    fourCellPositiveCoshMoment r (fourCellOperatorHalfWidth / 2) ^ 2 ≤
      (1 / 50000000 : ℝ) * fourCellEvenPolarFreeOperator r := by
  let M : ℝ := ∫ x : ℝ in -1..1, r x ^ 2
  let D : ℝ := ∫ x : ℝ in -1..1,
    (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift
      fourCellEvenHalfWideCoshQuadraticSelectorPolynomial x) ^ 2
  have hpair :
      fourCellPositiveCoshMoment r (fourCellOperatorHalfWidth / 2) ^ 2 ≤
        D * M := by
    simpa only [D, M] using
      positiveCoshMoment_sq_le_quadraticCoshRemainderNorm_mul_mass_of_tailFourteen
        r hr heven hlow
  have hD : D ≤ (1 / 50000000 : ℝ) := by
    simpa only [D] using integral_halfWideCosh_sub_quadraticSelector_sq_le
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hDM : D * M ≤ (1 / 50000000 : ℝ) * M :=
    mul_le_mul_of_nonneg_right hD hM
  have hmass := tailFourteen_mass_le_fourCellEvenPolarFreeOperator
    r hr hlocal heven hlow
  have hmassScaled :=
    mul_le_mul_of_nonneg_left hmass (by norm_num : (0 : ℝ) ≤ 1 / 50000000)
  exact hpair.trans (hDM.trans hmassScaled)

/-- For a full zero-cosh profile, the finite `P₀,…,P₁₂` cosh
coordinate is exactly the negative tail coordinate.  Hence its entire
constraint defect is owned by one fifty-millionth of the `P₁₄+`
polar-free operator. -/
theorem lowProjectionFourteen_positiveCoshMoment_sq_le_one_div_fiftyMillion_tailPolarFree
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0) :
    fourCellPositiveCoshMoment (centeredLegendreLowProjection w hw 14)
        (fourCellOperatorHalfWidth / 2) ^ 2 ≤
      (1 / 50000000 : ℝ) * fourCellEvenPolarFreeOperator
        (centeredLegendreHigherResidual w hw 14) := by
  let p : ℝ → ℝ := centeredLegendreLowProjection w hw 14
  let r : ℝ → ℝ := centeredLegendreHigherResidual w hw 14
  let lambda : ℝ := fourCellOperatorHalfWidth / 2
  have hp : Continuous p := by
    simpa only [p] using continuous_centeredLegendreLowProjection w hw 14
  have hr : Continuous r := by
    simpa only [r] using continuous_centeredLegendreHigherResidual w hw 14
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    simpa only [r] using
      locallyLipschitzOn_centeredLegendreHigherResidual w hw hlocal 14
  have hrEven : Function.Even r := by
    simpa only [r] using centeredLegendreHigherResidual_even w hw heven 14
  have hrGap : centeredLegendreMomentsVanishBelow r 14 := by
    simpa only [r] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 14
  have hsum : p + r = w := by
    simpa only [p, r] using
      centeredLegendreLowProjection_add_higherResidual w hw 14
  have hpInt : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (lambda * x) * p x) volume 0 1 :=
    ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).mul hp)
      |>.intervalIntegrable _ _
  have hrInt : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (lambda * x) * r x) volume 0 1 :=
    ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).mul hr)
      |>.intervalIntegrable _ _
  have hCadd : fourCellPositiveCoshMoment (p + r) lambda =
      fourCellPositiveCoshMoment p lambda +
        fourCellPositiveCoshMoment r lambda := by
    unfold fourCellPositiveCoshMoment
    rw [show (fun x : ℝ ↦ Real.cosh (lambda * x) * (p + r) x) =
      fun x ↦ Real.cosh (lambda * x) * p x +
        Real.cosh (lambda * x) * r x by
      funext x
      simp only [Pi.add_apply]
      ring,
      intervalIntegral.integral_add hpInt hrInt]
  rw [hsum] at hCadd
  have hneg : fourCellPositiveCoshMoment p lambda =
      -fourCellPositiveCoshMoment r lambda := by
    dsimp only [lambda] at hCadd
    linarith only [hCadd, hzero]
  have htail :=
    tailFourteen_positiveCoshMoment_sq_le_one_div_fiftyMillion_polarFree
      r hr hrLocal hrEven hrGap
  dsimp only [p, r, lambda] at hneg ⊢
  rw [hneg, neg_sq]
  simpa only [r] using htail

/-- The cosh Gram pivot is uniformly positive.  The simple lower bound
comes from `cosh ≥ 1`; it is enough to make the quotient projection scalar
canonical without evaluating any transcendental integral. -/
theorem one_half_le_integral_fourCellEvenHalfWideCoshRepresenter_sq :
    (1 / 2 : ℝ) ≤
      ∫ x : ℝ in -1..1, fourCellEvenHalfWideCoshRepresenter x ^ 2 := by
  have hH : Continuous fourCellEvenHalfWideCoshRepresenter := by
    unfold fourCellEvenHalfWideCoshRepresenter
    fun_prop
  have hconst : IntervalIntegrable (fun _x : ℝ ↦ (1 / 4 : ℝ))
      volume (-1) 1 := Continuous.intervalIntegrable continuous_const _ _
  have hHsq : IntervalIntegrable
      (fun x : ℝ ↦ fourCellEvenHalfWideCoshRepresenter x ^ 2)
      volume (-1) 1 := (hH.pow 2).intervalIntegrable _ _
  calc
    (1 / 2 : ℝ) = ∫ _x : ℝ in -1..1, (1 / 4 : ℝ) := by norm_num
    _ ≤ ∫ x : ℝ in -1..1,
        fourCellEvenHalfWideCoshRepresenter x ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num) hconst hHsq
      intro x _hx
      have hcosh := Real.one_le_cosh
        ((fourCellOperatorHalfWidth / 2) * x)
      unfold fourCellEvenHalfWideCoshRepresenter
      nlinarith only [hcosh,
        sq_nonneg (Real.cosh ((fourCellOperatorHalfWidth / 2) * x) - 1)]

/-- Pythagorean identity for the exact wide-cosh quotient.  At fixed low
polynomial selector `q`, the displayed Gram ratio is the unique best scalar;
every other choice pays exactly the positive cosh pivot times a square. -/
theorem integral_endpointSeedTailFourteenConstrainedRepresenter_sq_eq_optimal_add
    (q : ℝ[X]) (s : ℝ) :
    let B := ∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenRepresenter q x *
        fourCellEvenHalfWideCoshRepresenter x
    let D := ∫ x : ℝ in -1..1,
      fourCellEvenHalfWideCoshRepresenter x ^ 2
    (∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s x ^ 2) =
      (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q (B / D) x ^ 2) +
        D * (s - B / D) ^ 2 := by
  dsimp only
  let B : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenEndpointSeedTailFourteenRepresenter q x *
      fourCellEvenHalfWideCoshRepresenter x
  let D : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenHalfWideCoshRepresenter x ^ 2
  let A : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2
  have hDlower : (1 / 2 : ℝ) ≤ D := by
    simpa only [D] using
      one_half_le_integral_fourCellEvenHalfWideCoshRepresenter_sq
  have hD : D ≠ 0 := by nlinarith only [hDlower]
  have hs :=
    integral_endpointSeedTailFourteenConstrainedRepresenter_sq_eq_quadratic
      q s
  have hopt :=
    integral_endpointSeedTailFourteenConstrainedRepresenter_sq_eq_quadratic
      q (B / D)
  change (∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s x ^ 2) =
    A - 2 * s * B + s ^ 2 * D at hs
  change (∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q (B / D) x ^ 2) =
    A - 2 * (B / D) * B + (B / D) ^ 2 * D at hopt
  change (∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s x ^ 2) =
    (∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q (B / D) x ^ 2) +
      D * (s - B / D) ^ 2
  rw [hs, hopt]
  field_simp [hD]
  ring

/-- Refined Cauchy closure on a `P₁₄+` tail.  The extra polynomial selector
is invisible to the tail, but removes its first three even dual coordinates
from the representer norm.  This is the exact weighted/coupled replacement
for charging the adversarial `P₈/P₁₀/P₁₂` direction by unweighted mass. -/
theorem fourCellEvenEndpointSeedCanonicalTailRow_sq_le_mass_of_tailFourteenNorm
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlow : centeredLegendreMomentsVanishBelow r 14)
    (q : ℝ[X]) (hq : q.natDegree < 14)
    (C : ℝ)
    (hdual :
      (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2) ≤ C) :
    fourCellEvenEndpointSeedCanonicalTailRow r ^ 2 ≤
      C * (∫ x : ℝ in -1..1, r x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  let G₀ : ℝ → ℝ :=
    fourCellEvenEndpointSeedProjectedTailRowRepresenter
      fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial
  let P : ℝ → ℝ := centeredPolynomialLift q
  let G : ℝ → ℝ := fourCellEvenEndpointSeedTailFourteenRepresenter q
  have hlowEight : centeredLegendreMomentsVanishBelow r 8 := by
    intro n hn
    exact hlow n (by omega)
  have hG₀ : MemLp G₀ 2 μ := by
    simpa only [G₀, μ] using
      memLp_fourCellEvenEndpointSeedProjectedTailRowRepresenter
        fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial
  have hP : MemLp P 2 μ := by
    simpa only [P, μ] using memLp_centeredPolynomialLift_two_restrict q
  have hG : MemLp G 2 μ := by
    simpa only [G, G₀, P,
      fourCellEvenEndpointSeedTailFourteenRepresenter] using hG₀.sub hP
  have hrMeas : AEStronglyMeasurable r μ :=
    hr.aestronglyMeasurable.restrict
  have hrLp : MemLp r 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hrMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖r x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hr.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hG₀r : IntervalIntegrable (fun x : ℝ ↦ G₀ x * r x)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact (hrLp.mul' hG₀ : MemLp (fun x : ℝ ↦ G₀ x * r x) 1 μ).integrable
      (by norm_num)
  have hPr : IntervalIntegrable (fun x : ℝ ↦ P x * r x)
      volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact (hrLp.mul' hP : MemLp (fun x : ℝ ↦ P x * r x) 1 μ).integrable
      (by norm_num)
  have hpoly : (∫ x : ℝ in -1..1, P x * r x) = 0 := by
    simpa only [P] using
      intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
        q r hr hlow hq
  have hpairing : fourCellEvenEndpointSeedCanonicalTailRow r =
      ∫ x : ℝ in -1..1, G x * r x := by
    have hbase :=
      fourCellEvenEndpointSeedTailRow_eq_projectedRepresenterPairing
        r hr hlowEight
        fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial
        natDegree_fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial_lt_eight
    change fourCellEvenEndpointSeedCanonicalTailRow r = _ at hbase
    calc
      fourCellEvenEndpointSeedCanonicalTailRow r =
          ∫ x : ℝ in -1..1, G₀ x * r x := by
        simpa only [G₀] using hbase
      _ = (∫ x : ℝ in -1..1, G₀ x * r x) -
          ∫ x : ℝ in -1..1, P x * r x := by rw [hpoly, sub_zero]
      _ = ∫ x : ℝ in -1..1, G x * r x := by
        rw [← intervalIntegral.integral_sub hG₀r hPr]
        apply intervalIntegral.integral_congr
        intro x _hx
        dsimp only [G, G₀, P,
          fourCellEvenEndpointSeedTailFourteenRepresenter]
        ring
  have hcauchy :=
    YoshidaEndpointWeightedCauchy.sq_integral_mul_le_weighted
      μ (fun _ : ℝ ↦ 1) G r (by simp)
        (by simpa only [div_one, Real.sqrt_one] using hG)
        (by simpa only [Real.sqrt_one, one_mul] using hrLp)
  have hcauchy' :
      (∫ x : ℝ in -1..1, G x * r x) ^ 2 ≤
        (∫ x : ℝ in -1..1, G x ^ 2) *
          (∫ x : ℝ in -1..1, r x ^ 2) := by
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa only [μ, div_one, one_mul] using hcauchy
  have hR : 0 ≤ ∫ x : ℝ in -1..1, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hdualScaled := mul_le_mul_of_nonneg_right hdual hR
  rw [hpairing]
  exact hcauchy'.trans hdualScaled

/-- Harmonic version of the refined `P₁₄+` estimate.  Any exact norm bound
for the additionally projected representer is converted directly into a
bound by the retained singular logarithmic energy. -/
theorem harmonic_fourteen_mul_fourCellEvenEndpointSeedCanonicalTailRow_sq_le_raw_of_norm
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (hlow : centeredLegendreMomentsVanishBelow r 14)
    (q : ℝ[X]) (hq : q.natDegree < 14)
    (C : ℝ) (hC : 0 ≤ C)
    (hdual :
      (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2) ≤ C) :
    (harmonic 14 : ℝ) *
        fourCellEvenEndpointSeedCanonicalTailRow r ^ 2 ≤
      C * (centeredRawLogEnergy r / 4) := by
  have hrow :=
    fourCellEvenEndpointSeedCanonicalTailRow_sq_le_mass_of_tailFourteenNorm
      r hr hlow q hq C hdual
  have hraw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    r hr hlocal 14 hlow
  have hH : 0 ≤ (harmonic 14 : ℝ) := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hrowScaled := mul_le_mul_of_nonneg_left hrow hH
  have hrawScaled := mul_le_mul_of_nonneg_left hraw hC
  unfold factorTwoIntrinsicEnergy at hrawScaled
  nlinarith only [hrowScaled, hrawScaled]

/-- Final cutoff-fourteen Young handoff.  The old coarse tail-mass charge is
replaced by the exact reciprocal fourteenth harmonic and by an arbitrary
degree-`< 14` representer projection.  Thus the only finite obligation is
the coupled row through `P₁₂`; every higher mode is paid by retained
singular energy with the sharp structural factor `1 / H₁₄`. -/
theorem fourCellEvenEndpointSeedRow_sq_le_lowThroughTwelve_add_rawTail_of_norm
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (q : ℝ[X]) (hq : q.natDegree < 14)
    (C : ℝ) (hC : 0 ≤ C)
    (hdual :
      (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2) ≤ C)
    (η : ℝ) (hη : 0 < η) :
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      (1 + η) *
          fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw ^ 2 +
        (1 + η⁻¹) * ((360360 / 1171733 : ℝ) * C) *
          (centeredRawLogEnergy
            (centeredLegendreHigherResidual w hw 14) / 4) := by
  let r : ℝ → ℝ := centeredLegendreHigherResidual w hw 14
  let L : ℝ := fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw
  let T : ℝ := fourCellEvenEndpointSeedCanonicalTailRow r
  have hr : Continuous r := by
    simpa only [r] using continuous_centeredLegendreHigherResidual w hw 14
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    simpa only [r] using
      locallyLipschitzOn_centeredLegendreHigherResidual w hw hlocal 14
  have hrGap : centeredLegendreMomentsVanishBelow r 14 := by
    simpa only [r] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 14
  have hweighted : (harmonic 14 : ℝ) * T ^ 2 ≤
      C * (centeredRawLogEnergy r / 4) := by
    simpa only [T] using
      harmonic_fourteen_mul_fourCellEvenEndpointSeedCanonicalTailRow_sq_le_raw_of_norm
        r hr hrLocal hrGap q hq C hC hdual
  have hT : T ^ 2 ≤
      (360360 / 1171733 : ℝ) * C *
        (centeredRawLogEnergy r / 4) := by
    norm_num [harmonic, Finset.sum_range_succ] at hweighted
    nlinarith only [hweighted]
  have hscale : 0 ≤ 1 + η⁻¹ := by
    have hinv : 0 < η⁻¹ := inv_pos.mpr hη
    positivity
  have hTscaled := mul_le_mul_of_nonneg_left hT hscale
  have hrow :=
    fourCellEvenEndpointSeedRow_eq_canonicalLowThroughTwelve_add_tailFourteen
      w hw hlocal heven hzero
  have hrow' : fourCellEvenEndpointSeedRow w = L + T := by
    simpa only [L, T, r] using hrow
  have hyoung : (L + T) ^ 2 ≤
      (1 + η) * L ^ 2 + (1 + η⁻¹) * T ^ 2 := by
    have hηne : η ≠ 0 := hη.ne'
    have hinv0 : 0 ≤ η⁻¹ := (inv_pos.mpr hη).le
    have hid :
        (1 + η) * L ^ 2 + (1 + η⁻¹) * T ^ 2 - (L + T) ^ 2 =
          η⁻¹ * (η * L - T) ^ 2 := by
      field_simp [hηne]
      all_goals ring
    rw [← sub_nonneg, hid]
    exact mul_nonneg hinv0 (sq_nonneg (η * L - T))
  rw [hrow']
  calc
    (L + T) ^ 2 ≤
        (1 + η) * L ^ 2 + (1 + η⁻¹) * T ^ 2 :=
      hyoung
    _ ≤ (1 + η) * L ^ 2 +
        (1 + η⁻¹) * ((360360 / 1171733 : ℝ) * C) *
          (centeredRawLogEnergy r / 4) := by
      nlinarith only [hTscaled]
    _ = (1 + η) *
          fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw ^ 2 +
        (1 + η⁻¹) * ((360360 / 1171733 : ℝ) * C) *
          (centeredRawLogEnergy
            (centeredLegendreHigherResidual w hw 14) / 4) := by
      dsimp only [L, r]

/-- Concrete unconditional cutoff-fourteen budget obtained from the current
canonical representer certificate.  Its tail coefficient
`6719427 / 82021310000` is exactly the old norm budget divided by `H₁₄`;
future `P₈/P₁₀/P₁₂` projection certificates can only improve it. -/
theorem fourCellEvenEndpointSeedRow_sq_le_lowThroughTwelve_add_rawTail_of_positive
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (η : ℝ) (hη : 0 < η) :
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      (1 + η) *
          fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw ^ 2 +
        (1 + η⁻¹) * (6719427 / 82021310000 : ℝ) *
          (centeredRawLogEnergy
            (centeredLegendreHigherResidual w hw 14) / 4) := by
  have h :=
    fourCellEvenEndpointSeedRow_sq_le_lowThroughTwelve_add_rawTail_of_norm
      w hw hlocal heven hzero 0 (by norm_num)
      fourCellEvenEndpointSeedCanonicalTailNormBudget
      (by norm_num [fourCellEvenEndpointSeedCanonicalTailNormBudget])
      integral_endpointSeedTailFourteenRepresenter_zero_sq_le_rational η hη
  convert h using 1
  all_goals norm_num [fourCellEvenEndpointSeedCanonicalTailNormBudget]

/-- Harmonic-weighted form of the endpoint-row estimate above a genuine
`P₁₄` cutoff.  Unlike the unweighted mass estimate, this charges the row to
the singular logarithmic diagonal retained by the four-cell operator.  The
first three even tail modes `P₈/P₁₀/P₁₂` are deliberately excluded: they
belong in the coupled finite block rather than being paid at the weakest
eighth-harmonic rate. -/
theorem harmonic_fourteen_mul_fourCellEvenEndpointSeedCanonicalTailRow_sq_le_raw
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (hlow : centeredLegendreMomentsVanishBelow r 14) :
    (harmonic 14 : ℝ) *
        fourCellEvenEndpointSeedCanonicalTailRow r ^ 2 ≤
      fourCellEvenEndpointSeedCanonicalTailNormBudget *
        (centeredRawLogEnergy r / 4) := by
  have hlowEight : centeredLegendreMomentsVanishBelow r 8 := by
    intro n hn
    exact hlow n (by omega)
  have hrow :=
    fourCellEvenEndpointSeedCanonicalTailRow_sq_le_rational_mass
      r hr hlowEight
  have hraw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    r hr hlocal 14 hlow
  have hH : 0 ≤ (harmonic 14 : ℝ) := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hC : 0 ≤ fourCellEvenEndpointSeedCanonicalTailNormBudget := by
    norm_num [fourCellEvenEndpointSeedCanonicalTailNormBudget]
  have hrowScaled := mul_le_mul_of_nonneg_left hrow hH
  have hrawScaled := mul_le_mul_of_nonneg_left hraw hC
  unfold factorTwoIntrinsicEnergy at hrawScaled
  nlinarith only [hrowScaled, hrawScaled]

/-- Exact scalar Young inequality with a free positive allocation parameter.
Keeping the parameter free is essential: a fixed split can consume more tail
diagonal than the four-cell operator possesses. -/
theorem add_sq_le_of_positive_youngParameter
    (x y η : ℝ) (hη : 0 < η) :
    (x + y) ^ 2 ≤
      (1 + η) * x ^ 2 + (1 + η⁻¹) * y ^ 2 := by
  have hηne : η ≠ 0 := hη.ne'
  have hinv0 : 0 ≤ η⁻¹ := (inv_pos.mpr hη).le
  have hid :
      (1 + η) * x ^ 2 + (1 + η⁻¹) * y ^ 2 - (x + y) ^ 2 =
        η⁻¹ * (η * x - y) ^ 2 := by
    field_simp [hηne]
    all_goals ring
  rw [← sub_nonneg, hid]
  exact mul_nonneg hinv0 (sq_nonneg (η * x - y))

/-- Coupled cutoff-fourteen handoff in the actual zero-cosh quotient.  The
finite row and the tail density share the same free scalar `s`: changing `s`
cannot change the full row, but it can move the wide-cosh direction to the
side of the Schur block where it is cheapest.  Only after this lossless
coupling is exposed is a free Young allocation applied. -/
theorem fourCellEvenEndpointSeedRow_sq_le_coshConstrainedLowThroughTwelve_add_rawTail_of_norm
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (q : ℝ[X]) (hq : q.natDegree < 14) (s C : ℝ) (hC : 0 ≤ C)
    (hdual :
      (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s x ^ 2) ≤
          C)
    (η : ℝ) (hη : 0 < η) :
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      (1 + η) *
          (fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw -
            s * fourCellPositiveCoshMoment
              (centeredLegendreLowProjection w hw 14)
              (fourCellOperatorHalfWidth / 2)) ^ 2 +
        (1 + η⁻¹) * ((360360 / 1171733 : ℝ) * C) *
          (centeredRawLogEnergy
            (centeredLegendreHigherResidual w hw 14) / 4) := by
  let r : ℝ → ℝ := centeredLegendreHigherResidual w hw 14
  let L : ℝ :=
    fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw -
      s * fourCellPositiveCoshMoment
        (centeredLegendreLowProjection w hw 14)
        (fourCellOperatorHalfWidth / 2)
  let T : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s x * r x
  have hr : Continuous r := by
    simpa only [r] using continuous_centeredLegendreHigherResidual w hw 14
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    simpa only [r] using
      locallyLipschitzOn_centeredLegendreHigherResidual w hw hlocal 14
  have hrGap : centeredLegendreMomentsVanishBelow r 14 := by
    simpa only [r] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 14
  have hweighted : (harmonic 14 : ℝ) * T ^ 2 ≤
      C * (centeredRawLogEnergy r / 4) := by
    simpa only [T] using
      harmonic_fourteen_mul_endpointSeedTailFourteenConstrainedPairing_sq_le_raw_of_norm
        r hr hrLocal hrGap q s C hC hdual
  have hT : T ^ 2 ≤
      (360360 / 1171733 : ℝ) * C *
        (centeredRawLogEnergy r / 4) := by
    norm_num [harmonic, Finset.sum_range_succ] at hweighted
    nlinarith only [hweighted]
  have hscale : 0 ≤ 1 + η⁻¹ := by
    have hinv : 0 < η⁻¹ := inv_pos.mpr hη
    positivity
  have hTscaled := mul_le_mul_of_nonneg_left hT hscale
  have hrow :=
    fourCellEvenEndpointSeedRow_eq_coshConstrainedLowThroughTwelve_add_tailPairing
      w hw hlocal heven hzero q hq s
  have hrow' : fourCellEvenEndpointSeedRow w = L + T := by
    simpa only [L, T, r] using hrow
  rw [hrow']
  calc
    (L + T) ^ 2 ≤
        (1 + η) * L ^ 2 + (1 + η⁻¹) * T ^ 2 :=
      add_sq_le_of_positive_youngParameter L T η hη
    _ ≤ (1 + η) * L ^ 2 +
        (1 + η⁻¹) * ((360360 / 1171733 : ℝ) * C) *
          (centeredRawLogEnergy r / 4) := by
      nlinarith only [hTscaled]
    _ = (1 + η) *
          (fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw -
            s * fourCellPositiveCoshMoment
              (centeredLegendreLowProjection w hw 14)
              (fourCellOperatorHalfWidth / 2)) ^ 2 +
        (1 + η⁻¹) * ((360360 / 1171733 : ℝ) * C) *
          (centeredRawLogEnergy
            (centeredLegendreHigherResidual w hw 14) / 4) := by
      dsimp only [L, r]

/-- Self-contained quadratic form of the cosh-bordered handoff.  The three
tail Gram entries remain coupled exactly, so the shared selector `s` is now a
literal finite scalar border rather than an external norm certificate. -/
theorem fourCellEvenEndpointSeedRow_sq_le_coshBorderQuadratic
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (q : ℝ[X]) (hq : q.natDegree < 14)
    (s η : ℝ) (hη : 0 < η) :
    let a : ℝ := 1 + η
    let L : ℝ := fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw
    let P : ℝ := fourCellPositiveCoshMoment
      (centeredLegendreLowProjection w hw 14)
      (fourCellOperatorHalfWidth / 2)
    let A : ℝ := ∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2
    let B : ℝ := ∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenRepresenter q x *
        fourCellEvenHalfWideCoshRepresenter x
    let D : ℝ := ∫ x : ℝ in -1..1,
      fourCellEvenHalfWideCoshRepresenter x ^ 2
    let E : ℝ := centeredRawLogEnergy
      (centeredLegendreHigherResidual w hw 14) / 4
    let W : ℝ :=
      (1 + η⁻¹) * (360360 / 1171733 : ℝ) * E
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      a * (L - s * P) ^ 2 + W * (A - 2 * s * B + s ^ 2 * D) := by
  dsimp only
  let C : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q s x ^ 2
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hbound :=
    fourCellEvenEndpointSeedRow_sq_le_coshConstrainedLowThroughTwelve_add_rawTail_of_norm
      w hw hlocal heven hzero q hq s C hC (by rfl) η hη
  have hnorm :=
    integral_endpointSeedTailFourteenConstrainedRepresenter_sq_eq_quadratic
      q s
  dsimp only [C] at hbound
  rw [hnorm] at hbound
  convert hbound using 1
  all_goals ring

/-- Strong quotient form of the bordered quadratic.  The cosh direction is
first reduced modulo an arbitrary degree-`<14` polynomial `p`; hence its tail
pivot contains only the part that a `P₁₄+` residual can actually see. -/
theorem fourCellEvenEndpointSeedRow_sq_le_polynomialCoshBorderQuadratic
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (q p : ℝ[X]) (hq : q.natDegree < 14) (hp : p.natDegree < 14)
    (s η : ℝ) (hη : 0 < η) :
    let a : ℝ := 1 + η
    let L : ℝ := fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw
    let P : ℝ := fourCellPositiveCoshMoment
      (centeredLegendreLowProjection w hw 14)
      (fourCellOperatorHalfWidth / 2)
    let A : ℝ := ∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2
    let B : ℝ := ∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenRepresenter q x *
        (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift p x)
    let D : ℝ := ∫ x : ℝ in -1..1,
      (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift p x) ^ 2
    let E : ℝ := centeredRawLogEnergy
      (centeredLegendreHigherResidual w hw 14) / 4
    let W : ℝ :=
      (1 + η⁻¹) * (360360 / 1171733 : ℝ) * E
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      a * (L - s * P) ^ 2 + W * (A - 2 * s * B + s ^ 2 * D) := by
  dsimp only
  let q' : ℝ[X] := q - s • p
  have hq' : q'.natDegree < 14 := by
    simpa only [q'] using natDegree_sub_smul_lt_fourteen q p s hq hp
  let C : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenEndpointSeedTailFourteenPolynomialCoshRepresenter q p s x ^ 2
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hdual :
      (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter q' s x ^ 2) ≤
          C := by
    apply le_of_eq
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [q', C]
    rw [← fourCellEvenEndpointSeedTailFourteenPolynomialCoshRepresenter_eq_constrained]
  have hbound :=
    fourCellEvenEndpointSeedRow_sq_le_coshConstrainedLowThroughTwelve_add_rawTail_of_norm
      w hw hlocal heven hzero q' hq' s C hC hdual η hη
  have hnorm :=
    integral_endpointSeedTailFourteenPolynomialCoshRepresenter_sq_eq_quadratic
      q p s
  dsimp only [C] at hbound
  rw [hnorm] at hbound
  convert hbound using 1
  all_goals ring

/-- Completely rational analytic handoff for the shared cosh border.  The
only remaining profile-dependent entries are the finite row `L`, its finite
cosh coordinate `P`, and the raw tail energy `E`; all three tail Gram entries
have been replaced by structural rational bounds. -/
theorem fourCellEvenEndpointSeedRow_sq_le_quadraticCoshBorderRational
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (s η : ℝ) (hη : 0 < η) :
    let L : ℝ := fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw
    let P : ℝ := fourCellPositiveCoshMoment
      (centeredLegendreLowProjection w hw 14)
      (fourCellOperatorHalfWidth / 2)
    let E : ℝ := centeredRawLogEnergy
      (centeredLegendreHigherResidual w hw 14) / 4
    let W : ℝ :=
      (1 + η⁻¹) * (360360 / 1171733 : ℝ) * E
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      (1 + η) * (L - s * P) ^ 2 +
        W * (fourCellEvenEndpointSeedCanonicalTailNormBudget +
          |s| / 200000 + s ^ 2 / 50000000) := by
  dsimp only
  let A : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenEndpointSeedTailFourteenRepresenter 0 x ^ 2
  let B : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenEndpointSeedTailFourteenRepresenter 0 x *
      (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift
        fourCellEvenHalfWideCoshQuadraticSelectorPolynomial x)
  let D : ℝ := ∫ x : ℝ in -1..1,
    (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift
      fourCellEvenHalfWideCoshQuadraticSelectorPolynomial x) ^ 2
  let E : ℝ := centeredRawLogEnergy
    (centeredLegendreHigherResidual w hw 14) / 4
  let W : ℝ := (1 + η⁻¹) * (360360 / 1171733 : ℝ) * E
  have hA : A ≤ fourCellEvenEndpointSeedCanonicalTailNormBudget := by
    simpa only [A] using
      integral_endpointSeedTailFourteenRepresenter_zero_sq_le_rational
  have hB : |B| ≤ (1 / 400000 : ℝ) := by
    simpa only [B] using
      abs_integral_endpointSeedTailFourteenRepresenter_zero_mul_quadraticCoshRemainder_le
  have hD : D ≤ (1 / 50000000 : ℝ) := by
    simpa only [D] using integral_halfWideCosh_sub_quadraticSelector_sq_le
  have hcross : -2 * s * B ≤ |s| / 200000 := by
    calc
      -2 * s * B ≤ |-2 * s * B| := le_abs_self _
      _ = 2 * |s| * |B| := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ 2 * |s| * (1 / 400000 : ℝ) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      _ = |s| / 200000 := by ring
  have hDscaled : s ^ 2 * D ≤ s ^ 2 / 50000000 := by
    have h := mul_le_mul_of_nonneg_left hD (sq_nonneg s)
    nlinarith only [h]
  have hgram :
      A - 2 * s * B + s ^ 2 * D ≤
        fourCellEvenEndpointSeedCanonicalTailNormBudget +
          |s| / 200000 + s ^ 2 / 50000000 := by
    linarith only [hA, hcross, hDscaled]
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact div_nonneg (centeredRawLogEnergy_nonnegative _) (by norm_num)
  have hW : 0 ≤ W := by
    dsimp only [W]
    have hinv : 0 < η⁻¹ := inv_pos.mpr hη
    positivity
  have hgramScaled := mul_le_mul_of_nonneg_left hgram hW
  have hquad :=
    fourCellEvenEndpointSeedRow_sq_le_polynomialCoshBorderQuadratic
      w hw hlocal heven hzero 0
        fourCellEvenHalfWideCoshQuadraticSelectorPolynomial (by simp)
        natDegree_fourCellEvenHalfWideCoshQuadraticSelectorPolynomial_lt_fourteen
        s η hη
  have hquad' : fourCellEvenEndpointSeedRow w ^ 2 ≤
      (1 + η) *
          (fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw -
            s * fourCellPositiveCoshMoment
              (centeredLegendreLowProjection w hw 14)
              (fourCellOperatorHalfWidth / 2)) ^ 2 +
        W * (A - 2 * s * B + s ^ 2 * D) := by
    simpa only [A, B, D, E, W] using hquad
  apply hquad'.trans
  dsimp only [W, E] at hgramScaled ⊢
  linarith only [hgramScaled]

/-- The rational cosh-border tail charge still fits inside one sixteenth of
the tail operator for every selector in the wide structural range
`|s| ≤ 10`.  This leaves the finite Schur certificate free to use the cosh
constraint without reopening the infinite block. -/
theorem quadraticCoshBorderRational_tailCharge_le_one_sixteenth_polarFree_of_tailFourteen
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (heven : Function.Even r)
    (hlow : centeredLegendreMomentsVanishBelow r 14)
    (s : ℝ) (hs : |s| ≤ 10) :
    (1 + ((1 / 250 : ℝ)⁻¹)) * (360360 / 1171733 : ℝ) *
        (centeredRawLogEnergy r / 4) *
          (fourCellEvenEndpointSeedCanonicalTailNormBudget +
            |s| / 200000 + s ^ 2 / 50000000) ≤
      (1 / 16 : ℝ) * fourCellEvenPolarFreeOperator r := by
  let C : ℝ := fourCellEvenEndpointSeedCanonicalTailNormBudget +
    |s| / 200000 + s ^ 2 / 50000000
  let E : ℝ := centeredRawLogEnergy r / 4
  let K : ℝ :=
    (1 + ((1 / 250 : ℝ)⁻¹)) * (360360 / 1171733 : ℝ)
  have hsSq : s ^ 2 ≤ (100 : ℝ) := by
    nlinarith only [sq_abs s, abs_nonneg s, hs]
  have hC : C ≤
      fourCellEvenEndpointSeedCanonicalTailNormBudget +
        (10 : ℝ) / 200000 + 100 / 50000000 := by
    dsimp only [C]
    linarith only [hs, hsSq]
  have hK : 0 ≤ K := by
    dsimp only [K]
    norm_num
  have hKC : K * C ≤ (1 / 40 : ℝ) := by
    calc
      K * C ≤ K *
          (fourCellEvenEndpointSeedCanonicalTailNormBudget +
            (10 : ℝ) / 200000 + 100 / 50000000) :=
        mul_le_mul_of_nonneg_left hC hK
      _ ≤ (1 / 40 : ℝ) := by
        dsimp only [K]
        norm_num [fourCellEvenEndpointSeedCanonicalTailNormBudget]
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact div_nonneg (centeredRawLogEnergy_nonnegative r) (by norm_num)
  have hcharge := mul_le_mul_of_nonneg_right hKC hE
  have htail :=
    two_fifths_rawEnergy_le_fourCellEvenPolarFreeOperator_of_tailFourteen
      r hr hlocal heven hlow
  have htailScaled :=
    mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 1 / 16)
  change K * E * C ≤ (1 / 16 : ℝ) * fourCellEvenPolarFreeOperator r
  calc
    K * E * C = (K * C) * E := by ring
    _ ≤ (1 / 40 : ℝ) * E := hcharge
    _ = (1 / 16 : ℝ) * ((2 / 5 : ℝ) * E) := by ring
    _ ≤ (1 / 16 : ℝ) * fourCellEvenPolarFreeOperator r := by
      simpa only [E] using htailScaled

/-- Final infinite-block elimination with the shared finite cosh selector
retained.  For any `|s| ≤ 10`, the endpoint row is reduced to the single
finite square `L - sP`; every `P₁₄+` contribution is absorbed by the
fixed one-sixteenth tail reserve. -/
theorem fourCellEvenEndpointSeedRow_sq_le_251_div_250_coshReducedLowThroughTwelve_add_one_sixteenth_tailPolarFree
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (s : ℝ) (hs : |s| ≤ 10) :
    let L : ℝ := fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw
    let P : ℝ := fourCellPositiveCoshMoment
      (centeredLegendreLowProjection w hw 14)
      (fourCellOperatorHalfWidth / 2)
    let r : ℝ → ℝ := centeredLegendreHigherResidual w hw 14
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      (251 / 250 : ℝ) * (L - s * P) ^ 2 +
        (1 / 16 : ℝ) * fourCellEvenPolarFreeOperator r := by
  dsimp only
  let r : ℝ → ℝ := centeredLegendreHigherResidual w hw 14
  have hr : Continuous r := by
    simpa only [r] using continuous_centeredLegendreHigherResidual w hw 14
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    simpa only [r] using
      locallyLipschitzOn_centeredLegendreHigherResidual w hw hlocal 14
  have hrEven : Function.Even r := by
    simpa only [r] using centeredLegendreHigherResidual_even w hw heven 14
  have hrGap : centeredLegendreMomentsVanishBelow r 14 := by
    simpa only [r] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 14
  let T : ℝ :=
    (1 + ((1 / 250 : ℝ)⁻¹)) * (360360 / 1171733 : ℝ) *
      (centeredRawLogEnergy r / 4) *
        (fourCellEvenEndpointSeedCanonicalTailNormBudget +
          |s| / 200000 + s ^ 2 / 50000000)
  have hrow := fourCellEvenEndpointSeedRow_sq_le_quadraticCoshBorderRational
    w hw hlocal heven hzero s (1 / 250) (by norm_num)
  have hrow' : fourCellEvenEndpointSeedRow w ^ 2 ≤
      (251 / 250 : ℝ) *
          (fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw -
            s * fourCellPositiveCoshMoment
              (centeredLegendreLowProjection w hw 14)
              (fourCellOperatorHalfWidth / 2)) ^ 2 + T := by
    dsimp only [T, r]
    norm_num at hrow
    ring_nf at hrow ⊢
    exact hrow
  have htail : T ≤
      (1 / 16 : ℝ) * fourCellEvenPolarFreeOperator r := by
    dsimp only [T]
    exact
      quadraticCoshBorderRational_tailCharge_le_one_sixteenth_polarFree_of_tailFourteen
        r hr hrLocal hrEven hrGap s hs
  dsimp only [r] at htail ⊢
  linarith only [hrow', htail]

/-- Exact scalar Schur complement of the shared finite/tail cosh border.
The negative square is retained: this is the structural gain lost by treating
the finite row and the tail representer with separate absolute-value bounds.
The remaining positivity premise is precisely the one-dimensional bordered
diagonal, not a family of modes or a numerical search. -/
theorem fourCellEvenEndpointSeedRow_sq_le_coshBorderSchurComplement
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (q : ℝ[X]) (hq : q.natDegree < 14)
    (η : ℝ) (hη : 0 < η) :
    let a : ℝ := 1 + η
    let L : ℝ := fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw
    let P : ℝ := fourCellPositiveCoshMoment
      (centeredLegendreLowProjection w hw 14)
      (fourCellOperatorHalfWidth / 2)
    let A : ℝ := ∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2
    let B : ℝ := ∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenRepresenter q x *
        fourCellEvenHalfWideCoshRepresenter x
    let D : ℝ := ∫ x : ℝ in -1..1,
      fourCellEvenHalfWideCoshRepresenter x ^ 2
    let E : ℝ := centeredRawLogEnergy
      (centeredLegendreHigherResidual w hw 14) / 4
    let W : ℝ :=
      (1 + η⁻¹) * (360360 / 1171733 : ℝ) * E
    let K : ℝ := a * P ^ 2 + W * D
    let N : ℝ := a * L * P + W * B
    0 < K →
      fourCellEvenEndpointSeedRow w ^ 2 ≤
        a * L ^ 2 + W * A - N ^ 2 / K := by
  dsimp only
  intro hKpos
  let a : ℝ := 1 + η
  let L : ℝ := fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw
  let P : ℝ := fourCellPositiveCoshMoment
    (centeredLegendreLowProjection w hw 14)
    (fourCellOperatorHalfWidth / 2)
  let A : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2
  let B : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenEndpointSeedTailFourteenRepresenter q x *
      fourCellEvenHalfWideCoshRepresenter x
  let D : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenHalfWideCoshRepresenter x ^ 2
  let E : ℝ := centeredRawLogEnergy
    (centeredLegendreHigherResidual w hw 14) / 4
  let W : ℝ :=
    (1 + η⁻¹) * (360360 / 1171733 : ℝ) * E
  let K : ℝ := a * P ^ 2 + W * D
  let N : ℝ := a * L * P + W * B
  change 0 < K at hKpos
  change fourCellEvenEndpointSeedRow w ^ 2 ≤
    a * L ^ 2 + W * A - N ^ 2 / K
  let s : ℝ := N / K
  have hquad := fourCellEvenEndpointSeedRow_sq_le_coshBorderQuadratic
    w hw hlocal heven hzero q hq s η hη
  have hquad' : fourCellEvenEndpointSeedRow w ^ 2 ≤
      a * (L - s * P) ^ 2 + W * (A - 2 * s * B + s ^ 2 * D) := by
    simpa only [a, L, P, A, B, D, E, W] using hquad
  have hcompletion := coupled_scalar_cosh_border_completion
    a W L P A B D s hKpos.ne'
  have hcompletion' :
      a * (L - s * P) ^ 2 + W * (A - 2 * s * B + s ^ 2 * D) =
        a * L ^ 2 + W * A - N ^ 2 / K := by
    simpa [s, N, K] using hcompletion
  exact hquad'.trans_eq hcompletion'

/-- The scalar Schur-complement handoff is unconditional.  Its diagonal is
nonnegative from the raw-energy square and the cosh pivot `D ≥ 1/2`.  If the
diagonal vanishes, both the finite cosh coordinate and the weighted tail
factor vanish, so Lean's zero-division convention gives the same displayed
formula without a separate analytic case assumption. -/
theorem fourCellEvenEndpointSeedRow_sq_le_coshBorderSchurComplement_unconditional
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (q : ℝ[X]) (hq : q.natDegree < 14)
    (η : ℝ) (hη : 0 < η) :
    let a : ℝ := 1 + η
    let L : ℝ := fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw
    let P : ℝ := fourCellPositiveCoshMoment
      (centeredLegendreLowProjection w hw 14)
      (fourCellOperatorHalfWidth / 2)
    let A : ℝ := ∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2
    let B : ℝ := ∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenRepresenter q x *
        fourCellEvenHalfWideCoshRepresenter x
    let D : ℝ := ∫ x : ℝ in -1..1,
      fourCellEvenHalfWideCoshRepresenter x ^ 2
    let E : ℝ := centeredRawLogEnergy
      (centeredLegendreHigherResidual w hw 14) / 4
    let W : ℝ :=
      (1 + η⁻¹) * (360360 / 1171733 : ℝ) * E
    let K : ℝ := a * P ^ 2 + W * D
    let N : ℝ := a * L * P + W * B
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      a * L ^ 2 + W * A - N ^ 2 / K := by
  dsimp only
  let a : ℝ := 1 + η
  let L : ℝ := fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw
  let P : ℝ := fourCellPositiveCoshMoment
    (centeredLegendreLowProjection w hw 14)
    (fourCellOperatorHalfWidth / 2)
  let A : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2
  let B : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenEndpointSeedTailFourteenRepresenter q x *
      fourCellEvenHalfWideCoshRepresenter x
  let D : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenHalfWideCoshRepresenter x ^ 2
  let E : ℝ := centeredRawLogEnergy
    (centeredLegendreHigherResidual w hw 14) / 4
  let W : ℝ :=
    (1 + η⁻¹) * (360360 / 1171733 : ℝ) * E
  let K : ℝ := a * P ^ 2 + W * D
  let N : ℝ := a * L * P + W * B
  change fourCellEvenEndpointSeedRow w ^ 2 ≤
    a * L ^ 2 + W * A - N ^ 2 / K
  have ha : 0 < a := by
    dsimp only [a]
    linarith only [hη]
  have hDlower : (1 / 2 : ℝ) ≤ D := by
    simpa only [D] using
      one_half_le_integral_fourCellEvenHalfWideCoshRepresenter_sq
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) hDlower
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact div_nonneg (centeredRawLogEnergy_nonnegative _) (by norm_num)
  have hinv : 0 < η⁻¹ := inv_pos.mpr hη
  have hW : 0 ≤ W := by
    dsimp only [W]
    positivity
  have hAP : 0 ≤ a * P ^ 2 := mul_nonneg ha.le (sq_nonneg P)
  have hWD : 0 ≤ W * D := mul_nonneg hW hD.le
  have hKnonneg : 0 ≤ K := by
    dsimp only [K]
    exact add_nonneg hAP hWD
  by_cases hKzero : K = 0
  · have hsum : a * P ^ 2 + W * D = 0 := by
      simpa only [K] using hKzero
    have hAPzero : a * P ^ 2 = 0 := by
      nlinarith only [hsum, hAP, hWD]
    have hWDzero : W * D = 0 := by
      nlinarith only [hsum, hAP, hWD]
    have hPsqzero : P ^ 2 = 0 :=
      (mul_eq_zero.mp hAPzero).resolve_left ha.ne'
    have hPzero : P = 0 := sq_eq_zero_iff.mp hPsqzero
    have hWzero : W = 0 :=
      (mul_eq_zero.mp hWDzero).resolve_right hD.ne'
    have hNzero : N = 0 := by
      dsimp only [N]
      rw [hPzero, hWzero]
      ring
    have hquad := fourCellEvenEndpointSeedRow_sq_le_coshBorderQuadratic
      w hw hlocal heven hzero q hq 0 η hη
    have hquad' : fourCellEvenEndpointSeedRow w ^ 2 ≤
        a * (L - 0 * P) ^ 2 + W * (A - 2 * 0 * B + 0 ^ 2 * D) := by
      simpa only [a, L, P, A, B, D, E, W] using hquad
    rw [hWzero] at hquad'
    rw [hWzero, hNzero, hKzero]
    norm_num at hquad' ⊢
    exact hquad'
  · have hKpos : 0 < K :=
      lt_of_le_of_ne hKnonneg (Ne.symm hKzero)
    have hschur :=
      fourCellEvenEndpointSeedRow_sq_le_coshBorderSchurComplement
        w hw hlocal heven hzero q hq η hη
    dsimp only at hschur
    have hschur' := hschur (by
      simpa only [a, L, P, A, B, D, E, W, K] using hKpos)
    simpa only [a, L, P, A, B, D, E, W, K, N] using hschur'

/-- The polynomial-reduced cosh border also admits an unconditional exact
Schur complement.  This is the form relevant to the genuine `P₁₄+`
quotient: both the endpoint row and the cosh direction have first been
reduced modulo all lower polynomials.  The proof includes the degenerate
case `K = 0`; positivity of the two-vector Gram then forces the numerator to
vanish, so Lean's zero-division convention agrees with the displayed
formula. -/
theorem
    fourCellEvenEndpointSeedRow_sq_le_polynomialCoshBorderSchurComplement_unconditional
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (q p : ℝ[X]) (hq : q.natDegree < 14) (hp : p.natDegree < 14)
    (η : ℝ) (hη : 0 < η) :
    let a : ℝ := 1 + η
    let L : ℝ := fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw
    let P : ℝ := fourCellPositiveCoshMoment
      (centeredLegendreLowProjection w hw 14)
      (fourCellOperatorHalfWidth / 2)
    let A : ℝ := ∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2
    let B : ℝ := ∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedTailFourteenRepresenter q x *
        (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift p x)
    let D : ℝ := ∫ x : ℝ in -1..1,
      (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift p x) ^ 2
    let E : ℝ := centeredRawLogEnergy
      (centeredLegendreHigherResidual w hw 14) / 4
    let W : ℝ :=
      (1 + η⁻¹) * (360360 / 1171733 : ℝ) * E
    let K : ℝ := a * P ^ 2 + W * D
    let N : ℝ := a * L * P + W * B
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      a * L ^ 2 + W * A - N ^ 2 / K := by
  dsimp only
  let a : ℝ := 1 + η
  let L : ℝ := fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw
  let P : ℝ := fourCellPositiveCoshMoment
    (centeredLegendreLowProjection w hw 14)
    (fourCellOperatorHalfWidth / 2)
  let A : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenEndpointSeedTailFourteenRepresenter q x ^ 2
  let B : ℝ := ∫ x : ℝ in -1..1,
    fourCellEvenEndpointSeedTailFourteenRepresenter q x *
      (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift p x)
  let D : ℝ := ∫ x : ℝ in -1..1,
    (fourCellEvenHalfWideCoshRepresenter x - centeredPolynomialLift p x) ^ 2
  let E : ℝ := centeredRawLogEnergy
    (centeredLegendreHigherResidual w hw 14) / 4
  let W : ℝ :=
    (1 + η⁻¹) * (360360 / 1171733 : ℝ) * E
  let K : ℝ := a * P ^ 2 + W * D
  let N : ℝ := a * L * P + W * B
  change fourCellEvenEndpointSeedRow w ^ 2 ≤
    a * L ^ 2 + W * A - N ^ 2 / K
  have ha : 0 < a := by
    dsimp only [a]
    linarith only [hη]
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact div_nonneg (centeredRawLogEnergy_nonnegative _) (by norm_num)
  have hinv : 0 < η⁻¹ := inv_pos.mpr hη
  have hW : 0 ≤ W := by
    dsimp only [W]
    positivity
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hgram : B ^ 2 ≤ A * D := by
    simpa only [A, B, D] using
      sq_integral_endpointSeedTailFourteenRepresenter_mul_polynomialCosh_le_gram
        q p
  have hAP : 0 ≤ a * P ^ 2 := mul_nonneg ha.le (sq_nonneg P)
  have hWD : 0 ≤ W * D := mul_nonneg hW hD
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact add_nonneg hAP hWD
  by_cases hKzero : K = 0
  · have hsum : a * P ^ 2 + W * D = 0 := by
      simpa only [K] using hKzero
    have hAPzero : a * P ^ 2 = 0 := by
      nlinarith only [hsum, hAP, hWD]
    have hWDzero : W * D = 0 := by
      nlinarith only [hsum, hAP, hWD]
    have hPsqzero : P ^ 2 = 0 :=
      (mul_eq_zero.mp hAPzero).resolve_left ha.ne'
    have hPzero : P = 0 := sq_eq_zero_iff.mp hPsqzero
    have hWBzero : W * B = 0 := by
      rcases mul_eq_zero.mp hWDzero with hWzero | hDzero
      · rw [hWzero, zero_mul]
      · have hBsq : B ^ 2 ≤ 0 := by
          rw [hDzero, mul_zero] at hgram
          exact hgram
        have hBzero : B = 0 := by
          nlinarith only [hBsq, sq_nonneg B]
        rw [hBzero, mul_zero]
    have hNzero : N = 0 := by
      dsimp only [N]
      rw [hPzero, mul_zero, zero_add]
      exact hWBzero
    have hquad :=
      fourCellEvenEndpointSeedRow_sq_le_polynomialCoshBorderQuadratic
        w hw hlocal heven hzero q p hq hp 0 η hη
    have hquad' : fourCellEvenEndpointSeedRow w ^ 2 ≤
        a * (L - 0 * P) ^ 2 + W * (A - 2 * 0 * B + 0 ^ 2 * D) := by
      simpa only [a, L, P, A, B, D, E, W] using hquad
    rw [hNzero, hKzero]
    norm_num at hquad' ⊢
    exact hquad'
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKzero)
    let s : ℝ := N / K
    have hquad :=
      fourCellEvenEndpointSeedRow_sq_le_polynomialCoshBorderQuadratic
        w hw hlocal heven hzero q p hq hp s η hη
    have hquad' : fourCellEvenEndpointSeedRow w ^ 2 ≤
        a * (L - s * P) ^ 2 + W * (A - 2 * s * B + s ^ 2 * D) := by
      simpa only [a, L, P, A, B, D, E, W] using hquad
    have hcompletion := coupled_scalar_cosh_border_completion
      a W L P A B D s hKpos.ne'
    have hcompletion' :
        a * (L - s * P) ^ 2 + W * (A - 2 * s * B + s ^ 2 * D) =
          a * L ^ 2 + W * A - N ^ 2 / K := by
      simpa [s, N, K] using hcompletion
    exact hquad'.trans_eq hcompletion'

/-- At the engineered allocation `η = 1/250`, the complete canonical
`P₁₄+` row charge uses at most one sixteenth of that tail's own
polar-free operator.  Thus the infinite endpoint-row block is not merely
positive: it is absorbed with a fixed quantitative reserve. -/
theorem canonicalTailNormBudget_rawCharge_le_one_sixteenth_polarFree_of_tailFourteen
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (heven : Function.Even r)
    (hlow : centeredLegendreMomentsVanishBelow r 14) :
    (1 + ((1 / 250 : ℝ)⁻¹)) * (360360 / 1171733 : ℝ) *
        fourCellEvenEndpointSeedCanonicalTailNormBudget *
          (centeredRawLogEnergy r / 4) ≤
      (1 / 16 : ℝ) * fourCellEvenPolarFreeOperator r := by
  have hE : 0 ≤ centeredRawLogEnergy r / 4 :=
    div_nonneg (centeredRawLogEnergy_nonnegative r) (by norm_num)
  have hcoefficient :
      (1 + ((1 / 250 : ℝ)⁻¹)) * (360360 / 1171733 : ℝ) *
          fourCellEvenEndpointSeedCanonicalTailNormBudget ≤
        (1 / 40 : ℝ) := by
    norm_num [fourCellEvenEndpointSeedCanonicalTailNormBudget]
  have hcharge := mul_le_mul_of_nonneg_right hcoefficient hE
  have htail :=
    two_fifths_rawEnergy_le_fourCellEvenPolarFreeOperator_of_tailFourteen
      r hr hlocal heven hlow
  have htailScaled :=
    mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 1 / 16)
  calc
    _ ≤ (1 / 40 : ℝ) * (centeredRawLogEnergy r / 4) := by
      simpa only [mul_assoc] using hcharge
    _ = (1 / 16 : ℝ) *
        ((2 / 5 : ℝ) * (centeredRawLogEnergy r / 4)) := by ring
    _ ≤ (1 / 16 : ℝ) * fourCellEvenPolarFreeOperator r :=
      htailScaled

/-- Structural cutoff-fourteen reduction of the universal endpoint row.
Only the seven even coordinates `P₀,P₂,…,P₁₂` remain in the
finite square; the whole infinite block is charged against one sixteenth of
its own polar-free quadratic form. -/
theorem fourCellEvenEndpointSeedRow_sq_le_251_div_250_lowThroughTwelve_add_one_sixteenth_tailPolarFree
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0) :
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      (251 / 250 : ℝ) *
          fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw ^ 2 +
        (1 / 16 : ℝ) * fourCellEvenPolarFreeOperator
          (centeredLegendreHigherResidual w hw 14) := by
  let r : ℝ → ℝ := centeredLegendreHigherResidual w hw 14
  have hr : Continuous r := by
    simpa only [r] using continuous_centeredLegendreHigherResidual w hw 14
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    simpa only [r] using
      locallyLipschitzOn_centeredLegendreHigherResidual w hw hlocal 14
  have hrEven : Function.Even r := by
    simpa only [r] using centeredLegendreHigherResidual_even w hw heven 14
  have hrGap : centeredLegendreMomentsVanishBelow r 14 := by
    simpa only [r] using
      centeredLegendreHigherResidual_momentsVanishBelow w hw 14
  have hbudget : 0 ≤ fourCellEvenEndpointSeedCanonicalTailNormBudget := by
    norm_num [fourCellEvenEndpointSeedCanonicalTailNormBudget]
  have hdual :
      (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter 0 0 x ^ 2) ≤
          fourCellEvenEndpointSeedCanonicalTailNormBudget := by
    simpa only [fourCellEvenEndpointSeedTailFourteenConstrainedRepresenter,
      zero_mul, sub_zero] using
        integral_endpointSeedTailFourteenRepresenter_zero_sq_le_rational
  have hrow :=
    fourCellEvenEndpointSeedRow_sq_le_coshConstrainedLowThroughTwelve_add_rawTail_of_norm
      w hw hlocal heven hzero 0 (by simp) 0
        fourCellEvenEndpointSeedCanonicalTailNormBudget hbudget hdual
        (1 / 250) (by norm_num)
  let T : ℝ :=
    (1 + ((1 / 250 : ℝ)⁻¹)) * (360360 / 1171733 : ℝ) *
      fourCellEvenEndpointSeedCanonicalTailNormBudget *
        (centeredRawLogEnergy r / 4)
  have hrow' : fourCellEvenEndpointSeedRow w ^ 2 ≤
      (251 / 250 : ℝ) *
          fourCellEvenEndpointSeedCanonicalLowThroughTwelveRow w hw ^ 2 + T := by
    dsimp only [T, r]
    norm_num at hrow
    ring_nf at hrow ⊢
    exact hrow
  have htail : T ≤
      (1 / 16 : ℝ) * fourCellEvenPolarFreeOperator r := by
    dsimp only [T]
    exact
      canonicalTailNormBudget_rawCharge_le_one_sixteenth_polarFree_of_tailFourteen
        r hr hrLocal hrEven hrGap
  dsimp only [r] at htail ⊢
  linarith only [hrow', htail]

/-- The canonical row is bounded by one explicit finite-row square and the
mass of the moment-eight residual, for every positive Young allocation.
This is an unconditional diagnostic interface; closing the universal Schur
step still requires a sharper weighted tail allocation than the unweighted
mass estimate alone supplies. -/
theorem fourCellEvenEndpointSeedRow_sq_le_canonicalLowTailBudget_of_positive
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (η : ℝ) (hη : 0 < η) :
    fourCellEvenEndpointSeedRow w ^ 2 ≤
      (1 + η) *
          fourCellEvenEndpointSeedCanonicalLowRow w hw ^ 2 +
        (1 + η⁻¹) * fourCellEvenEndpointSeedCanonicalTailNormBudget *
          fourCellEvenEndpointSeedCanonicalTailMass w hw := by
  let r : ℝ → ℝ := centeredLegendreHigherResidual w hw 8
  let L : ℝ := fourCellEvenEndpointSeedCanonicalLowRow w hw
  let T : ℝ := fourCellEvenEndpointSeedCanonicalTailRow r
  have hr : Continuous r := by
    simpa only [r] using continuous_centeredLegendreHigherResidual w hw 8
  have hrGap : centeredLegendreMomentsVanishBelow r 8 := by
    simpa only [r] using centeredLegendreHigherResidual_momentsVanishBelow w hw 8
  have hT : T ^ 2 ≤
      fourCellEvenEndpointSeedCanonicalTailNormBudget *
        (∫ x : ℝ in -1..1, r x ^ 2) := by
    simpa only [T] using
      fourCellEvenEndpointSeedCanonicalTailRow_sq_le_rational_mass r hr hrGap
  have hscale : 0 ≤ (1 + η⁻¹) := by
    have hinv : 0 < η⁻¹ := inv_pos.mpr hη
    positivity
  have hTscaled := mul_le_mul_of_nonneg_left hT hscale
  have hrow := fourCellEvenEndpointSeedRow_eq_canonicalCutoffEightLow_add_tail
    w hw hlocal heven hzero
  have hrow' : fourCellEvenEndpointSeedRow w = L + T := by
    dsimp only [L, T, fourCellEvenEndpointSeedCanonicalLowRow,
      fourCellEvenEndpointSeedCanonicalTailRow, r]
    simpa only [sub_eq_add_neg, add_assoc] using hrow
  rw [hrow']
  calc
    (L + T) ^ 2 ≤ (1 + η) * L ^ 2 + (1 + η⁻¹) * T ^ 2 :=
      add_sq_le_of_positive_youngParameter L T η hη
    _ ≤ (1 + η) * L ^ 2 +
        (1 + η⁻¹) * fourCellEvenEndpointSeedCanonicalTailNormBudget *
          (∫ x : ℝ in -1..1, r x ^ 2) := by
      nlinarith only [hTscaled]
    _ = (1 + η) *
          fourCellEvenEndpointSeedCanonicalLowRow w hw ^ 2 +
        (1 + η⁻¹) * fourCellEvenEndpointSeedCanonicalTailNormBudget *
          fourCellEvenEndpointSeedCanonicalTailMass w hw := by
      dsimp only [L, r, fourCellEvenEndpointSeedCanonicalTailMass]

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedUniversalClosureStructural
