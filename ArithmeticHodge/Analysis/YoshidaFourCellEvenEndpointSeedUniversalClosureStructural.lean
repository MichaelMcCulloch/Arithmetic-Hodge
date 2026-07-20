import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCombinedNormStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped Interval

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedUniversalClosureStructural

noncomputable section

open YoshidaConstantBounds
open ShiftedLegendreLogEnergyOrthogonalProjection
open UnitIntervalLogEnergyAffine
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicNineCanonicalProjectionStructural
open YoshidaFourCellEvenEndpointCoshSchurStructural
open YoshidaFourCellEvenEndpointCapacityCauchyStructural
open YoshidaFourCellEvenEndpointSeedCapacityCrossStructural
open YoshidaFourCellEvenEndpointSeedCombinedNormStructural
open YoshidaFourCellEvenEndpointSeedCutoffEightBridgeStructural
open YoshidaFourCellEvenEndpointSeedRegularRemainderStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellEvenZeroCoshCoupledCoreStructural
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
