import ArithmeticHodge.Analysis.YoshidaFourCellOddFiniteLegendreSolveStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51GalerkinRieszStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredL2Structural
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoEndpointBilinear
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP11CorrectedDeterminantAuditStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
open YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural

/-!
# Indexed `P51` Galerkin--Riesz certificate

The finite solve is the uniform inverse-defined solve on
`P3,P5,...,P51`.  This file adds the cutoff-independent assembly that was
previously written only for the five-coordinate `P13` reduction:

* exact positive-half Legendre projection at an arbitrary finite cutoff;
* a genuine indexed tail, orthogonal to `P1` and every retained coordinate;
* the Galerkin quadratic split and coercive middle reserve;
* specialization to the exact `q51` pivot and `P53+` residual dual.

No determinant or mode expansion enters the construction.
-/

private theorem contDiff_centeredP1_local : ContDiff ℝ 1 centeredP1 := by
  unfold centeredP1
  fun_prop

private theorem odd_centeredP1_local : Function.Odd centeredP1 := by
  intro x
  unfold centeredP1
  ring

private theorem odd_const_mul
    {v : ℝ → ℝ} (hv : Function.Odd v) (t : ℝ) :
    Function.Odd (fun x ↦ t * v x) := by
  intro x
  change t * v (-x) = -(t * v x)
  rw [hv]
  ring

private theorem centeredOddP1Coefficient_add_const_mul
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) (t : ℝ) :
    centeredOddP1Coefficient (u + fun x ↦ t * v x) =
      centeredOddP1Coefficient u + t * centeredOddP1Coefficient v := by
  unfold centeredOddP1Coefficient
  have huI : IntervalIntegrable (fun x : ℝ ↦ u x * centeredP1 x)
      volume (-1) 1 :=
    (hu.mul (by unfold centeredP1; fun_prop)).intervalIntegrable _ _
  have hvI : IntervalIntegrable (fun x : ℝ ↦
      t * (v x * centeredP1 x)) volume (-1) 1 :=
    (continuous_const.mul
      (hv.mul (by unfold centeredP1; fun_prop))).intervalIntegrable _ _
  rw [show (fun x : ℝ ↦
      (u + fun y ↦ t * v y) x * centeredP1 x) =
      fun x ↦ u x * centeredP1 x + t * (v x * centeredP1 x) by
    funext x
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add huI hvI,
    intervalIntegral.integral_const_mul]
  ring

/-! ## Exact finite Legendre projection -/

/-- Positive-half moment against retained coordinate `i`. -/
def fourCellOddFiniteRetainedMoment (N : ℕ) (r : ℝ → ℝ)
    (i : Fin (N + 1)) : ℝ :=
  ∫ x : ℝ in 0..1, fourCellOddFiniteRetainedBasis i x * r x

/-- The normalized coefficient of the positive-half `L²` projection. -/
def fourCellOddFiniteL2Coefficient (N : ℕ) (r : ℝ → ℝ)
    (i : Fin (N + 1)) : ℝ :=
  (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1) *
    fourCellOddFiniteRetainedMoment N r i

/-- Exact positive-half projection into `P3,...,P(2N+3)`. -/
def fourCellOddFiniteL2Projection (N : ℕ) (r : ℝ → ℝ) : ℝ → ℝ :=
  fourCellOddFiniteRetainedProfile N
    (fourCellOddFiniteL2Coefficient N r)

/-- Residual after removing the complete retained Legendre projection. -/
def fourCellOddFiniteL2Residual (N : ℕ) (r : ℝ → ℝ) : ℝ → ℝ :=
  r - fourCellOddFiniteL2Projection N r

/-- Indexed moment conditions for a genuine tail beyond the retained block.
The `P1` condition is stated in the production normalization, while every
retained odd Legendre condition is an exact positive-half moment. -/
def FourCellOddFiniteLegendreTailMoments (N : ℕ) (r : ℝ → ℝ) : Prop :=
  centeredOddP1Coefficient r = 0 ∧
    ∀ i : Fin (N + 1), fourCellOddFiniteRetainedMoment N r i = 0

theorem fourCellOddFiniteRetainedProfile_linear_combination
    (N : ℕ) (s t : ℝ) (a b : Fin (N + 1) → ℝ) :
    fourCellOddFiniteRetainedProfile N (fun i ↦ s * a i + t * b i) =
      fun x ↦ s * fourCellOddFiniteRetainedProfile N a x +
        t * fourCellOddFiniteRetainedProfile N b x := by
  funext x
  unfold fourCellOddFiniteRetainedProfile
  simp only [Finset.sum_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Exact diagonal positive-half Gram of two retained basis vectors. -/
theorem integral_zero_one_fourCellOddFiniteRetainedBasis_mul
    (N : ℕ) (i j : Fin (N + 1)) :
    (∫ x : ℝ in 0..1,
      fourCellOddFiniteRetainedBasis i x *
        fourCellOddFiniteRetainedBasis j x) =
      if i = j then
        1 / (2 * (fourCellOddFiniteRetainedDegree j : ℝ) + 1)
      else 0 := by
  let f : ℝ → ℝ := fun x ↦
    fourCellOddFiniteRetainedBasis i x *
      fourCellOddFiniteRetainedBasis j x
  have hf : Continuous f :=
    (contDiff_fourCellOddFiniteRetainedBasis i).continuous.mul
      (contDiff_fourCellOddFiniteRetainedBasis j).continuous
  have hfeven : Function.Even f := by
    intro x
    dsimp only [f]
    rw [odd_fourCellOddFiniteRetainedBasis i,
      odd_fourCellOddFiniteRetainedBasis j]
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    f (hf.intervalIntegrable _ _) hfeven
  by_cases hij : i = j
  · subst j
    have hgram := centeredLegendreL2Gram
      (fourCellOddFiniteRetainedDegree i)
      (fourCellOddFiniteRetainedDegree i)
    unfold centeredPolynomialPair at hgram
    rw [if_pos rfl] at hgram
    have hfull : (∫ x : ℝ in -1..1, f x) =
        2 / (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1) := by
      dsimp only [f]
      unfold fourCellOddFiniteRetainedBasis
      simpa only [Polynomial.eval_neg, neg_mul_neg] using hgram
    rw [if_pos rfl]
    rw [hfull] at hfold
    calc
      (∫ x : ℝ in 0..1,
          fourCellOddFiniteRetainedBasis i x *
            fourCellOddFiniteRetainedBasis i x) =
          (2 / (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1)) / 2 := by
        dsimp only [f] at hfold
        linarith
      _ = 1 / (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1) := by
        ring
  · have hdeg : fourCellOddFiniteRetainedDegree i ≠
        fourCellOddFiniteRetainedDegree j := by
      intro h
      exact hij (fourCellOddFiniteRetainedDegree_injective N h)
    have hgram := centeredLegendreL2Gram
      (fourCellOddFiniteRetainedDegree i)
      (fourCellOddFiniteRetainedDegree j)
    unfold centeredPolynomialPair at hgram
    rw [if_neg hdeg] at hgram
    have hfull : (∫ x : ℝ in -1..1, f x) = 0 := by
      dsimp only [f]
      unfold fourCellOddFiniteRetainedBasis
      simpa only [Polynomial.eval_neg, neg_mul_neg] using hgram
    rw [if_neg hij]
    rw [hfull] at hfold
    linarith

/-- Moment of an arbitrary retained profile against one basis coordinate. -/
theorem integral_zero_one_fourCellOddFiniteRetainedBasis_mul_profile
    (N : ℕ) (i : Fin (N + 1)) (a : Fin (N + 1) → ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddFiniteRetainedBasis i x *
        fourCellOddFiniteRetainedProfile N a x) =
      a i / (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1) := by
  classical
  rw [show (fun x : ℝ ↦
      fourCellOddFiniteRetainedBasis i x *
        fourCellOddFiniteRetainedProfile N a x) =
      fun x ↦ ∑ j, a j *
        (fourCellOddFiniteRetainedBasis i x *
          fourCellOddFiniteRetainedBasis j x) by
    funext x
    unfold fourCellOddFiniteRetainedProfile
    simp only [Finset.sum_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring,
    intervalIntegral.integral_finset_sum]
  · simp_rw [intervalIntegral.integral_const_mul,
      integral_zero_one_fourCellOddFiniteRetainedBasis_mul N]
    rw [Finset.sum_eq_single i]
    · simp
      ring
    · intro j hj hji
      rw [if_neg (Ne.symm hji)]
      ring
    · simp
  · intro j hj
    exact ((contDiff_fourCellOddFiniteRetainedBasis i).continuous.mul
      (contDiff_fourCellOddFiniteRetainedBasis j).continuous).intervalIntegrable
        _ _ |>.const_mul (a j)

theorem contDiff_fourCellOddFiniteL2Projection
    (N : ℕ) (r : ℝ → ℝ) :
    ContDiff ℝ 1 (fourCellOddFiniteL2Projection N r) :=
  contDiff_fourCellOddFiniteRetainedProfile N _

theorem odd_fourCellOddFiniteL2Projection
    (N : ℕ) (r : ℝ → ℝ) :
    Function.Odd (fourCellOddFiniteL2Projection N r) :=
  odd_fourCellOddFiniteRetainedProfile N _

theorem contDiff_fourCellOddFiniteL2Residual
    (N : ℕ) (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) :
    ContDiff ℝ 1 (fourCellOddFiniteL2Residual N r) :=
  hr.sub (contDiff_fourCellOddFiniteL2Projection N r)

theorem odd_fourCellOddFiniteL2Residual
    (N : ℕ) (r : ℝ → ℝ) (hr : Function.Odd r) :
    Function.Odd (fourCellOddFiniteL2Residual N r) := by
  intro x
  unfold fourCellOddFiniteL2Residual
  simp only [Pi.sub_apply]
  rw [hr, odd_fourCellOddFiniteL2Projection N r]
  ring

/-- Exact reconstruction after retaining all finite Legendre coordinates. -/
theorem fourCellOddFiniteL2Projection_add_residual
    (N : ℕ) (r : ℝ → ℝ) :
    fourCellOddFiniteL2Projection N r +
      fourCellOddFiniteL2Residual N r = r := by
  funext x
  unfold fourCellOddFiniteL2Residual
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- The projection residual has zero moment against every retained mode. -/
theorem fourCellOddFiniteL2Residual_retainedMoment_eq_zero
    (N : ℕ) (r : ℝ → ℝ) (hr : Continuous r)
    (i : Fin (N + 1)) :
    fourCellOddFiniteRetainedMoment N
      (fourCellOddFiniteL2Residual N r) i = 0 := by
  let D : ℝ := 2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1
  have hD : D ≠ 0 := by
    dsimp only [D]
    positivity
  have hri : IntervalIntegrable (fun x : ℝ ↦
      fourCellOddFiniteRetainedBasis i x * r x) volume 0 1 :=
    ((contDiff_fourCellOddFiniteRetainedBasis i).continuous.mul hr).intervalIntegrable
      _ _
  have hpi : IntervalIntegrable (fun x : ℝ ↦
      fourCellOddFiniteRetainedBasis i x *
        fourCellOddFiniteL2Projection N r x) volume 0 1 :=
    ((contDiff_fourCellOddFiniteRetainedBasis i).continuous.mul
      (contDiff_fourCellOddFiniteL2Projection N r).continuous).intervalIntegrable
        _ _
  unfold fourCellOddFiniteRetainedMoment fourCellOddFiniteL2Residual
  rw [show (fun x : ℝ ↦
      fourCellOddFiniteRetainedBasis i x *
        (r - fourCellOddFiniteL2Projection N r) x) =
      fun x ↦ fourCellOddFiniteRetainedBasis i x * r x -
        fourCellOddFiniteRetainedBasis i x *
          fourCellOddFiniteL2Projection N r x by
    funext x
    simp only [Pi.sub_apply]
    ring,
    intervalIntegral.integral_sub hri hpi,
    show fourCellOddFiniteL2Projection N r =
        fourCellOddFiniteRetainedProfile N
          (fourCellOddFiniteL2Coefficient N r) by rfl,
    integral_zero_one_fourCellOddFiniteRetainedBasis_mul_profile]
  unfold fourCellOddFiniteL2Coefficient fourCellOddFiniteRetainedMoment
  dsimp only [D] at hD ⊢
  field_simp [hD]
  ring

/-- Removing retained `P3+` coordinates preserves exact `P1` orthogonality. -/
theorem centeredOddP1Coefficient_fourCellOddFiniteL2Residual_eq_zero
    (N : ℕ) (r : ℝ → ℝ) (hr : Continuous r)
    (h1 : centeredOddP1Coefficient r = 0) :
    centeredOddP1Coefficient (fourCellOddFiniteL2Residual N r) = 0 := by
  have hp : Continuous (fourCellOddFiniteL2Projection N r) :=
    (contDiff_fourCellOddFiniteL2Projection N r).continuous
  have hrI : IntervalIntegrable (fun x : ℝ ↦ r x * centeredP1 x)
      volume (-1) 1 :=
    (hr.mul (by unfold centeredP1; fun_prop)).intervalIntegrable _ _
  have hpI : IntervalIntegrable (fun x : ℝ ↦
      fourCellOddFiniteL2Projection N r x * centeredP1 x)
      volume (-1) 1 :=
    (hp.mul (by unfold centeredP1; fun_prop)).intervalIntegrable _ _
  unfold fourCellOddFiniteL2Residual
  unfold centeredOddP1Coefficient at h1 ⊢
  rw [show (fun x : ℝ ↦
      (r - fourCellOddFiniteL2Projection N r) x * centeredP1 x) =
      fun x ↦ r x * centeredP1 x -
        fourCellOddFiniteL2Projection N r x * centeredP1 x by
    funext x
    simp only [Pi.sub_apply]
    ring,
    intervalIntegral.integral_sub hrI hpI]
  have hp1 :=
    centeredOddP1Coefficient_fourCellOddFiniteRetainedProfile_eq_zero
      N (fourCellOddFiniteL2Coefficient N r)
  unfold centeredOddP1Coefficient at hp1
  have hp1' : 3 / 2 * (∫ x : ℝ in -1..1,
      fourCellOddFiniteL2Projection N r x * centeredP1 x) = 0 := by
    simpa only [fourCellOddFiniteL2Projection] using hp1
  linarith

/-- The canonical residual is a genuine tail beyond the entire retained
family. -/
theorem fourCellOddFiniteL2Residual_tailMoments
    (N : ℕ) (r : ℝ → ℝ) (hr : Continuous r)
    (h1 : centeredOddP1Coefficient r = 0) :
    FourCellOddFiniteLegendreTailMoments N
      (fourCellOddFiniteL2Residual N r) := by
  constructor
  · exact centeredOddP1Coefficient_fourCellOddFiniteL2Residual_eq_zero
      N r hr h1
  · exact fourCellOddFiniteL2Residual_retainedMoment_eq_zero N r hr

/-! ## Orthogonal mass and coercive middle block -/

/-- Every retained profile is positive-half `L²`-orthogonal to a tail
satisfying the indexed moment equations. -/
theorem integral_zero_one_fourCellOddFiniteRetainedProfile_mul_tail_eq_zero
    (N : ℕ) (a : Fin (N + 1) → ℝ) (r : ℝ → ℝ)
    (hr : Continuous r)
    (hmom : ∀ i : Fin (N + 1),
      fourCellOddFiniteRetainedMoment N r i = 0) :
    (∫ x : ℝ in 0..1,
      fourCellOddFiniteRetainedProfile N a x * r x) = 0 := by
  classical
  rw [show (fun x : ℝ ↦
      fourCellOddFiniteRetainedProfile N a x * r x) =
      fun x ↦ ∑ i, a i *
        (fourCellOddFiniteRetainedBasis i x * r x) by
    funext x
    unfold fourCellOddFiniteRetainedProfile
    simp only [Finset.sum_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring,
    intervalIntegral.integral_finset_sum]
  · simp_rw [intervalIntegral.integral_const_mul]
    apply Finset.sum_eq_zero
    intro i hi
    rw [show (∫ x : ℝ in 0..1,
        fourCellOddFiniteRetainedBasis i x * r x) =
          fourCellOddFiniteRetainedMoment N r i by rfl,
      hmom i]
    ring
  · intro i hi
    exact ((contDiff_fourCellOddFiniteRetainedBasis i).continuous.mul hr)
      |>.intervalIntegrable 0 1 |>.const_mul (a i)

/-- Exact positive-half Pythagoras for a retained profile and a scaled
genuine tail. -/
theorem integral_zero_one_finiteRetained_add_scaled_tail_sq
    (N : ℕ) (a : Fin (N + 1) → ℝ) (t : ℝ) (r : ℝ → ℝ)
    (hr : Continuous r)
    (hmom : ∀ i : Fin (N + 1),
      fourCellOddFiniteRetainedMoment N r i = 0) :
    (∫ x : ℝ in 0..1,
      (fourCellOddFiniteRetainedProfile N a x + t * r x) ^ 2) =
      (∫ x : ℝ in 0..1,
        fourCellOddFiniteRetainedProfile N a x ^ 2) +
        t ^ 2 * (∫ x : ℝ in 0..1, r x ^ 2) := by
  let u := fourCellOddFiniteRetainedProfile N a
  have hu : Continuous u :=
    (contDiff_fourCellOddFiniteRetainedProfile N a).continuous
  have huuI : IntervalIntegrable (fun x : ℝ ↦ u x ^ 2) volume 0 1 :=
    (hu.pow 2).intervalIntegrable _ _
  have hurI : IntervalIntegrable (fun x : ℝ ↦
      2 * t * (u x * r x)) volume 0 1 :=
    (continuous_const.mul (hu.mul hr)).intervalIntegrable _ _
  have hrrI : IntervalIntegrable (fun x : ℝ ↦
      t ^ 2 * r x ^ 2) volume 0 1 :=
    (continuous_const.mul (hr.pow 2)).intervalIntegrable _ _
  have hcross : (∫ x : ℝ in 0..1, u x * r x) = 0 := by
    dsimp only [u]
    exact integral_zero_one_fourCellOddFiniteRetainedProfile_mul_tail_eq_zero
      N a r hr hmom
  change (∫ x : ℝ in 0..1, (u x + t * r x) ^ 2) = _
  rw [show (fun x : ℝ ↦ (u x + t * r x) ^ 2) =
      fun x ↦ u x ^ 2 + 2 * t * (u x * r x) + t ^ 2 * r x ^ 2 by
    funext x
    ring,
    intervalIntegral.integral_add (huuI.add hurI) hrrI,
    intervalIntegral.integral_add huuI hurI,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    hcross]
  dsimp only [u]
  ring

/-- Coercivity of the core keeps the complete scaled tail mass after an
arbitrary retained vector is added. -/
theorem kappa_mul_scaled_finiteLegendreTailMass_le_middleQuadratic
    (N : ℕ) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hcoercive : FourCellOddCorePositiveHalfCoerciveAt kappa)
    (a : Fin (N + 1) → ℝ) (t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (htail : FourCellOddFiniteLegendreTailMoments N r) :
    t ^ 2 * (kappa * (∫ x : ℝ in 0..1, r x ^ 2)) ≤
      fourCellOddCoreLocalQuadratic
        (fourCellOddFiniteRetainedProfile N a + fun x ↦ t * r x) := by
  let u := fourCellOddFiniteRetainedProfile N a
  let tr : ℝ → ℝ := fun x ↦ t * r x
  have hu : ContDiff ℝ 1 u :=
    contDiff_fourCellOddFiniteRetainedProfile N a
  have huodd : Function.Odd u :=
    odd_fourCellOddFiniteRetainedProfile N a
  have htr : ContDiff ℝ 1 tr := contDiff_const.mul hr
  have htrodd : Function.Odd tr := odd_const_mul hodd t
  have hu1 : centeredOddP1Coefficient u = 0 := by
    dsimp only [u]
    exact centeredOddP1Coefficient_fourCellOddFiniteRetainedProfile_eq_zero
      N a
  have hsum1 : centeredOddP1Coefficient (u + tr) = 0 := by
    dsimp only [tr]
    rw [centeredOddP1Coefficient_add_const_mul u r
      hu.continuous hr.continuous t, hu1, htail.1]
    ring
  have hcore := hcoercive (u + tr) (hu.add htr)
    (huodd.add htrodd) hsum1
  have hmass := integral_zero_one_finiteRetained_add_scaled_tail_sq
    N a t r hr.continuous htail.2
  have huMass : 0 ≤ ∫ x : ℝ in 0..1, u x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (u x))
  have hkLow : 0 ≤ kappa * (∫ x : ℝ in 0..1, u x ^ 2) :=
    mul_nonneg hkappa huMass
  dsimp only [tr] at hcore
  change kappa * (∫ x : ℝ in 0..1,
    (u + fun x ↦ t * r x) x ^ 2) ≤ _ at hcore
  change (∫ x : ℝ in 0..1, (u x + t * r x) ^ 2) =
    (∫ x : ℝ in 0..1, u x ^ 2) +
      t ^ 2 * (∫ x : ℝ in 0..1, r x ^ 2) at hmass
  have hlower :
      kappa * (t ^ 2 * (∫ x : ℝ in 0..1, r x ^ 2)) ≤
        kappa * (∫ x : ℝ in 0..1, (u x + t * r x) ^ 2) := by
    rw [hmass]
    nlinarith
  calc
    t ^ 2 * (kappa * (∫ x : ℝ in 0..1, r x ^ 2)) =
        kappa * (t ^ 2 * (∫ x : ℝ in 0..1, r x ^ 2)) := by ring
    _ ≤ kappa * (∫ x : ℝ in 0..1, (u x + t * r x) ^ 2) := hlower
    _ = kappa * (∫ x : ℝ in 0..1,
        (u + fun x ↦ t * r x) x ^ 2) := by rfl
    _ ≤ fourCellOddCoreLocalQuadratic
        (u + fun x ↦ t * r x) := hcore

/-! ## Cutoff-independent Galerkin--Riesz split -/

/-- Inverse-solved Galerkin residual at an arbitrary retained cutoff. -/
def fourCellOddFiniteSolvedGalerkinResidualProfile (N : ℕ) : ℝ → ℝ :=
  fourCellOddFiniteGalerkinResidualProfile N
    (fourCellOddFiniteRetainedSolution N)

/-- Exact scalar Schur pivot of the inverse-solved finite residual. -/
def fourCellOddFiniteSolvedGalerkinPivot (N : ℕ) : ℝ :=
  fourCellOddCoreLocalQuadratic
    (fourCellOddFiniteSolvedGalerkinResidualProfile N)

/-- Structural Schur-complement identity for the exact finite pivot.  This
isolates its sign as `Q(P1) - Q(projection)` without expanding the Gram. -/
theorem fourCellOddFiniteSolvedGalerkinPivot_eq_sub_projection (N : ℕ) :
    fourCellOddFiniteSolvedGalerkinPivot N =
      fourCellOddCoreLocalQuadratic centeredP1 -
        fourCellOddCoreLocalQuadratic
          (fourCellOddFiniteRetainedProfile N
            (fourCellOddFiniteRetainedSolution N)) := by
  let p := fourCellOddFiniteRetainedProfile N
    (fourCellOddFiniteRetainedSolution N)
  let q := fourCellOddFiniteSolvedGalerkinResidualProfile N
  let np : ℝ → ℝ := fun x ↦ (-1 : ℝ) * p x
  have hp : ContDiff ℝ 1 p :=
    contDiff_fourCellOddFiniteRetainedProfile N _
  have hpodd : Function.Odd p :=
    odd_fourCellOddFiniteRetainedProfile N _
  have hnp : ContDiff ℝ 1 np := contDiff_const.mul hp
  have hnpodd : Function.Odd np := odd_const_mul hpodd (-1)
  have hnormal := fourCellOddFiniteRetainedSolution_normal
    N (fourCellOddFiniteRetainedSolution N)
  have hself := fourCellOddCoreLocalBilinear_self_eq_quadratic
    p hp hpodd
  have hrow : fourCellOddCoreLocalBilinear centeredP1 p =
      fourCellOddCoreLocalQuadratic p := by
    dsimp only [p] at hnormal hself ⊢
    linarith
  have hqeq : q = centeredP1 + np := by
    funext x
    dsimp only [q, np, p]
    unfold fourCellOddFiniteSolvedGalerkinResidualProfile
      fourCellOddFiniteGalerkinResidualProfile
    simp only [Pi.add_apply]
    ring
  have hadd := fourCellOddCoreLocalQuadratic_add
    centeredP1 np contDiff_centeredP1_local.continuous hnp.continuous
  have hnpQ := fourCellOddCoreLocalQuadratic_const_mul p hp hpodd (-1)
  have hcross := fourCellOddCoreLocalBilinear_const_mul_right
    centeredP1 p contDiff_centeredP1_local hp odd_centeredP1_local hpodd (-1)
  unfold fourCellOddFiniteSolvedGalerkinPivot
  dsimp only [q] at hqeq
  rw [hqeq, hadd]
  dsimp only [np] at hnpQ hcross ⊢
  rw [hnpQ, hcross, hrow]
  ring

theorem contDiff_fourCellOddFiniteSolvedGalerkinResidualProfile (N : ℕ) :
    ContDiff ℝ 1 (fourCellOddFiniteSolvedGalerkinResidualProfile N) :=
  contDiff_fourCellOddFiniteGalerkinResidualProfile N _

theorem odd_fourCellOddFiniteSolvedGalerkinResidualProfile (N : ℕ) :
    Function.Odd (fourCellOddFiniteSolvedGalerkinResidualProfile N) :=
  odd_fourCellOddFiniteGalerkinResidualProfile N _

/-- The single analytic row left after the complete finite solve. -/
def FourCellOddFiniteSolvedGalerkinResidualL2Dual
    (N : ℕ) (kappa : ℝ) : Prop :=
  ∀ (r : ℝ → ℝ), ContDiff ℝ 1 r → Function.Odd r →
    FourCellOddFiniteLegendreTailMoments N r →
      fourCellOddCoreLocalBilinear
          (fourCellOddFiniteSolvedGalerkinResidualProfile N) r ^ 2 ≤
        fourCellOddFiniteSolvedGalerkinPivot N *
          (kappa * (∫ x : ℝ in 0..1, r x ^ 2))

/-- Exact quadratic split for the inverse-solved finite block.  The normal
equations kill the complete retained mixed row at once. -/
theorem fourCellOddCoreLocalQuadratic_finiteSolvedGalerkin_split
    (N : ℕ) (b : Fin (N + 1) → ℝ) (s t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r) :
    let q := fourCellOddFiniteSolvedGalerkinResidualProfile N
    let u := fourCellOddFiniteRetainedProfile N
      (fun i ↦ s * fourCellOddFiniteRetainedSolution N i + t * b i)
    fourCellOddCoreLocalQuadratic
        (fun x ↦ s * centeredP1 x +
          t * (fourCellOddFiniteRetainedProfile N b x + r x)) =
      fourCellOddCoreLocalQuadratic (u + fun x ↦ t * r x) +
        2 * s * t * fourCellOddCoreLocalBilinear q r +
          s ^ 2 * fourCellOddCoreLocalQuadratic q := by
  dsimp only
  let q := fourCellOddFiniteSolvedGalerkinResidualProfile N
  let u := fourCellOddFiniteRetainedProfile N
    (fun i ↦ s * fourCellOddFiniteRetainedSolution N i + t * b i)
  let sq : ℝ → ℝ := fun x ↦ s * q x
  let tr : ℝ → ℝ := fun x ↦ t * r x
  have hq : ContDiff ℝ 1 q := by
    dsimp only [q]
    exact contDiff_fourCellOddFiniteSolvedGalerkinResidualProfile N
  have hqodd : Function.Odd q := by
    dsimp only [q]
    exact odd_fourCellOddFiniteSolvedGalerkinResidualProfile N
  have hu : ContDiff ℝ 1 u := by
    dsimp only [u]
    exact contDiff_fourCellOddFiniteRetainedProfile N _
  have huodd : Function.Odd u := by
    dsimp only [u]
    exact odd_fourCellOddFiniteRetainedProfile N _
  have hsq : ContDiff ℝ 1 sq := contDiff_const.mul hq
  have hsqodd : Function.Odd sq := odd_const_mul hqodd s
  have htr : ContDiff ℝ 1 tr := contDiff_const.mul hr
  have htrodd : Function.Odd tr := odd_const_mul hodd t
  have hqu : fourCellOddCoreLocalBilinear q u = 0 := by
    dsimp only [q, u, fourCellOddFiniteSolvedGalerkinResidualProfile]
    exact fourCellOddFiniteRetainedSolution_orthogonal N _
  have hqtr : fourCellOddCoreLocalBilinear q tr =
      t * fourCellOddCoreLocalBilinear q r := by
    dsimp only [tr]
    exact fourCellOddCoreLocalBilinear_const_mul_right
      q r hq hr hqodd hodd t
  have hqadd : fourCellOddCoreLocalBilinear q (u + tr) =
      fourCellOddCoreLocalBilinear q u +
        fourCellOddCoreLocalBilinear q tr := by
    calc
      fourCellOddCoreLocalBilinear q (u + tr) =
          fourCellOddCoreLocalBilinear (u + tr) q :=
        fourCellOddCoreLocalBilinear_comm q (u + tr)
          hq.continuous (hu.add htr).continuous
      _ = fourCellOddCoreLocalBilinear u q +
            fourCellOddCoreLocalBilinear tr q :=
        fourCellOddCoreLocalBilinear_add_left
          u tr q hu htr hq huodd htrodd hqodd
      _ = fourCellOddCoreLocalBilinear q u +
            fourCellOddCoreLocalBilinear q tr := by
        rw [fourCellOddCoreLocalBilinear_comm u q
            hu.continuous hq.continuous,
          fourCellOddCoreLocalBilinear_comm tr q
            htr.continuous hq.continuous]
  have hcross : fourCellOddCoreLocalBilinear sq (u + tr) =
      s * t * fourCellOddCoreLocalBilinear q r := by
    dsimp only [sq]
    rw [fourCellOddCoreLocalBilinear_const_mul_left
      q (u + tr) hq (hu.add htr) hqodd (huodd.add htrodd) s,
      hqadd, hqu, hqtr]
    ring
  have hsqQ : fourCellOddCoreLocalQuadratic sq =
      s ^ 2 * fourCellOddCoreLocalQuadratic q := by
    dsimp only [sq]
    exact fourCellOddCoreLocalQuadratic_const_mul q hq hqodd s
  have huProfile : u = fun x ↦
      s * fourCellOddFiniteRetainedProfile N
          (fourCellOddFiniteRetainedSolution N) x +
        t * fourCellOddFiniteRetainedProfile N b x := by
    dsimp only [u]
    exact fourCellOddFiniteRetainedProfile_linear_combination
      N s t (fourCellOddFiniteRetainedSolution N) b
  have hreconstruct :
      (fun x ↦ s * centeredP1 x +
        t * (fourCellOddFiniteRetainedProfile N b x + r x)) =
        sq + (u + tr) := by
    funext x
    have hux := congrFun huProfile x
    dsimp only [q, sq, tr]
    unfold fourCellOddFiniteSolvedGalerkinResidualProfile
      fourCellOddFiniteGalerkinResidualProfile
    simp only [Pi.add_apply]
    rw [hux]
    ring
  rw [hreconstruct,
    fourCellOddCoreLocalQuadratic_add sq (u + tr)
      hsq.continuous (hu.add htr).continuous,
    hcross, hsqQ]
  dsimp only [q, u]
  ring

/-- A nonnegative finite pivot plus its genuine-tail dual proves the complete
`P1`-orthogonal form-dual inequality at any retained cutoff. -/
theorem fourCellOddP1OrthogonalFormDualBound_of_finiteSolvedGalerkinRiesz
    (N : ℕ) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hcoercive : FourCellOddCorePositiveHalfCoerciveAt kappa)
    (hpivot : 0 ≤ fourCellOddFiniteSolvedGalerkinPivot N)
    (hdual : FourCellOddFiniteSolvedGalerkinResidualL2Dual N kappa) :
    FourCellOddP1OrthogonalFormDualBound := by
  intro v hv hvodd hv1
  let b := fourCellOddFiniteL2Coefficient N v
  let r := fourCellOddFiniteL2Residual N v
  let q := fourCellOddFiniteSolvedGalerkinResidualProfile N
  have hr : ContDiff ℝ 1 r := by
    dsimp only [r]
    exact contDiff_fourCellOddFiniteL2Residual N v hv
  have hrodd : Function.Odd r := by
    dsimp only [r]
    exact odd_fourCellOddFiniteL2Residual N v hvodd
  have htail : FourCellOddFiniteLegendreTailMoments N r := by
    dsimp only [r]
    exact fourCellOddFiniteL2Residual_tailMoments
      N v hv.continuous hv1
  have hq : ContDiff ℝ 1 q := by
    dsimp only [q]
    exact contDiff_fourCellOddFiniteSolvedGalerkinResidualProfile N
  have hqodd : Function.Odd q := by
    dsimp only [q]
    exact odd_fourCellOddFiniteSolvedGalerkinResidualProfile N
  have hmass0 : 0 ≤ kappa * (∫ x : ℝ in 0..1, r x ^ 2) :=
    mul_nonneg hkappa
      (intervalIntegral.integral_nonneg (by norm_num)
        (fun x _hx ↦ sq_nonneg (r x)))
  have hresidualDual := hdual r hr hrodd htail
  have hpencil : ∀ s t : ℝ,
      0 ≤ fourCellOddCoreLocalQuadratic
        (fun x ↦ s * centeredP1 x + t * v x) := by
    intro s t
    let u := fourCellOddFiniteRetainedProfile N
      (fun i ↦ s * fourCellOddFiniteRetainedSolution N i + t * b i)
    have hmiddle :=
      kappa_mul_scaled_finiteLegendreTailMass_le_middleQuadratic
        N kappa hkappa hcoercive
        (fun i ↦ s * fourCellOddFiniteRetainedSolution N i + t * b i)
        t r hr hrodd htail
    have hbinary :=
      (real_quadratic_pencil_nonneg_iff
        (fourCellOddFiniteSolvedGalerkinPivot N)
        (kappa * (∫ x : ℝ in 0..1, r x ^ 2))
        (fourCellOddCoreLocalBilinear q r)).2
          ⟨hpivot, hmass0,
            by simpa only [q] using hresidualDual⟩ s t
    have hsplit :=
      fourCellOddCoreLocalQuadratic_finiteSolvedGalerkin_split
        N b s t r hr hrodd
    have hreconstruct :
        fourCellOddFiniteRetainedProfile N b + r = v := by
      dsimp only [b, r]
      exact fourCellOddFiniteL2Projection_add_residual N v
    have hprofile :
        (fun x ↦ s * centeredP1 x + t * v x) =
          (fun x ↦ s * centeredP1 x +
            t * (fourCellOddFiniteRetainedProfile N b x + r x)) := by
      funext x
      have hx := congrFun hreconstruct x
      simp only [Pi.add_apply] at hx
      rw [hx]
    rw [hprofile]
    dsimp only [q, u] at hsplit hmiddle hbinary ⊢
    unfold fourCellOddFiniteSolvedGalerkinPivot at hbinary
    rw [hsplit]
    linarith
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let B := fourCellOddCoreLocalQuadratic v
  let C := fourCellOddCoreLocalBilinear centeredP1 v
  have hquad : ∀ s t : ℝ,
      0 ≤ A * s ^ 2 + 2 * C * s * t + B * t ^ 2 := by
    intro s t
    have hnonneg := hpencil s t
    let sp : ℝ → ℝ := fun x ↦ s * centeredP1 x
    let tv : ℝ → ℝ := fun x ↦ t * v x
    have hsp : ContDiff ℝ 1 sp :=
      contDiff_const.mul contDiff_centeredP1_local
    have hspodd : Function.Odd sp := odd_const_mul odd_centeredP1_local s
    have htv : ContDiff ℝ 1 tv := contDiff_const.mul hv
    have htvodd : Function.Odd tv := odd_const_mul hvodd t
    have hsum : (fun x ↦ s * centeredP1 x + t * v x) = sp + tv := by
      funext x
      rfl
    rw [hsum,
      fourCellOddCoreLocalQuadratic_add sp tv
        hsp.continuous htv.continuous] at hnonneg
    have hspQ := fourCellOddCoreLocalQuadratic_const_mul
      centeredP1 contDiff_centeredP1_local odd_centeredP1_local s
    have htvQ := fourCellOddCoreLocalQuadratic_const_mul v hv hvodd t
    have hcross : fourCellOddCoreLocalBilinear sp tv =
        s * t * fourCellOddCoreLocalBilinear centeredP1 v := by
      dsimp only [sp, tv]
      rw [fourCellOddCoreLocalBilinear_const_mul_left
          centeredP1 (fun x ↦ t * v x)
            contDiff_centeredP1_local (contDiff_const.mul hv)
              odd_centeredP1_local (odd_const_mul hvodd t) s,
        fourCellOddCoreLocalBilinear_const_mul_right
          centeredP1 v contDiff_centeredP1_local hv
            odd_centeredP1_local hvodd t]
      ring
    rw [hspQ, htvQ, hcross] at hnonneg
    dsimp only [A, B, C]
    convert hnonneg using 1
    ring
  exact (real_quadratic_pencil_nonneg_iff A B C).1 hquad |>.2.2

/-- Certificate form of the cutoff-independent assembly. -/
def FourCellOddFiniteSolvedGalerkinRieszCertificate
    (N : ℕ) (kappa : ℝ) : Prop :=
  0 ≤ fourCellOddFiniteSolvedGalerkinPivot N ∧
    FourCellOddFiniteSolvedGalerkinResidualL2Dual N kappa

theorem fourCellOddP1OrthogonalFormDualBound_of_finiteSolvedGalerkinCertificate
    (N : ℕ) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hcoercive : FourCellOddCorePositiveHalfCoerciveAt kappa)
    (hcert : FourCellOddFiniteSolvedGalerkinRieszCertificate N kappa) :
    FourCellOddP1OrthogonalFormDualBound :=
  fourCellOddP1OrthogonalFormDualBound_of_finiteSolvedGalerkinRiesz
    N kappa hkappa hcoercive hcert.1 hcert.2

/-! ## Exact `P51` / `P53+` specialization -/

/-- The exact inverse-solved `q51 = P1 - proj(P3,...,P51)`. -/
def fourCellOddQ51 : ℝ → ℝ :=
  fourCellOddP51GalerkinResidualProfile

theorem fourCellOddQ51_eq :
    fourCellOddQ51 = fun x ↦ centeredP1 x -
      fourCellOddP51RetainedProfile
        fourCellOddP51RetainedSolution x := by
  rfl

theorem contDiff_fourCellOddQ51 : ContDiff ℝ 1 fourCellOddQ51 := by
  simpa only [fourCellOddQ51, fourCellOddP51GalerkinResidualProfile,
    fourCellOddP51RetainedSolution] using
      contDiff_fourCellOddFiniteSolvedGalerkinResidualProfile 24

theorem odd_fourCellOddQ51 : Function.Odd fourCellOddQ51 := by
  simpa only [fourCellOddQ51, fourCellOddP51GalerkinResidualProfile,
    fourCellOddP51RetainedSolution] using
      odd_fourCellOddFiniteSolvedGalerkinResidualProfile 24

/-- Core orthogonality of `q51` to the complete 25-coordinate retained
family. -/
theorem fourCellOddQ51_finiteOrthogonal
    (b : FourCellOddP51RetainedIndex → ℝ) :
    fourCellOddCoreLocalBilinear fourCellOddQ51
      (fourCellOddP51RetainedProfile b) = 0 := by
  have h := fourCellOddP51RetainedSolution_orthogonal b
  simpa only [fourCellOddQ51, fourCellOddP51GalerkinResidualProfile,
    fourCellOddP51RetainedProfile, fourCellOddP51RetainedSolution] using h

/-- Exact finite Schur pivot left after eliminating `P3,...,P51`. -/
def fourCellOddP51GalerkinPivot : ℝ :=
  fourCellOddCoreLocalQuadratic fourCellOddQ51

theorem fourCellOddP51GalerkinPivot_eq_sub_projection :
    fourCellOddP51GalerkinPivot =
      fourCellOddCoreLocalQuadratic centeredP1 -
        fourCellOddCoreLocalQuadratic
          (fourCellOddP51RetainedProfile
            fourCellOddP51RetainedSolution) := by
  simpa only [fourCellOddP51GalerkinPivot, fourCellOddQ51,
    fourCellOddP51GalerkinResidualProfile,
    fourCellOddP51RetainedProfile, fourCellOddP51RetainedSolution] using
      fourCellOddFiniteSolvedGalerkinPivot_eq_sub_projection 24

/-- The finite sign premise is named separately: positive definiteness of
the retained Gram does not alone decide this `P1` Schur complement. -/
def FourCellOddP51GalerkinPivotNonnegative : Prop :=
  0 ≤ fourCellOddP51GalerkinPivot

/-- Exact indexed moment hypotheses for the smooth odd `P53+` residual. -/
def FourCellOddP53PlusMomentConditions (r : ℝ → ℝ) : Prop :=
  centeredOddP1Coefficient r = 0 ∧
    ∀ i : FourCellOddP51RetainedIndex,
      (∫ x : ℝ in 0..1,
        fourCellOddFiniteRetainedBasis i x * r x) = 0

theorem fourCellOddP53PlusMomentConditions_iff
    (r : ℝ → ℝ) :
    FourCellOddP53PlusMomentConditions r ↔
      FourCellOddFiniteLegendreTailMoments 24 r := by
  rfl

/-- Sole infinite-dimensional proposition after the exact `P51` solve:
the `q51` row is tested only against the genuine `P53+` tail. -/
def FourCellOddP51GalerkinP53PlusResidualDual (kappa : ℝ) : Prop :=
  ∀ (r : ℝ → ℝ), ContDiff ℝ 1 r → Function.Odd r →
    FourCellOddP53PlusMomentConditions r →
      fourCellOddCoreLocalBilinear fourCellOddQ51 r ^ 2 ≤
        fourCellOddP51GalerkinPivot *
          (kappa * (∫ x : ℝ in 0..1, r x ^ 2))

theorem fourCellOddP51GalerkinP53PlusResidualDual_iff
    (kappa : ℝ) :
    FourCellOddP51GalerkinP53PlusResidualDual kappa ↔
      FourCellOddFiniteSolvedGalerkinResidualL2Dual 24 kappa := by
  rfl

/-- The complete P51 finite-plus-tail certificate. -/
def FourCellOddP51GalerkinRieszCertificate (kappa : ℝ) : Prop :=
  FourCellOddP51GalerkinPivotNonnegative ∧
    FourCellOddP51GalerkinP53PlusResidualDual kappa

/-- P51 certificate handoff to the complete `P1`-orthogonal core
Cauchy--Schwarz inequality. -/
theorem fourCellOddP1OrthogonalFormDualBound_of_P51GalerkinRieszCertificate
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hcoercive : FourCellOddCorePositiveHalfCoerciveAt kappa)
    (hcert : FourCellOddP51GalerkinRieszCertificate kappa) :
    FourCellOddP1OrthogonalFormDualBound := by
  apply fourCellOddP1OrthogonalFormDualBound_of_finiteSolvedGalerkinRiesz
    24 kappa hkappa hcoercive
  · exact hcert.1
  · exact hcert.2

/-- Requested production handoff: the P51 finite pivot and the exact P53+
tail dual imply the corrected `P11+` determinant frontier. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_P51GalerkinRieszCertificate
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hcoercive : FourCellOddCorePositiveHalfCoerciveAt kappa)
    (hcert : FourCellOddP51GalerkinRieszCertificate kappa) :
    FourCellOddP11CoupledRieszDefectNonnegative :=
  (fourCellOddP11CoupledRieszDefectNonnegative_iff_P1OrthogonalFormDual).2
    (fourCellOddP1OrthogonalFormDualBound_of_P51GalerkinRieszCertificate
      kappa hkappa hcoercive hcert)

/-- Production nineteen-twentieths specialization. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_nineteenTwentieths_P51Certificate
    (hcert : FourCellOddP51GalerkinRieszCertificate
      fourCellOddNineteenTwentiethsCoercivityConstant) :
    FourCellOddP11CoupledRieszDefectNonnegative :=
  fourCellOddP11CoupledRieszDefectNonnegative_of_P51GalerkinRieszCertificate
    fourCellOddNineteenTwentiethsCoercivityConstant
    fourCellOddNineteenTwentiethsCoercivityConstant_pos.le
    fourCellOddCorePositiveHalfCoerciveAt_nineteenTwentieths hcert

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51GalerkinRieszStructural
