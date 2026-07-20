import ArithmeticHodge.Analysis.YoshidaFourCellOddP51GalerkinRieszStructural

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51GalerkinPivotCoerciveReductionStructural

noncomputable section

open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
open YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# A coercive normal-residual certificate for the `P51` pivot

The exact `P51` solve need not be expanded or certified by twenty-five
successive scalar pivots.  Given any approximate coefficient vector `a`, the
difference from the exact solve lies in the `P3,...,P51` retained space.  The
already proved coercivity of that space bounds the energy of this correction
by the weighted squared residual of the normal equations.

Consequently the sign of the exact Schur pivot follows from one scalar
inequality involving the approximate residual.  This is an inverse-free
block argument; it does not enumerate matrix entries or determinants.
-/

/-- Residual obtained from an arbitrary approximate retained solve. -/
def fourCellOddP51ApproximateResidual
    (a : FourCellOddP51RetainedIndex → ℝ) : ℝ → ℝ :=
  fourCellOddFiniteGalerkinResidualProfile 24 a

/-- Weighted dual norm of the defect in all `P51` normal equations.  The
weight is dual to the exact diagonal positive-half Legendre mass. -/
def fourCellOddP51NormalResidualEnergy
    (a : FourCellOddP51RetainedIndex → ℝ) : ℝ :=
  ∑ i, (2 * (@fourCellOddFiniteRetainedDegree 24 i : ℝ) + 1) *
    fourCellOddCoreLocalBilinear
      (fourCellOddP51ApproximateResidual a)
      (fourCellOddFiniteRetainedBasis i) ^ 2

private theorem approximateResidual_eq_exact_add_correction
    (a : FourCellOddP51RetainedIndex → ℝ) :
    fourCellOddP51ApproximateResidual a =
      fourCellOddQ51 +
        fourCellOddP51RetainedProfile
          (fourCellOddP51RetainedSolution - a) := by
  funext x
  unfold fourCellOddP51ApproximateResidual fourCellOddQ51
    fourCellOddP51GalerkinResidualProfile
    fourCellOddP51RetainedProfile
    fourCellOddFiniteGalerkinResidualProfile
    fourCellOddFiniteRetainedProfile
  simp only [Finset.sum_apply, Pi.add_apply, Pi.sub_apply]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

private theorem correction_orthogonal_exact
    (a : FourCellOddP51RetainedIndex → ℝ) :
    fourCellOddCoreLocalBilinear fourCellOddQ51
      (fourCellOddP51RetainedProfile
        (fourCellOddP51RetainedSolution - a)) = 0 :=
  fourCellOddQ51_finiteOrthogonal _

private theorem approximateResidual_quadratic_split
    (a : FourCellOddP51RetainedIndex → ℝ) :
    fourCellOddCoreLocalQuadratic (fourCellOddP51ApproximateResidual a) =
      fourCellOddP51GalerkinPivot +
        fourCellOddCoreLocalQuadratic
          (fourCellOddP51RetainedProfile
            (fourCellOddP51RetainedSolution - a)) := by
  let d := fourCellOddP51RetainedProfile
    (fourCellOddP51RetainedSolution - a)
  have hd : ContDiff ℝ 1 d := by
    dsimp only [d, fourCellOddP51RetainedProfile]
    exact contDiff_fourCellOddFiniteRetainedProfile 24 _
  rw [approximateResidual_eq_exact_add_correction a,
    fourCellOddCoreLocalQuadratic_add fourCellOddQ51 d
      contDiff_fourCellOddQ51.continuous hd.continuous]
  have horth := correction_orthogonal_exact a
  change fourCellOddCoreLocalBilinear fourCellOddQ51 d = 0 at horth
  rw [horth]
  unfold fourCellOddP51GalerkinPivot
  ring

private theorem approximate_normal_row_eq_correction_row
    (a : FourCellOddP51RetainedIndex → ℝ)
    (i : FourCellOddP51RetainedIndex) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP51ApproximateResidual a)
        (fourCellOddFiniteRetainedBasis i) =
      fourCellOddCoreLocalBilinear
        (fourCellOddP51RetainedProfile
          (fourCellOddP51RetainedSolution - a))
        (fourCellOddFiniteRetainedBasis i) := by
  let d := fourCellOddP51RetainedProfile
    (fourCellOddP51RetainedSolution - a)
  have hd : ContDiff ℝ 1 d := by
    dsimp only [d, fourCellOddP51RetainedProfile]
    exact contDiff_fourCellOddFiniteRetainedProfile 24 _
  have hdodd : Function.Odd d := by
    dsimp only [d, fourCellOddP51RetainedProfile]
    exact odd_fourCellOddFiniteRetainedProfile 24 _
  have hbasis : fourCellOddP51RetainedProfile
      (fun j ↦ if j = i then 1 else 0) =
      fourCellOddFiniteRetainedBasis i := by
    funext x
    unfold fourCellOddP51RetainedProfile fourCellOddFiniteRetainedProfile
    simp
  rw [approximateResidual_eq_exact_add_correction a,
    fourCellOddCoreLocalBilinear_add_left fourCellOddQ51 d
      (fourCellOddFiniteRetainedBasis i)
      contDiff_fourCellOddQ51 hd
      (contDiff_fourCellOddFiniteRetainedBasis i)
      odd_fourCellOddQ51 hdodd
      (odd_fourCellOddFiniteRetainedBasis i),
    ← hbasis,
    fourCellOddQ51_finiteOrthogonal
      (fun j ↦ if j = i then 1 else 0)]
  ring

private theorem correction_quadratic_eq_weighted_rows
    (a : FourCellOddP51RetainedIndex → ℝ) :
    fourCellOddCoreLocalQuadratic
        (fourCellOddP51RetainedProfile
          (fourCellOddP51RetainedSolution - a)) =
      ∑ i, (fourCellOddP51RetainedSolution - a) i *
        fourCellOddCoreLocalBilinear
          (fourCellOddP51ApproximateResidual a)
          (fourCellOddFiniteRetainedBasis i) := by
  let c := fourCellOddP51RetainedSolution - a
  let d := fourCellOddP51RetainedProfile c
  have hd : ContDiff ℝ 1 d := by
    dsimp only [d, fourCellOddP51RetainedProfile]
    exact contDiff_fourCellOddFiniteRetainedProfile 24 _
  have hdodd : Function.Odd d := by
    dsimp only [d, fourCellOddP51RetainedProfile]
    exact odd_fourCellOddFiniteRetainedProfile 24 _
  have hself := fourCellOddCoreLocalBilinear_self_eq_quadratic d hd hdodd
  have hexpand := fourCellOddCoreLocalBilinear_finiteRetainedProfile_left
    24 c d hd hdodd
  dsimp only [d, c, fourCellOddP51RetainedProfile] at hself hexpand ⊢
  rw [← hself, hexpand]
  apply Finset.sum_congr rfl
  intro i hi
  have hrow := approximate_normal_row_eq_correction_row a i
  change fourCellOddCoreLocalBilinear
      (fourCellOddP51ApproximateResidual a)
      (fourCellOddFiniteRetainedBasis i) =
    fourCellOddCoreLocalBilinear
      (fourCellOddFiniteRetainedProfile 24
        (fourCellOddP51RetainedSolution - a))
      (fourCellOddFiniteRetainedBasis i) at hrow
  rw [fourCellOddCoreLocalBilinear_comm
      (fourCellOddFiniteRetainedBasis i)
      (fourCellOddFiniteRetainedProfile 24
        (fourCellOddP51RetainedSolution - a))
      (contDiff_fourCellOddFiniteRetainedBasis i).continuous
      (contDiff_fourCellOddFiniteRetainedProfile 24 _).continuous,
    ← hrow]

private theorem correction_mass_eq_weighted_coefficients
    (a : FourCellOddP51RetainedIndex → ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddP51RetainedProfile
        (fourCellOddP51RetainedSolution - a) x ^ 2) =
      ∑ i, (fourCellOddP51RetainedSolution - a) i ^ 2 /
        (2 * (@fourCellOddFiniteRetainedDegree 24 i : ℝ) + 1) := by
  simpa only [fourCellOddP51RetainedProfile] using
    integral_zero_one_fourCellOddFiniteRetainedProfile_sq
      24 (fourCellOddP51RetainedSolution - a)

private theorem correction_energy_nonneg
    (a : FourCellOddP51RetainedIndex → ℝ) :
    0 ≤ fourCellOddCoreLocalQuadratic
      (fourCellOddP51RetainedProfile
        (fourCellOddP51RetainedSolution - a)) := by
  let d := fourCellOddP51RetainedProfile
    (fourCellOddP51RetainedSolution - a)
  have hcoercive := fourCellOddCorePositiveHalfCoerciveAt_rationalFloor
    d
    (by
      dsimp only [d, fourCellOddP51RetainedProfile]
      exact contDiff_fourCellOddFiniteRetainedProfile 24 _)
    (by
      dsimp only [d, fourCellOddP51RetainedProfile]
      exact odd_fourCellOddFiniteRetainedProfile 24 _)
    (by
      dsimp only [d, fourCellOddP51RetainedProfile]
      exact centeredOddP1Coefficient_fourCellOddFiniteRetainedProfile_eq_zero
        24 _)
  have hmass : 0 ≤ ∫ x : ℝ in 0..1, d x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (d x))
  exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 343 / 12500) hmass).trans
    hcoercive

/-- The correction from an approximate solve to the exact `P51` solve is
bounded by the dual norm of its normal-equation residual at any available
positive coercivity constant. -/
theorem fourCellOddP51_correction_energy_le_normalResidualEnergy_div
    (a : FourCellOddP51RetainedIndex → ℝ) (kappa : ℝ)
    (hkappa : 0 < kappa)
    (hcoercive : FourCellOddCorePositiveHalfCoerciveAt kappa) :
    fourCellOddCoreLocalQuadratic
        (fourCellOddP51RetainedProfile
          (fourCellOddP51RetainedSolution - a)) ≤
      fourCellOddP51NormalResidualEnergy a / kappa := by
  let c := fourCellOddP51RetainedSolution - a
  let d := fourCellOddP51RetainedProfile c
  let E := fourCellOddCoreLocalQuadratic d
  let M := ∑ i, c i ^ 2 /
    (2 * (@fourCellOddFiniteRetainedDegree 24 i : ℝ) + 1)
  let R := fourCellOddP51NormalResidualEnergy a
  have hden (i : FourCellOddP51RetainedIndex) :
      0 < 2 * (@fourCellOddFiniteRetainedDegree 24 i : ℝ) + 1 := by
    positivity
  have hsqrt (i : FourCellOddP51RetainedIndex) :
      0 < Real.sqrt (2 * (@fourCellOddFiniteRetainedDegree 24 i : ℝ) + 1) :=
    Real.sqrt_pos.2 (hden i)
  have hmul (i : FourCellOddP51RetainedIndex) :
      (c i / Real.sqrt
          (2 * (@fourCellOddFiniteRetainedDegree 24 i : ℝ) + 1)) *
        (Real.sqrt
            (2 * (@fourCellOddFiniteRetainedDegree 24 i : ℝ) + 1) *
          fourCellOddCoreLocalBilinear
            (fourCellOddP51ApproximateResidual a)
            (fourCellOddFiniteRetainedBasis i)) =
      c i * fourCellOddCoreLocalBilinear
        (fourCellOddP51ApproximateResidual a)
        (fourCellOddFiniteRetainedBasis i) := by
    field_simp [(hsqrt i).ne']
  have hleft (i : FourCellOddP51RetainedIndex) :
      (c i / Real.sqrt
          (2 * (@fourCellOddFiniteRetainedDegree 24 i : ℝ) + 1)) ^ 2 =
        c i ^ 2 /
          (2 * (@fourCellOddFiniteRetainedDegree 24 i : ℝ) + 1) := by
    rw [div_pow, Real.sq_sqrt (hden i).le]
  have hright (i : FourCellOddP51RetainedIndex) :
      (Real.sqrt
          (2 * (@fourCellOddFiniteRetainedDegree 24 i : ℝ) + 1) *
        fourCellOddCoreLocalBilinear
          (fourCellOddP51ApproximateResidual a)
          (fourCellOddFiniteRetainedBasis i)) ^ 2 =
        (2 * (@fourCellOddFiniteRetainedDegree 24 i : ℝ) + 1) *
          fourCellOddCoreLocalBilinear
            (fourCellOddP51ApproximateResidual a)
            (fourCellOddFiniteRetainedBasis i) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hden i).le]
  have hcauchy : E ^ 2 ≤ M * R := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i ↦ c i / Real.sqrt
        (2 * (@fourCellOddFiniteRetainedDegree 24 i : ℝ) + 1))
      (fun i ↦ Real.sqrt
          (2 * (@fourCellOddFiniteRetainedDegree 24 i : ℝ) + 1) *
        fourCellOddCoreLocalBilinear
          (fourCellOddP51ApproximateResidual a)
          (fourCellOddFiniteRetainedBasis i))
    simp_rw [hmul, hleft, hright] at h
    rw [show E = ∑ i, c i *
        fourCellOddCoreLocalBilinear
          (fourCellOddP51ApproximateResidual a)
          (fourCellOddFiniteRetainedBasis i) by
      dsimp only [E, d, c]
      exact correction_quadratic_eq_weighted_rows a]
    simpa only [M, R, fourCellOddP51NormalResidualEnergy] using h
  have hcoercive' : kappa * M ≤ E := by
    have h := hcoercive
      d
      (by
        dsimp only [d, fourCellOddP51RetainedProfile]
        exact contDiff_fourCellOddFiniteRetainedProfile 24 _)
      (by
        dsimp only [d, fourCellOddP51RetainedProfile]
        exact odd_fourCellOddFiniteRetainedProfile 24 _)
      (by
        dsimp only [d, fourCellOddP51RetainedProfile]
        exact centeredOddP1Coefficient_fourCellOddFiniteRetainedProfile_eq_zero
          24 _)
    rw [correction_mass_eq_weighted_coefficients a] at h
    simpa only [d, c, M, E] using h
  have hE : 0 ≤ E := by
    dsimp only [E, d, c]
    exact correction_energy_nonneg a
  have hR : 0 ≤ R := by
    dsimp only [R, fourCellOddP51NormalResidualEnergy]
    exact Finset.sum_nonneg (fun i _hi ↦
      mul_nonneg (hden i).le (sq_nonneg _))
  have hcoerciveR : kappa * M * R ≤ E * R :=
    mul_le_mul_of_nonneg_right hcoercive' hR
  have hcauchyScaled : kappa * E ^ 2 ≤ kappa * (M * R) :=
    mul_le_mul_of_nonneg_left hcauchy hkappa.le
  have hER : kappa * E ≤ R := by
    by_cases hEzero : E = 0
    · rw [hEzero]
      simpa using hR
    · have hEpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hEzero)
      nlinarith
  apply (le_div_iff₀ hkappa).2
  dsimp only [E, R, d, c] at hER ⊢
  nlinarith

/-- Exact-constant specialization of the correction estimate. -/
theorem fourCellOddP51_correction_energy_le_normalResidualEnergy_div_exact :
    ∀ a : FourCellOddP51RetainedIndex → ℝ,
    fourCellOddCoreLocalQuadratic
        (fourCellOddP51RetainedProfile
          (fourCellOddP51RetainedSolution - a)) ≤
      fourCellOddP51NormalResidualEnergy a /
        fourCellOddNineteenTwentiethsCoercivityConstant := by
  intro a
  exact fourCellOddP51_correction_energy_le_normalResidualEnergy_div
    a fourCellOddNineteenTwentiethsCoercivityConstant
      fourCellOddNineteenTwentiethsCoercivityConstant_pos
      fourCellOddCorePositiveHalfCoerciveAt_nineteenTwentieths

/-- Non-strict single-scalar certificate for the production pivot. -/
theorem fourCellOddP51GalerkinPivotNonnegative_of_approximateResidual_le
    (a : FourCellOddP51RetainedIndex → ℝ)
    (hcertificate :
      fourCellOddP51NormalResidualEnergy a ≤
        fourCellOddNineteenTwentiethsCoercivityConstant *
          fourCellOddCoreLocalQuadratic
            (fourCellOddP51ApproximateResidual a)) :
    FourCellOddP51GalerkinPivotNonnegative := by
  have hcorrection :=
    fourCellOddP51_correction_energy_le_normalResidualEnergy_div_exact a
  have hkappa := fourCellOddNineteenTwentiethsCoercivityConstant_pos
  have hsmall :
      fourCellOddCoreLocalQuadratic
          (fourCellOddP51RetainedProfile
            (fourCellOddP51RetainedSolution - a)) ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP51ApproximateResidual a) := by
    calc
      fourCellOddCoreLocalQuadratic
          (fourCellOddP51RetainedProfile
            (fourCellOddP51RetainedSolution - a)) ≤
          fourCellOddP51NormalResidualEnergy a /
            fourCellOddNineteenTwentiethsCoercivityConstant := hcorrection
      _ ≤ fourCellOddCoreLocalQuadratic
          (fourCellOddP51ApproximateResidual a) :=
        (div_le_iff₀ hkappa).2 (by simpa [mul_comm] using hcertificate)
  rw [approximateResidual_quadratic_split a] at hsmall
  change 0 ≤ fourCellOddP51GalerkinPivot
  linarith

/-- Single-scalar sufficient condition for strict positivity of the exact
`P51` Schur pivot.  Any structural approximate solve may be used. -/
theorem fourCellOddP51GalerkinPivot_pos_of_approximateResidual
    (a : FourCellOddP51RetainedIndex → ℝ)
    (hcertificate :
      fourCellOddP51NormalResidualEnergy a <
        (343 / 12500 : ℝ) *
          fourCellOddCoreLocalQuadratic
            (fourCellOddP51ApproximateResidual a)) :
    0 < fourCellOddP51GalerkinPivot := by
  have hcorrection :=
    fourCellOddP51_correction_energy_le_normalResidualEnergy_div
      a (343 / 12500 : ℝ) (by norm_num)
        fourCellOddCorePositiveHalfCoerciveAt_rationalFloor
  have hfloor : (0 : ℝ) < 343 / 12500 := by norm_num
  have hsmall :
      fourCellOddCoreLocalQuadratic
          (fourCellOddP51RetainedProfile
            (fourCellOddP51RetainedSolution - a)) <
        fourCellOddCoreLocalQuadratic
          (fourCellOddP51ApproximateResidual a) := by
    calc
      fourCellOddCoreLocalQuadratic
          (fourCellOddP51RetainedProfile
            (fourCellOddP51RetainedSolution - a)) ≤
          fourCellOddP51NormalResidualEnergy a / (343 / 12500 : ℝ) :=
        hcorrection
      _ < fourCellOddCoreLocalQuadratic
          (fourCellOddP51ApproximateResidual a) :=
        (div_lt_iff₀ hfloor).2 (by simpa [mul_comm] using hcertificate)
  rw [approximateResidual_quadratic_split a] at hsmall
  linarith

/-- The same scalar certificate discharges the production proposition. -/
theorem fourCellOddP51GalerkinPivotNonnegative_of_approximateResidual
    (a : FourCellOddP51RetainedIndex → ℝ)
    (hcertificate :
      fourCellOddP51NormalResidualEnergy a <
        (343 / 12500 : ℝ) *
          fourCellOddCoreLocalQuadratic
            (fourCellOddP51ApproximateResidual a)) :
    FourCellOddP51GalerkinPivotNonnegative :=
  (fourCellOddP51GalerkinPivot_pos_of_approximateResidual
    a hcertificate).le

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51GalerkinPivotCoerciveReductionStructural
