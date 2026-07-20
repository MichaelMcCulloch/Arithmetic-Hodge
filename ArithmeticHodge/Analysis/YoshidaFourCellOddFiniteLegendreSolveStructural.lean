import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
import ArithmeticHodge.Analysis.ShiftedLegendreCenteredL2Structural
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

open MeasureTheory Polynomial Real Set Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddFiniteLegendreSolveStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural

/-!
# Uniform finite solve for retained odd Legendre modes

For every `N`, this file retains the family

`P3, P5, ..., P(2N+3)`

on the index type `Fin (N + 1)`.  Its exact diagonal Legendre mass and the
existing `P1`-orthogonal core coercivity prove nonsingularity of the finite
core Gram.  The construction therefore reaches `P51` at `N = 24` without
any determinant expansion or degree-by-degree module ladder.
-/

/-- Degree of retained coordinate `i`: `3,5,7,...`. -/
def fourCellOddFiniteRetainedDegree {N : ℕ} (i : Fin (N + 1)) : ℕ :=
  2 * (i : ℕ) + 3

theorem fourCellOddFiniteRetainedDegree_injective (N : ℕ) :
    Function.Injective
      (@fourCellOddFiniteRetainedDegree N) := by
  intro i j hij
  apply Fin.ext
  unfold fourCellOddFiniteRetainedDegree at hij
  omega

theorem fourCellOddFiniteRetainedDegree_last (N : ℕ) :
    fourCellOddFiniteRetainedDegree (Fin.last N) = 2 * N + 3 := by
  simp [fourCellOddFiniteRetainedDegree]

/-- The production-sign centered odd Legendre basis vector at coordinate
`i`. -/
def fourCellOddFiniteRetainedBasis {N : ℕ}
    (i : Fin (N + 1)) (x : ℝ) : ℝ :=
  -(centeredShiftedLegendreReal
      (fourCellOddFiniteRetainedDegree i)).eval x

theorem contDiff_fourCellOddFiniteRetainedBasis {N : ℕ}
    (i : Fin (N + 1)) :
    ContDiff ℝ 1 (fourCellOddFiniteRetainedBasis i) := by
  unfold fourCellOddFiniteRetainedBasis
  exact (centeredShiftedLegendreReal
    (fourCellOddFiniteRetainedDegree i)).contDiff_aeval (𝕜 := ℝ) 1 |>.neg

theorem odd_fourCellOddFiniteRetainedBasis {N : ℕ}
    (i : Fin (N + 1)) :
    Function.Odd (fourCellOddFiniteRetainedBasis i) := by
  intro x
  unfold fourCellOddFiniteRetainedBasis
  rw [eval_centeredShiftedLegendreReal_neg]
  rw [show (-1 : ℝ) ^ fourCellOddFiniteRetainedDegree i = -1 by
    unfold fourCellOddFiniteRetainedDegree
    rw [pow_add, pow_mul]
    norm_num]
  ring

/-- A coefficient vector interpreted in the complete retained family. -/
def fourCellOddFiniteRetainedProfile (N : ℕ)
    (a : Fin (N + 1) → ℝ) : ℝ → ℝ :=
  ∑ i, fun x ↦ a i * fourCellOddFiniteRetainedBasis i x

private theorem contDiff_fourCellOddFiniteRetainedPartialProfile
    {N : ℕ} (a : Fin (N + 1) → ℝ) (s : Finset (Fin (N + 1))) :
    ContDiff ℝ 1 (s.sum fun i ↦
      fun x ↦ a i * fourCellOddFiniteRetainedBasis i x) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (contDiff_const.mul
        (contDiff_fourCellOddFiniteRetainedBasis i)).add ih

private theorem odd_fourCellOddFiniteRetainedPartialProfile
    {N : ℕ} (a : Fin (N + 1) → ℝ) (s : Finset (Fin (N + 1))) :
    Function.Odd (s.sum fun i ↦
      fun x ↦ a i * fourCellOddFiniteRetainedBasis i x) := by
  induction s using Finset.induction_on with
  | empty =>
      intro x
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      apply Function.Odd.add
      · intro x
        change a i * fourCellOddFiniteRetainedBasis i (-x) =
          -(a i * fourCellOddFiniteRetainedBasis i x)
        rw [odd_fourCellOddFiniteRetainedBasis]
        ring
      · exact ih

theorem contDiff_fourCellOddFiniteRetainedProfile (N : ℕ)
    (a : Fin (N + 1) → ℝ) :
    ContDiff ℝ 1 (fourCellOddFiniteRetainedProfile N a) := by
  exact contDiff_fourCellOddFiniteRetainedPartialProfile a Finset.univ

theorem odd_fourCellOddFiniteRetainedProfile (N : ℕ)
    (a : Fin (N + 1) → ℝ) :
    Function.Odd (fourCellOddFiniteRetainedProfile N a) := by
  exact odd_fourCellOddFiniteRetainedPartialProfile a Finset.univ

private def fourCellOddFiniteRetainedPolynomial (N : ℕ)
    (a : Fin (N + 1) → ℝ) : ℝ[X] :=
  ∑ i, a i •
    (-(centeredShiftedLegendreReal
      (fourCellOddFiniteRetainedDegree i)))

private theorem fourCellOddFiniteRetainedPolynomial_eval (N : ℕ)
    (a : Fin (N + 1) → ℝ) (x : ℝ) :
    (fourCellOddFiniteRetainedPolynomial N a).eval x =
      fourCellOddFiniteRetainedProfile N a x := by
  unfold fourCellOddFiniteRetainedPolynomial
    fourCellOddFiniteRetainedProfile fourCellOddFiniteRetainedBasis
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_smul,
    Polynomial.eval_neg, Finset.sum_apply, smul_eq_mul]

private theorem centeredPolynomialPair_add_left_local
    (p q r : ℝ[X]) :
    centeredPolynomialPair (p + q) r =
      centeredPolynomialPair p r + centeredPolynomialPair q r := by
  unfold centeredPolynomialPair
  simp only [Polynomial.eval_add, add_mul]
  exact intervalIntegral.integral_add
    ((p.continuous.mul r.continuous).intervalIntegrable _ _)
    ((q.continuous.mul r.continuous).intervalIntegrable _ _)

private theorem centeredPolynomialPair_sum_left_local
    {ι : Type} [DecidableEq ι] (s : Finset ι)
    (p : ι → ℝ[X]) (q : ℝ[X]) :
    centeredPolynomialPair (s.sum p) q =
      s.sum (fun i ↦ centeredPolynomialPair (p i) q) := by
  induction s using Finset.induction_on with
  | empty => simp [centeredPolynomialPair]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, centeredPolynomialPair_add_left_local,
        ih, Finset.sum_insert hi]

private theorem centeredPolynomialPair_sum_right_local
    {ι : Type} [DecidableEq ι] (s : Finset ι)
    (p : ℝ[X]) (q : ι → ℝ[X]) :
    centeredPolynomialPair p (s.sum q) =
      s.sum (fun i ↦ centeredPolynomialPair p (q i)) := by
  rw [centeredPolynomialPair_comm]
  rw [centeredPolynomialPair_sum_left_local]
  apply Finset.sum_congr rfl
  intro i hi
  exact centeredPolynomialPair_comm _ _

private theorem centeredPolynomialPair_smul_left_local
    (c : ℝ) (p q : ℝ[X]) :
    centeredPolynomialPair (c • p) q =
      c * centeredPolynomialPair p q := by
  unfold centeredPolynomialPair
  rw [show (fun x : ℝ ↦ (c • p).eval x * q.eval x) =
      fun x ↦ c * (p.eval x * q.eval x) by
    funext x
    simp only [Polynomial.eval_smul, smul_eq_mul]
    ring,
    intervalIntegral.integral_const_mul]

private theorem centeredPolynomialPair_smul_right_local
    (c : ℝ) (p q : ℝ[X]) :
    centeredPolynomialPair p (c • q) =
      c * centeredPolynomialPair p q := by
  rw [centeredPolynomialPair_comm,
    centeredPolynomialPair_smul_left_local,
    centeredPolynomialPair_comm q p]

private theorem centeredPolynomialPair_negLegendre
    (m n : ℕ) :
    centeredPolynomialPair
        (-(centeredShiftedLegendreReal m))
        (-(centeredShiftedLegendreReal n)) =
      if m = n then 2 / (2 * (n : ℝ) + 1) else 0 := by
  have h := centeredLegendreL2Gram m n
  unfold centeredPolynomialPair at h ⊢
  simpa only [Polynomial.eval_neg, neg_mul_neg] using h

private theorem centeredPolynomialPair_finiteRetainedBasis
    {N : ℕ} (i j : Fin (N + 1)) :
    centeredPolynomialPair
        (-(centeredShiftedLegendreReal
          (fourCellOddFiniteRetainedDegree i)))
        (-(centeredShiftedLegendreReal
          (fourCellOddFiniteRetainedDegree j))) =
      if i = j then
        2 / (2 * (fourCellOddFiniteRetainedDegree j : ℝ) + 1)
      else 0 := by
  rw [centeredPolynomialPair_negLegendre]
  by_cases hij : i = j
  · simp [hij]
  · have hdeg : fourCellOddFiniteRetainedDegree i ≠
        fourCellOddFiniteRetainedDegree j := by
      intro h
      exact hij (fourCellOddFiniteRetainedDegree_injective N h)
    simp [hij, hdeg]

/-- Exact positive-half diagonal mass of every finite retained odd family. -/
theorem integral_zero_one_fourCellOddFiniteRetainedProfile_sq
    (N : ℕ) (a : Fin (N + 1) → ℝ) :
    (∫ x : ℝ in 0..1, fourCellOddFiniteRetainedProfile N a x ^ 2) =
      ∑ i, (a i) ^ 2 /
        (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1) := by
  let p := fourCellOddFiniteRetainedPolynomial N a
  have hinner (i : Fin (N + 1)) :
      (∑ j, a j *
        (if i = j then
          2 / (2 * (fourCellOddFiniteRetainedDegree j : ℝ) + 1)
        else 0)) =
        a i * (2 / (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1)) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _hj hji
      rw [if_neg (Ne.symm hji)]
      ring
    · simp
  have hpair : centeredPolynomialPair p p =
      ∑ i, a i *
        (a i * (2 /
          (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1))) := by
    dsimp only [p]
    unfold fourCellOddFiniteRetainedPolynomial
    rw [centeredPolynomialPair_sum_left_local]
    apply Finset.sum_congr rfl
    intro i hi
    rw [centeredPolynomialPair_smul_left_local,
      centeredPolynomialPair_sum_right_local]
    simp_rw [centeredPolynomialPair_smul_right_local,
      centeredPolynomialPair_finiteRetainedBasis]
    rw [hinner i]
  have hpair' : centeredPolynomialPair p p =
      2 * ∑ i, (a i) ^ 2 /
        (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1) := by
    calc
      centeredPolynomialPair p p =
          ∑ i, a i *
            (a i * (2 /
              (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1))) := hpair
      _ = 2 * ∑ i, (a i) ^ 2 /
          (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  unfold centeredPolynomialPair at hpair'
  rw [show (fun x : ℝ ↦ p.eval x * p.eval x) =
      fun x ↦ fourCellOddFiniteRetainedProfile N a x ^ 2 by
    funext x
    rw [show p.eval x = fourCellOddFiniteRetainedProfile N a x by
      dsimp only [p]
      exact fourCellOddFiniteRetainedPolynomial_eval N a x]
    ring] at hpair'
  have hfold := integral_sq_eq_two_mul_positiveHalf
    (fourCellOddFiniteRetainedProfile N a)
    (contDiff_fourCellOddFiniteRetainedProfile N a).continuous
    (Or.inr (odd_fourCellOddFiniteRetainedProfile N a))
  linarith

private theorem centeredP1_eq_neg_centeredLegendre_one :
    centeredP1 = fun x ↦ -(centeredShiftedLegendreReal 1).eval x := by
  funext x
  rw [ShiftedLegendreCenteredLowModes.eval_centeredShiftedLegendreReal_one]
  unfold centeredP1
  ring

private theorem centeredPolynomialPair_finiteRetained_P1_eq_zero
    (N : ℕ) (a : Fin (N + 1) → ℝ) :
    centeredPolynomialPair
      (fourCellOddFiniteRetainedPolynomial N a)
      (-(centeredShiftedLegendreReal 1)) = 0 := by
  unfold fourCellOddFiniteRetainedPolynomial
  rw [centeredPolynomialPair_sum_left_local]
  apply Finset.sum_eq_zero
  intro i hi
  rw [centeredPolynomialPair_smul_left_local,
    centeredPolynomialPair_negLegendre,
    if_neg]
  · ring
  · unfold fourCellOddFiniteRetainedDegree
    omega

/-- Every retained finite profile is exactly `P1`-orthogonal. -/
theorem centeredOddP1Coefficient_fourCellOddFiniteRetainedProfile_eq_zero
    (N : ℕ) (a : Fin (N + 1) → ℝ) :
    centeredOddP1Coefficient (fourCellOddFiniteRetainedProfile N a) = 0 := by
  let p := fourCellOddFiniteRetainedPolynomial N a
  have hpair : centeredPolynomialPair p
      (-(centeredShiftedLegendreReal 1)) = 0 := by
    dsimp only [p]
    exact centeredPolynomialPair_finiteRetained_P1_eq_zero N a
  unfold centeredPolynomialPair at hpair
  unfold centeredOddP1Coefficient
  rw [show (fun x : ℝ ↦
      fourCellOddFiniteRetainedProfile N a x * centeredP1 x) =
      fun x ↦ p.eval x * (-(centeredShiftedLegendreReal 1)).eval x by
    funext x
    rw [show p.eval x = fourCellOddFiniteRetainedProfile N a x by
      dsimp only [p]
      exact fourCellOddFiniteRetainedPolynomial_eval N a x,
      congrFun centeredP1_eq_neg_centeredLegendre_one x,
      Polynomial.eval_neg]]
  rw [hpair]
  ring

/-- Nonpositive exact retained mass forces every coordinate to vanish. -/
theorem fourCellOddFiniteRetainedProfile_coefficients_eq_zero_of_mass_nonpos
    (N : ℕ) (a : Fin (N + 1) → ℝ)
    (hmass : (∫ x : ℝ in 0..1,
      fourCellOddFiniteRetainedProfile N a x ^ 2) ≤ 0) :
    a = 0 := by
  rw [integral_zero_one_fourCellOddFiniteRetainedProfile_sq] at hmass
  funext i
  have hdenpos : 0 <
      2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1 := by positivity
  have hterm_nonneg (j : Fin (N + 1)) :
      0 ≤ (a j) ^ 2 /
        (2 * (fourCellOddFiniteRetainedDegree j : ℝ) + 1) := by
    positivity
  have hterm_le :
      (a i) ^ 2 /
          (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1) ≤
        ∑ j, (a j) ^ 2 /
          (2 * (fourCellOddFiniteRetainedDegree j : ℝ) + 1) :=
    Finset.single_le_sum (fun j _hj ↦ hterm_nonneg j) (Finset.mem_univ i)
  have hterm_zero :
      (a i) ^ 2 /
        (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1) = 0 :=
    le_antisymm (hterm_le.trans hmass) (hterm_nonneg i)
  have hsquare : (a i) ^ 2 = 0 :=
    (div_eq_zero_iff.mp hterm_zero).resolve_right (ne_of_gt hdenpos)
  simpa using (sq_eq_zero_iff.mp hsquare)

private theorem contDiff_centeredP1_local : ContDiff ℝ 1 centeredP1 := by
  unfold centeredP1
  fun_prop

private theorem odd_centeredP1_local : Function.Odd centeredP1 := by
  intro x
  unfold centeredP1
  ring

private theorem odd_const_mul
    {v : ℝ → ℝ} (hv : Function.Odd v) (c : ℝ) :
    Function.Odd (fun x ↦ c * v x) := by
  intro x
  change c * v (-x) = -(c * v x)
  rw [hv]
  ring

private theorem fourCellOddCoreLocalBilinear_add_right
    (u v w : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w)
    (huodd : Function.Odd u) (hvodd : Function.Odd v)
    (hwodd : Function.Odd w) :
    fourCellOddCoreLocalBilinear u (v + w) =
      fourCellOddCoreLocalBilinear u v +
        fourCellOddCoreLocalBilinear u w := by
  calc
    fourCellOddCoreLocalBilinear u (v + w) =
        fourCellOddCoreLocalBilinear (v + w) u :=
      fourCellOddCoreLocalBilinear_comm u (v + w)
        hu.continuous (hv.add hw).continuous
    _ = fourCellOddCoreLocalBilinear v u +
          fourCellOddCoreLocalBilinear w u :=
      fourCellOddCoreLocalBilinear_add_left
        v w u hv hw hu hvodd hwodd huodd
    _ = fourCellOddCoreLocalBilinear u v +
          fourCellOddCoreLocalBilinear u w := by
      rw [fourCellOddCoreLocalBilinear_comm v u
          hv.continuous hu.continuous,
        fourCellOddCoreLocalBilinear_comm w u
          hw.continuous hu.continuous]

private theorem fourCellOddCoreLocalBilinear_zero_right
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (huodd : Function.Odd u) :
    fourCellOddCoreLocalBilinear u 0 = 0 := by
  have h := fourCellOddCoreLocalBilinear_const_mul_right
    u u hu hu huodd huodd 0
  simpa using h

private theorem fourCellOddCoreLocalBilinear_partialProfile_right
    (N : ℕ) (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u)
    (huodd : Function.Odd u) (a : Fin (N + 1) → ℝ)
    (s : Finset (Fin (N + 1))) :
    fourCellOddCoreLocalBilinear u
        (s.sum fun i ↦
          fun x ↦ a i * fourCellOddFiniteRetainedBasis i x) =
      s.sum (fun i ↦ a i *
        fourCellOddCoreLocalBilinear u
          (fourCellOddFiniteRetainedBasis i)) := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact fourCellOddCoreLocalBilinear_zero_right u hu huodd
  | @insert i s hi ih =>
      have hvi : ContDiff ℝ 1
          (fun x ↦ a i * fourCellOddFiniteRetainedBasis i x) :=
        contDiff_const.mul (contDiff_fourCellOddFiniteRetainedBasis i)
      have hviodd : Function.Odd
          (fun x ↦ a i * fourCellOddFiniteRetainedBasis i x) :=
        odd_const_mul (odd_fourCellOddFiniteRetainedBasis i) (a i)
      have hvs := contDiff_fourCellOddFiniteRetainedPartialProfile a s
      have hvsodd := odd_fourCellOddFiniteRetainedPartialProfile a s
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        fourCellOddCoreLocalBilinear_add_right
          u (fun x ↦ a i * fourCellOddFiniteRetainedBasis i x)
          (s.sum fun j ↦ fun x ↦
            a j * fourCellOddFiniteRetainedBasis j x)
          hu hvi hvs huodd hviodd hvsodd,
        fourCellOddCoreLocalBilinear_const_mul_right
          u (fourCellOddFiniteRetainedBasis i)
          hu (contDiff_fourCellOddFiniteRetainedBasis i)
          huodd (odd_fourCellOddFiniteRetainedBasis i) (a i),
        ih]

/-- Linearity of the actual core pairing against an arbitrary retained
finite profile. -/
theorem fourCellOddCoreLocalBilinear_finiteRetainedProfile_right
    (N : ℕ) (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u)
    (huodd : Function.Odd u) (a : Fin (N + 1) → ℝ) :
    fourCellOddCoreLocalBilinear u
        (fourCellOddFiniteRetainedProfile N a) =
      ∑ i, a i * fourCellOddCoreLocalBilinear u
        (fourCellOddFiniteRetainedBasis i) :=
  fourCellOddCoreLocalBilinear_partialProfile_right
    N u hu huodd a Finset.univ

theorem fourCellOddCoreLocalBilinear_finiteRetainedProfile_left
    (N : ℕ) (a : Fin (N + 1) → ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) (hvodd : Function.Odd v) :
    fourCellOddCoreLocalBilinear
        (fourCellOddFiniteRetainedProfile N a) v =
      ∑ i, a i * fourCellOddCoreLocalBilinear
        (fourCellOddFiniteRetainedBasis i) v := by
  rw [fourCellOddCoreLocalBilinear_comm
      (fourCellOddFiniteRetainedProfile N a) v
      (contDiff_fourCellOddFiniteRetainedProfile N a).continuous
      hv.continuous,
    fourCellOddCoreLocalBilinear_finiteRetainedProfile_right
      N v hv hvodd a]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fourCellOddCoreLocalBilinear_comm v
    (fourCellOddFiniteRetainedBasis i) hv.continuous
    (contDiff_fourCellOddFiniteRetainedBasis i).continuous]

/-- Exact core Gram of `P3,P5,...,P(2N+3)`. -/
def fourCellOddFiniteRetainedGram (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j ↦ fourCellOddCoreLocalBilinear
    (fourCellOddFiniteRetainedBasis i)
    (fourCellOddFiniteRetainedBasis j)

/-- Exact `P1` mixed row in arbitrary retained coordinates. -/
def fourCellOddFiniteRetainedRhs (N : ℕ) : Fin (N + 1) → ℝ :=
  fun i ↦ fourCellOddCoreLocalBilinear
    (fourCellOddFiniteRetainedBasis i) centeredP1

private theorem fourCellOddFiniteRetainedGram_mulVec
    (N : ℕ) (a : Fin (N + 1) → ℝ) :
    fourCellOddFiniteRetainedGram N *ᵥ a =
      fun i ↦ fourCellOddCoreLocalBilinear
        (fourCellOddFiniteRetainedBasis i)
        (fourCellOddFiniteRetainedProfile N a) := by
  funext i
  rw [fourCellOddCoreLocalBilinear_finiteRetainedProfile_right
    N (fourCellOddFiniteRetainedBasis i)
    (contDiff_fourCellOddFiniteRetainedBasis i)
    (odd_fourCellOddFiniteRetainedBasis i) a]
  unfold fourCellOddFiniteRetainedGram Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Every finite retained Gram has trivial kernel by core coercivity and
the exact diagonal Legendre mass. -/
theorem fourCellOddFiniteRetainedGram_kernel
    (N : ℕ) (a : Fin (N + 1) → ℝ)
    (ha : fourCellOddFiniteRetainedGram N *ᵥ a = 0) :
    a = 0 := by
  have hrows := fourCellOddFiniteRetainedGram_mulVec N a
  rw [ha] at hrows
  have hrow (i : Fin (N + 1)) :
      fourCellOddCoreLocalBilinear
        (fourCellOddFiniteRetainedBasis i)
        (fourCellOddFiniteRetainedProfile N a) = 0 := by
    have hi := congrFun hrows i
    simpa using hi.symm
  have hself : fourCellOddCoreLocalBilinear
      (fourCellOddFiniteRetainedProfile N a)
      (fourCellOddFiniteRetainedProfile N a) = 0 := by
    rw [fourCellOddCoreLocalBilinear_finiteRetainedProfile_left
      N a (fourCellOddFiniteRetainedProfile N a)
      (contDiff_fourCellOddFiniteRetainedProfile N a)
      (odd_fourCellOddFiniteRetainedProfile N a)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hrow i]
    ring
  have hdiag := fourCellOddCoreLocalBilinear_self_eq_quadratic
    (fourCellOddFiniteRetainedProfile N a)
    (contDiff_fourCellOddFiniteRetainedProfile N a)
    (odd_fourCellOddFiniteRetainedProfile N a)
  have hqzero : fourCellOddCoreLocalQuadratic
      (fourCellOddFiniteRetainedProfile N a) = 0 := by
    linarith
  have hcoercive := fourCellOddCorePositiveHalfCoerciveAt_rationalFloor
    (fourCellOddFiniteRetainedProfile N a)
    (contDiff_fourCellOddFiniteRetainedProfile N a)
    (odd_fourCellOddFiniteRetainedProfile N a)
    (centeredOddP1Coefficient_fourCellOddFiniteRetainedProfile_eq_zero N a)
  rw [hqzero] at hcoercive
  have hmass : (∫ x : ℝ in 0..1,
      fourCellOddFiniteRetainedProfile N a x ^ 2) ≤ 0 := by
    nlinarith
  exact fourCellOddFiniteRetainedProfile_coefficients_eq_zero_of_mass_nonpos
    N a hmass

/-- The exact finite retained core Gram is nonsingular for every cutoff. -/
theorem fourCellOddFiniteRetainedGram_isUnit (N : ℕ) :
    IsUnit (fourCellOddFiniteRetainedGram N) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hsub : fourCellOddFiniteRetainedGram N *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp
    (fourCellOddFiniteRetainedGram_kernel N (x - y) hsub)

private theorem fourCellOddFiniteRetainedGram_det_isUnit (N : ℕ) :
    IsUnit (fourCellOddFiniteRetainedGram N).det :=
  (fourCellOddFiniteRetainedGram N).isUnit_iff_isUnit_det.mp
    (fourCellOddFiniteRetainedGram_isUnit N)

/-- Inverse-defined solution of all retained normal equations. -/
def fourCellOddFiniteRetainedSolution (N : ℕ) : Fin (N + 1) → ℝ :=
  (fourCellOddFiniteRetainedGram N)⁻¹ *ᵥ fourCellOddFiniteRetainedRhs N

theorem fourCellOddFiniteRetainedSolution_normalEquation (N : ℕ) :
    fourCellOddFiniteRetainedGram N *ᵥ
        fourCellOddFiniteRetainedSolution N =
      fourCellOddFiniteRetainedRhs N := by
  unfold fourCellOddFiniteRetainedSolution
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv (fourCellOddFiniteRetainedGram N)
      (fourCellOddFiniteRetainedGram_det_isUnit N),
    Matrix.one_mulVec]

/-- The inverse-defined vector is the unique solution of the retained
normal equations. -/
theorem fourCellOddFiniteRetainedSolution_unique
    (N : ℕ) (a : Fin (N + 1) → ℝ)
    (ha : fourCellOddFiniteRetainedGram N *ᵥ a =
      fourCellOddFiniteRetainedRhs N) :
    a = fourCellOddFiniteRetainedSolution N := by
  have hsub : fourCellOddFiniteRetainedGram N *ᵥ
      (a - fourCellOddFiniteRetainedSolution N) = 0 := by
    rw [Matrix.mulVec_sub, ha,
      fourCellOddFiniteRetainedSolution_normalEquation, sub_self]
  exact sub_eq_zero.mp
    (fourCellOddFiniteRetainedGram_kernel N
      (a - fourCellOddFiniteRetainedSolution N) hsub)

/-- The inverse normal equations hold against every retained vector. -/
theorem fourCellOddFiniteRetainedSolution_normal
    (N : ℕ) (a : Fin (N + 1) → ℝ) :
    fourCellOddCoreLocalBilinear
        (fourCellOddFiniteRetainedProfile N
          (fourCellOddFiniteRetainedSolution N))
        (fourCellOddFiniteRetainedProfile N a) =
      fourCellOddCoreLocalBilinear centeredP1
        (fourCellOddFiniteRetainedProfile N a) := by
  let proj := fourCellOddFiniteRetainedProfile N
    (fourCellOddFiniteRetainedSolution N)
  have hproj : ContDiff ℝ 1 proj :=
    contDiff_fourCellOddFiniteRetainedProfile N _
  have hprojodd : Function.Odd proj :=
    odd_fourCellOddFiniteRetainedProfile N _
  have hrows : (fun i ↦ fourCellOddCoreLocalBilinear
      (fourCellOddFiniteRetainedBasis i) proj) =
      fourCellOddFiniteRetainedRhs N :=
    (fourCellOddFiniteRetainedGram_mulVec N
      (fourCellOddFiniteRetainedSolution N)).symm.trans
      (fourCellOddFiniteRetainedSolution_normalEquation N)
  have hrow (i : Fin (N + 1)) :
      fourCellOddCoreLocalBilinear proj
          (fourCellOddFiniteRetainedBasis i) =
        fourCellOddCoreLocalBilinear centeredP1
          (fourCellOddFiniteRetainedBasis i) := by
    have hi := congrFun hrows i
    change fourCellOddCoreLocalBilinear
        (fourCellOddFiniteRetainedBasis i) proj =
      fourCellOddCoreLocalBilinear
        (fourCellOddFiniteRetainedBasis i) centeredP1 at hi
    rw [fourCellOddCoreLocalBilinear_comm proj
        (fourCellOddFiniteRetainedBasis i)
        hproj.continuous
        (contDiff_fourCellOddFiniteRetainedBasis i).continuous,
      fourCellOddCoreLocalBilinear_comm centeredP1
        (fourCellOddFiniteRetainedBasis i)
        contDiff_centeredP1_local.continuous
        (contDiff_fourCellOddFiniteRetainedBasis i).continuous]
    exact hi
  change fourCellOddCoreLocalBilinear proj
      (fourCellOddFiniteRetainedProfile N a) = _
  rw [fourCellOddCoreLocalBilinear_finiteRetainedProfile_right
      N proj hproj hprojodd a,
    fourCellOddCoreLocalBilinear_finiteRetainedProfile_right
      N centeredP1 contDiff_centeredP1_local odd_centeredP1_local a]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hrow i]

/-- The `P1` residual after projection to a finite retained family. -/
def fourCellOddFiniteGalerkinResidualProfile
    (N : ℕ) (a : Fin (N + 1) → ℝ) : ℝ → ℝ := fun x ↦
  centeredP1 x - fourCellOddFiniteRetainedProfile N a x

theorem contDiff_fourCellOddFiniteGalerkinResidualProfile
    (N : ℕ) (a : Fin (N + 1) → ℝ) :
    ContDiff ℝ 1 (fourCellOddFiniteGalerkinResidualProfile N a) :=
  contDiff_centeredP1_local.sub
    (contDiff_fourCellOddFiniteRetainedProfile N a)

theorem odd_fourCellOddFiniteGalerkinResidualProfile
    (N : ℕ) (a : Fin (N + 1) → ℝ) :
    Function.Odd (fourCellOddFiniteGalerkinResidualProfile N a) := by
  intro x
  unfold fourCellOddFiniteGalerkinResidualProfile
  rw [odd_centeredP1_local,
    odd_fourCellOddFiniteRetainedProfile N a]
  ring

/-- Exact finite orthogonality of a residual to the retained family. -/
def FourCellOddFiniteGalerkinOrthogonal
    (N : ℕ) (a : Fin (N + 1) → ℝ) : Prop :=
  ∀ b : Fin (N + 1) → ℝ,
    fourCellOddCoreLocalBilinear
      (fourCellOddFiniteGalerkinResidualProfile N a)
      (fourCellOddFiniteRetainedProfile N b) = 0

theorem fourCellOddFiniteRetainedSolution_orthogonal (N : ℕ) :
    FourCellOddFiniteGalerkinOrthogonal N
      (fourCellOddFiniteRetainedSolution N) := by
  intro b
  let proj := fourCellOddFiniteRetainedProfile N
    (fourCellOddFiniteRetainedSolution N)
  let p := fourCellOddFiniteRetainedProfile N b
  have hproj : ContDiff ℝ 1 proj :=
    contDiff_fourCellOddFiniteRetainedProfile N _
  have hprojodd : Function.Odd proj :=
    odd_fourCellOddFiniteRetainedProfile N _
  have hp : ContDiff ℝ 1 p :=
    contDiff_fourCellOddFiniteRetainedProfile N _
  have hpodd : Function.Odd p :=
    odd_fourCellOddFiniteRetainedProfile N _
  have hnormal := fourCellOddFiniteRetainedSolution_normal N b
  have hresidual :
      fourCellOddFiniteGalerkinResidualProfile N
          (fourCellOddFiniteRetainedSolution N) =
        centeredP1 + fun x ↦ (-1 : ℝ) * proj x := by
    funext x
    dsimp only [proj]
    unfold fourCellOddFiniteGalerkinResidualProfile
    simp only [Pi.add_apply]
    ring
  change fourCellOddCoreLocalBilinear
    (fourCellOddFiniteGalerkinResidualProfile N
      (fourCellOddFiniteRetainedSolution N)) p = 0
  rw [hresidual,
    fourCellOddCoreLocalBilinear_add_left centeredP1
      (fun x ↦ (-1 : ℝ) * proj x) p
      contDiff_centeredP1_local (contDiff_const.mul hproj) hp
      odd_centeredP1_local (odd_const_mul hprojodd (-1)) hpodd,
    fourCellOddCoreLocalBilinear_const_mul_left proj p
      hproj hp hprojodd hpodd (-1)]
  change fourCellOddCoreLocalBilinear proj p =
    fourCellOddCoreLocalBilinear centeredP1 p at hnormal
  rw [hnormal]
  ring

/-! ## Direct `P51` instantiation -/

abbrev FourCellOddP51RetainedIndex := Fin 25

theorem fourCellOddP51_last_retained_degree :
    fourCellOddFiniteRetainedDegree (Fin.last 24) = 51 := by
  norm_num [fourCellOddFiniteRetainedDegree]

def fourCellOddP51RetainedGram :
    Matrix FourCellOddP51RetainedIndex FourCellOddP51RetainedIndex ℝ :=
  fourCellOddFiniteRetainedGram 24

def fourCellOddP51RetainedRhs : FourCellOddP51RetainedIndex → ℝ :=
  fourCellOddFiniteRetainedRhs 24

def fourCellOddP51RetainedSolution : FourCellOddP51RetainedIndex → ℝ :=
  fourCellOddFiniteRetainedSolution 24

def fourCellOddP51RetainedProfile
    (a : FourCellOddP51RetainedIndex → ℝ) : ℝ → ℝ :=
  fourCellOddFiniteRetainedProfile 24 a

def fourCellOddP51GalerkinResidualProfile : ℝ → ℝ :=
  fourCellOddFiniteGalerkinResidualProfile 24
    fourCellOddP51RetainedSolution

theorem fourCellOddP51RetainedGram_isUnit :
    IsUnit fourCellOddP51RetainedGram := by
  simpa [fourCellOddP51RetainedGram] using
    fourCellOddFiniteRetainedGram_isUnit 24

theorem fourCellOddP51RetainedSolution_normalEquation :
    fourCellOddP51RetainedGram *ᵥ fourCellOddP51RetainedSolution =
      fourCellOddP51RetainedRhs := by
  simpa [fourCellOddP51RetainedGram, fourCellOddP51RetainedSolution,
    fourCellOddP51RetainedRhs] using
    fourCellOddFiniteRetainedSolution_normalEquation 24

theorem fourCellOddP51RetainedSolution_unique
    (a : FourCellOddP51RetainedIndex → ℝ)
    (ha : fourCellOddP51RetainedGram *ᵥ a =
      fourCellOddP51RetainedRhs) :
    a = fourCellOddP51RetainedSolution := by
  apply fourCellOddFiniteRetainedSolution_unique 24
  simpa [fourCellOddP51RetainedGram,
    fourCellOddP51RetainedRhs] using ha

theorem fourCellOddP51RetainedSolution_orthogonal :
    FourCellOddFiniteGalerkinOrthogonal 24
      fourCellOddP51RetainedSolution := by
  simpa [fourCellOddP51RetainedSolution] using
    fourCellOddFiniteRetainedSolution_orthogonal 24

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddFiniteLegendreSolveStructural
