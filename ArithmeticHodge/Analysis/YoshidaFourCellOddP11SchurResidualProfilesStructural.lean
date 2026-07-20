import ArithmeticHodge.Analysis.YoshidaFourCellOddP11DirectCorrectedCauchyStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11SchurResidualProfilesStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddFiveModeStrictCoercivityStructural
open YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
open YoshidaFourCellOddP11DirectCorrectedCauchyStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Schur residual profiles for the direct odd `P₁₁+` frontier

The corrected tail reserve and corrected finite--tail cross are ordinary
core-form quantities after applying the same inverse-free `P₁` Schur
residualization already used on the finite side.  This identifies the direct
corrected Cauchy frontier with Cauchy--Schwarz on two explicit profiles in the
core-orthogonal complement of `P₁`.
-/

/-- The inverse-free `P₁` Schur residual of a genuine odd tail profile. -/
def fourCellOddP11TailSchurResidualProfile (r : ℝ → ℝ) : ℝ → ℝ := fun x ↦
  fourCellOddCoreLocalQuadratic centeredP1 * r x -
    fourCellOddCoreLocalBilinear centeredP1 r * centeredP1 x

private theorem contDiff_centeredP1 : ContDiff ℝ 1 centeredP1 := by
  unfold centeredP1
  fun_prop

private theorem odd_centeredP1 : Function.Odd centeredP1 := by
  intro x
  unfold centeredP1
  ring

theorem contDiff_fourCellOddP11TailSchurResidualProfile
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) :
    ContDiff ℝ 1 (fourCellOddP11TailSchurResidualProfile r) := by
  unfold fourCellOddP11TailSchurResidualProfile
  exact (contDiff_const.mul hr).sub (contDiff_const.mul contDiff_centeredP1)

theorem odd_fourCellOddP11TailSchurResidualProfile
    (r : ℝ → ℝ) (hodd : Function.Odd r) :
    Function.Odd (fourCellOddP11TailSchurResidualProfile r) := by
  intro x
  change
    fourCellOddCoreLocalQuadratic centeredP1 * r (-x) -
        fourCellOddCoreLocalBilinear centeredP1 r * centeredP1 (-x) =
      -(fourCellOddCoreLocalQuadratic centeredP1 * r x -
        fourCellOddCoreLocalBilinear centeredP1 r * centeredP1 x)
  rw [hodd, odd_centeredP1]
  ring

/-- The tail Schur residual is exactly core-orthogonal to `P₁`. -/
theorem fourCellOddCoreLocalBilinear_centeredP1_tailSchurResidualProfile_eq_zero
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r) :
    fourCellOddCoreLocalBilinear centeredP1
      (fourCellOddP11TailSchurResidualProfile r) = 0 := by
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let b := fourCellOddCoreLocalBilinear centeredP1 r
  let u : ℝ → ℝ := fun x ↦ A * r x
  let v : ℝ → ℝ := fun x ↦ (-b) * centeredP1 x
  have hu : ContDiff ℝ 1 u := by
    dsimp only [u]
    exact contDiff_const.mul hr
  have hv : ContDiff ℝ 1 v := by
    dsimp only [v]
    exact contDiff_const.mul contDiff_centeredP1
  have huodd : Function.Odd u := by
    intro x
    dsimp only [u]
    rw [hodd]
    ring
  have hvodd : Function.Odd v := by
    intro x
    dsimp only [v]
    rw [odd_centeredP1]
    ring
  have hprofile : fourCellOddP11TailSchurResidualProfile r = u + v := by
    funext x
    unfold fourCellOddP11TailSchurResidualProfile
    dsimp only [A, b, u, v]
    simp only [Pi.add_apply]
    ring
  calc
    fourCellOddCoreLocalBilinear centeredP1
        (fourCellOddP11TailSchurResidualProfile r) =
        fourCellOddCoreLocalBilinear
          (fourCellOddP11TailSchurResidualProfile r) centeredP1 :=
      fourCellOddCoreLocalBilinear_comm _ _
        contDiff_centeredP1.continuous
        (contDiff_fourCellOddP11TailSchurResidualProfile r hr).continuous
    _ = fourCellOddCoreLocalBilinear (u + v) centeredP1 := by rw [hprofile]
    _ = fourCellOddCoreLocalBilinear u centeredP1 +
          fourCellOddCoreLocalBilinear v centeredP1 :=
      fourCellOddCoreLocalBilinear_add_left
        u v centeredP1 hu hv contDiff_centeredP1 huodd hvodd odd_centeredP1
    _ = A * fourCellOddCoreLocalBilinear r centeredP1 +
          (-b) * fourCellOddCoreLocalBilinear centeredP1 centeredP1 := by
      rw [show u = (fun x ↦ A * r x) by rfl,
        show v = (fun x ↦ (-b) * centeredP1 x) by rfl,
        fourCellOddCoreLocalBilinear_const_mul_left
          r centeredP1 hr contDiff_centeredP1 hodd odd_centeredP1 A,
        fourCellOddCoreLocalBilinear_const_mul_left
          centeredP1 centeredP1 contDiff_centeredP1 contDiff_centeredP1
          odd_centeredP1 odd_centeredP1 (-b)]
    _ = A * b + (-b) * A := by
      rw [fourCellOddCoreLocalBilinear_comm r centeredP1
          hr.continuous contDiff_centeredP1.continuous,
        fourCellOddCoreLocalBilinear_self_eq_quadratic
          centeredP1 contDiff_centeredP1 odd_centeredP1]
    _ = 0 := by ring

/-- Exact norm of the tail Schur residual. -/
theorem fourCellOddCoreLocalQuadratic_tailSchurResidualProfile
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r) :
    fourCellOddCoreLocalQuadratic
        (fourCellOddP11TailSchurResidualProfile r) =
      fourCellOddCoreLocalQuadratic centeredP1 *
        fourCellOddP11TailCorrectedReserve r := by
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let b := fourCellOddCoreLocalBilinear centeredP1 r
  let u : ℝ → ℝ := fun x ↦ A * r x
  let v : ℝ → ℝ := fun x ↦ (-b) * centeredP1 x
  have hu : ContDiff ℝ 1 u := by
    dsimp only [u]
    exact contDiff_const.mul hr
  have hv : ContDiff ℝ 1 v := by
    dsimp only [v]
    exact contDiff_const.mul contDiff_centeredP1
  have huodd : Function.Odd u := by
    intro x
    dsimp only [u]
    rw [hodd]
    ring
  have hvodd : Function.Odd v := by
    intro x
    dsimp only [v]
    rw [odd_centeredP1]
    ring
  have hprofile : fourCellOddP11TailSchurResidualProfile r = u + v := by
    funext x
    unfold fourCellOddP11TailSchurResidualProfile
    dsimp only [A, b, u, v]
    simp only [Pi.add_apply]
    ring
  have hqu : fourCellOddCoreLocalQuadratic u =
      A ^ 2 * fourCellOddCoreLocalQuadratic r := by
    dsimp only [u]
    exact fourCellOddCoreLocalQuadratic_const_mul r hr hodd A
  have hqv : fourCellOddCoreLocalQuadratic v =
      (-b) ^ 2 * fourCellOddCoreLocalQuadratic centeredP1 := by
    dsimp only [v]
    exact fourCellOddCoreLocalQuadratic_const_mul
      centeredP1 contDiff_centeredP1 odd_centeredP1 (-b)
  have huv : fourCellOddCoreLocalBilinear u v = -A * b ^ 2 := by
    rw [show u = (fun x ↦ A * r x) by rfl,
      show v = (fun x ↦ (-b) * centeredP1 x) by rfl,
      fourCellOddCoreLocalBilinear_const_mul_right
        (fun x ↦ A * r x) centeredP1 hu contDiff_centeredP1
        huodd odd_centeredP1 (-b),
      fourCellOddCoreLocalBilinear_const_mul_left
        r centeredP1 hr contDiff_centeredP1 hodd odd_centeredP1 A,
      fourCellOddCoreLocalBilinear_comm r centeredP1
        hr.continuous contDiff_centeredP1.continuous]
    dsimp only [b]
    ring
  rw [hprofile,
    fourCellOddCoreLocalQuadratic_add u v hu.continuous hv.continuous,
    hqu, huv, hqv]
  unfold fourCellOddP11TailCorrectedReserve
  dsimp only [A, b]
  ring

/-- The mixed pairing of the two residual profiles is exactly the corrected
finite--tail cross, multiplied by the positive `P₁` pivot. -/
theorem fourCellOddCoreLocalBilinear_finite_tailSchurResidualProfiles
    (d e f g : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP11FiniteSchurResidualProfile d e f g)
        (fourCellOddP11TailSchurResidualProfile r) =
      fourCellOddCoreLocalQuadratic centeredP1 *
        fourCellOddP11FiniteTailCorrectedCross d e f g r := by
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let b := fourCellOddCoreLocalBilinear centeredP1 r
  let h := fourCellOddP11FiniteSchurResidualProfile d e f g
  let u : ℝ → ℝ := fun x ↦ A * r x
  let v : ℝ → ℝ := fun x ↦ (-b) * centeredP1 x
  have hh : ContDiff ℝ 1 h := by
    dsimp only [h]
    exact contDiff_fourCellOddP11FiniteSchurResidualProfile d e f g
  have hhodd : Function.Odd h := by
    dsimp only [h]
    exact odd_fourCellOddP11FiniteSchurResidualProfile d e f g
  have hu : ContDiff ℝ 1 u := by
    dsimp only [u]
    exact contDiff_const.mul hr
  have hv : ContDiff ℝ 1 v := by
    dsimp only [v]
    exact contDiff_const.mul contDiff_centeredP1
  have huodd : Function.Odd u := by
    intro x
    dsimp only [u]
    rw [hodd]
    ring
  have hvodd : Function.Odd v := by
    intro x
    dsimp only [v]
    rw [odd_centeredP1]
    ring
  have hprofile : fourCellOddP11TailSchurResidualProfile r = u + v := by
    funext x
    unfold fourCellOddP11TailSchurResidualProfile
    dsimp only [A, b, u, v]
    simp only [Pi.add_apply]
    ring
  calc
    fourCellOddCoreLocalBilinear h
        (fourCellOddP11TailSchurResidualProfile r) =
        fourCellOddCoreLocalBilinear
          (fourCellOddP11TailSchurResidualProfile r) h :=
      fourCellOddCoreLocalBilinear_comm _ _ hh.continuous
        (contDiff_fourCellOddP11TailSchurResidualProfile r hr).continuous
    _ = fourCellOddCoreLocalBilinear (u + v) h := by rw [hprofile]
    _ = fourCellOddCoreLocalBilinear u h +
          fourCellOddCoreLocalBilinear v h :=
      fourCellOddCoreLocalBilinear_add_left
        u v h hu hv hh huodd hvodd hhodd
    _ = A * fourCellOddCoreLocalBilinear r h +
          (-b) * fourCellOddCoreLocalBilinear centeredP1 h := by
      rw [show u = (fun x ↦ A * r x) by rfl,
        show v = (fun x ↦ (-b) * centeredP1 x) by rfl,
        fourCellOddCoreLocalBilinear_const_mul_left
          r h hr hh hodd hhodd A,
        fourCellOddCoreLocalBilinear_const_mul_left
          centeredP1 h contDiff_centeredP1 hh odd_centeredP1 hhodd (-b)]
    _ = A * fourCellOddCoreLocalBilinear h r + (-b) * 0 := by
      rw [fourCellOddCoreLocalBilinear_comm r h hr.continuous hh.continuous]
      dsimp only [h]
      rw [fourCellOddCoreLocalBilinear_centeredP1_finiteSchurResidualProfile_eq_zero]
    _ = A * fourCellOddP11FiniteTailCorrectedCross d e f g r := by
      dsimp only [h]
      rw [fourCellOddCoreLocalBilinear_finiteSchurResidualProfile
        d e f g r hr hodd]
      ring
    _ = fourCellOddCoreLocalQuadratic centeredP1 *
        fourCellOddP11FiniteTailCorrectedCross d e f g r := by rfl

/-- Ordinary core Cauchy--Schwarz and diagonality for the explicit finite and
tail `P₁` Schur residuals. -/
def FourCellOddP11SchurResidualCoreCauchy : Prop :=
  ∀ (d e f g : ℝ) (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    0 ≤ fourCellOddCoreLocalQuadratic
        (fourCellOddP11TailSchurResidualProfile r) ∧
      fourCellOddCoreLocalBilinear
          (fourCellOddP11FiniteSchurResidualProfile d e f g)
          (fourCellOddP11TailSchurResidualProfile r) ^ 2 ≤
        fourCellOddCoreLocalQuadratic
            (fourCellOddP11FiniteSchurResidualProfile d e f g) *
          fourCellOddCoreLocalQuadratic
            (fourCellOddP11TailSchurResidualProfile r)

/-- The corrected odd frontier is exactly ordinary core Cauchy--Schwarz on
the two explicit `P₁` Schur residual profiles. -/
theorem fourCellOddP11DirectCorrectedCauchy_iff_schurResidualCoreCauchy :
    FourCellOddP11DirectCorrectedCauchy ↔
      FourCellOddP11SchurResidualCoreCauchy := by
  let A := fourCellOddCoreLocalQuadratic centeredP1
  have hA : 0 < A := by
    dsimp only [A]
    exact fourCellOddCoreLocalQuadratic_centeredP1_pos
  constructor
  · intro hcauchy d e f g r hr hodd hone hthree hfive hseven hnine
    rcases hcauchy d e f g r hr hodd hone hthree hfive hseven hnine with
      ⟨htail, hcross⟩
    constructor
    · rw [fourCellOddCoreLocalQuadratic_tailSchurResidualProfile r hr hodd]
      exact mul_nonneg hA.le htail
    · rw [fourCellOddCoreLocalBilinear_finite_tailSchurResidualProfiles
          d e f g r hr hodd,
        fourCellOddCoreLocalQuadratic_finiteSchurResidualProfile,
        fourCellOddCoreLocalQuadratic_tailSchurResidualProfile r hr hodd]
      have hscaled := mul_le_mul_of_nonneg_left hcross (sq_nonneg A)
      dsimp only [A] at hscaled ⊢
      nlinarith
  · intro hresidual d e f g r hr hodd hone hthree hfive hseven hnine
    rcases hresidual d e f g r hr hodd hone hthree hfive hseven hnine with
      ⟨htail, hcross⟩
    rw [fourCellOddCoreLocalQuadratic_tailSchurResidualProfile r hr hodd] at htail
    rw [fourCellOddCoreLocalBilinear_finite_tailSchurResidualProfiles
          d e f g r hr hodd,
      fourCellOddCoreLocalQuadratic_finiteSchurResidualProfile,
      fourCellOddCoreLocalQuadratic_tailSchurResidualProfile r hr hodd] at hcross
    constructor
    · dsimp only [A] at hA
      nlinarith
    · have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
      dsimp only [A] at hA2 hcross ⊢
      nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11SchurResidualProfilesStructural
