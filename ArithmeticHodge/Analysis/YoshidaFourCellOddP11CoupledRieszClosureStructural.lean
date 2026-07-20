import ArithmeticHodge.Analysis.YoshidaFourCellOddP1OrthogonalCoupledClosureStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoupledRieszClosureStructural

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
open YoshidaFourCellOddP11EndpointFormDualClosureStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# The corrected `P₁`/`P₁₁+` Riesz determinant

After the exact five-mode projection, separate Cauchy estimates for the
finite row, tail row, and finite--tail cross do not compose.  The invariant
that does compose is the corrected determinant below; it retains the sign
and correlation of the mixed row.
-/

/-- Corrected determinant of a finite row `(A,b,C)`, a tail row `(A,x,z)`,
and their coupled cross `y`. -/
def coupledP1TailSchurDefect
    (A b C x y z : ℝ) : ℝ :=
  (A * C - b ^ 2) +
    2 * (A * y - b * x) +
    (A * z - x ^ 2)

/-- Exact determinant identity.  In particular, the mixed correlation
cannot be replaced by its absolute value without spending finite reserve. -/
theorem coupledP1TailSchurDefect_eq
    (A b C x y z : ℝ) :
    coupledP1TailSchurDefect A b C x y z =
      A * (C + 2 * y + z) - (b + x) ^ 2 := by
  unfold coupledP1TailSchurDefect
  ring

theorem add_row_sq_le_of_coupledP1TailSchurDefect_nonneg
    {A b C x y z : ℝ}
    (hdefect : 0 ≤ coupledP1TailSchurDefect A b C x y z) :
    (b + x) ^ 2 ≤ A * (C + 2 * y + z) := by
  rw [coupledP1TailSchurDefect_eq] at hdefect
  linarith

/-- Sharp structural obstruction to a rowwise allocation: even saturated
finite Schur, tail Schur, and finite--tail Cauchy inequalities do not imply
the coupled conclusion.  The missing datum is the sign of `A*y - b*x`. -/
theorem rowwise_schur_bounds_do_not_imply_coupled :
    ¬ (∀ A b C x y z : ℝ,
      0 ≤ A → 0 ≤ C → 0 ≤ z →
      b ^ 2 ≤ A * C → x ^ 2 ≤ A * z → y ^ 2 ≤ C * z →
      (b + x) ^ 2 ≤ A * (C + 2 * y + z)) := by
  intro h
  have hbad := h 1 1 1 1 (-1) 1
  norm_num at hbad

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

private theorem intervalIntegrable_P1_regularRepresenter_mul
    (u : ℝ → ℝ) (hu : Continuous u) :
    IntervalIntegrable
      (fun x : ℝ ↦
        u x * fourCellOddFiveModeRegularRepresenter 1 0 0 0 0 x)
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

/-- Additivity of the exact affine `P₁` representer on its natural
`P₁`-orthogonal domain. -/
theorem fourCellOddCoreLocalBilinear_P1_add_of_P1Orthogonal
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v)
    (hu1 : centeredOddP1Coefficient u = 0)
    (hv1 : centeredOddP1Coefficient v = 0) :
    fourCellOddCoreLocalBilinear centeredP1 (u + v) =
      fourCellOddCoreLocalBilinear centeredP1 u +
        fourCellOddCoreLocalBilinear centeredP1 v := by
  have huv1 : centeredOddP1Coefficient (u + v) = 0 := by
    unfold centeredOddP1Coefficient at hu1 hv1 ⊢
    have huI : IntervalIntegrable
        (fun x : ℝ ↦ u x * centeredP1 x) volume (-1) 1 :=
      (hu.continuous.mul (by unfold centeredP1; fun_prop))
        |>.intervalIntegrable _ _
    have hvI : IntervalIntegrable
        (fun x : ℝ ↦ v x * centeredP1 x) volume (-1) 1 :=
      (hv.continuous.mul (by unfold centeredP1; fun_prop))
        |>.intervalIntegrable _ _
    rw [show (fun x : ℝ ↦ (u + v) x * centeredP1 x) =
        fun x ↦ u x * centeredP1 x + v x * centeredP1 x by
      funext x
      simp only [Pi.add_apply]
      ring,
      intervalIntegral.integral_add huI hvI]
    nlinarith
  rw [fourCellOddCoreLocalBilinear_P1_P1Orthogonal_eq_affineEndpointRepresenter
      (u + v) (hu.add hv) (huodd.add hvodd) huv1,
    fourCellOddCoreLocalBilinear_P1_P1Orthogonal_eq_affineEndpointRepresenter
      u hu huodd hu1,
    fourCellOddCoreLocalBilinear_P1_P1Orthogonal_eq_affineEndpointRepresenter
      v hv hvodd hv1]
  have huUpper : IntervalIntegrable
      (fun x : ℝ ↦ (8 / 5 - x) * u x) volume (3 / 5) 1 :=
    ((continuous_const.sub continuous_id).mul hu.continuous)
      |>.intervalIntegrable _ _
  have hvUpper : IntervalIntegrable
      (fun x : ℝ ↦ (8 / 5 - x) * v x) volume (3 / 5) 1 :=
    ((continuous_const.sub continuous_id).mul hv.continuous)
      |>.intervalIntegrable _ _
  have huPotential :=
    intervalIntegrable_zero_one_endpointPotential_mul_x_mul u hu.continuous
  have hvPotential :=
    intervalIntegrable_zero_one_endpointPotential_mul_x_mul v hv.continuous
  have huRegular :=
    intervalIntegrable_P1_regularRepresenter_mul u hu.continuous
  have hvRegular :=
    intervalIntegrable_P1_regularRepresenter_mul v hv.continuous
  simp only [Pi.add_apply]
  rw [show (fun x : ℝ ↦ (8 / 5 - x) * (u x + v x)) =
      fun x ↦ (8 / 5 - x) * u x + (8 / 5 - x) * v x by
    funext x
    ring,
    intervalIntegral.integral_add huUpper hvUpper,
    show (fun x : ℝ ↦ yoshidaEndpointPotential x * x * (u x + v x)) =
      fun x ↦ yoshidaEndpointPotential x * x * u x +
        yoshidaEndpointPotential x * x * v x by
      funext x
      ring,
    intervalIntegral.integral_add huPotential hvPotential,
    show (fun x : ℝ ↦ (u x + v x) *
        fourCellOddFiveModeRegularRepresenter 1 0 0 0 0 x) =
      fun x ↦
        u x * fourCellOddFiveModeRegularRepresenter 1 0 0 0 0 x +
          v x * fourCellOddFiveModeRegularRepresenter 1 0 0 0 0 x by
      funext x
      ring,
    intervalIntegral.integral_add huRegular hvRegular]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoupledRieszClosureStructural
