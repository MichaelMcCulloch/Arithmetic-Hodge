import ArithmeticHodge.Analysis.YoshidaFourCellOddP51GalerkinRieszStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailGalerkinRieszStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoEndpointBilinear
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddP11CorrectedDeterminantAuditStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# High-tail Galerkin--Riesz assembly at `P51`

The global positive-half coercivity constant is unnecessarily flattened for
the exact `P51` solve.  The Galerkin algebra only needs coercivity of the
middle block after an arbitrary retained vector is combined with a genuine
Legendre tail.  This file isolates that weaker interface and reruns the
cutoff-independent assembly with its own high-tail constant.

No analytic estimate for that constant is asserted here.
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

/-! ## Abstract finite-cutoff middle coercivity -/

/-- The exact coercivity input used by the finite Galerkin--Riesz assembly.
It reserves only the scaled mass of the genuine tail, uniformly over every
vector in the retained block. -/
def FourCellOddFiniteLegendreTailMiddleCoerciveAt
    (N : ℕ) (kappaTail : ℝ) : Prop :=
  ∀ (a : Fin (N + 1) → ℝ) (t : ℝ) (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    FourCellOddFiniteLegendreTailMoments N r →
      t ^ 2 * (kappaTail * (∫ x : ℝ in 0..1, r x ^ 2)) ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddFiniteRetainedProfile N a + fun x ↦ t * r x)

/-- A nonnegative finite pivot, its residual dual, and tail-specific middle
coercivity imply the full `P1`-orthogonal form-dual inequality. -/
theorem fourCellOddP1OrthogonalFormDualBound_of_finiteSolvedHighTailGalerkinRiesz
    (N : ℕ) (kappaTail : ℝ) (hkappaTail : 0 ≤ kappaTail)
    (hmiddle : FourCellOddFiniteLegendreTailMiddleCoerciveAt N kappaTail)
    (hpivot : 0 ≤ fourCellOddFiniteSolvedGalerkinPivot N)
    (hdual : FourCellOddFiniteSolvedGalerkinResidualL2Dual N kappaTail) :
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
  have hmass0 : 0 ≤ kappaTail * (∫ x : ℝ in 0..1, r x ^ 2) :=
    mul_nonneg hkappaTail
      (intervalIntegral.integral_nonneg (by norm_num)
        (fun x _hx ↦ sq_nonneg (r x)))
  have hresidualDual := hdual r hr hrodd htail
  have hpencil : ∀ s t : ℝ,
      0 ≤ fourCellOddCoreLocalQuadratic
        (fun x ↦ s * centeredP1 x + t * v x) := by
    intro s t
    let u := fourCellOddFiniteRetainedProfile N
      (fun i ↦ s * fourCellOddFiniteRetainedSolution N i + t * b i)
    have hmiddle' := hmiddle
      (fun i ↦ s * fourCellOddFiniteRetainedSolution N i + t * b i)
      t r hr hrodd htail
    have hbinary :=
      (real_quadratic_pencil_nonneg_iff
        (fourCellOddFiniteSolvedGalerkinPivot N)
        (kappaTail * (∫ x : ℝ in 0..1, r x ^ 2))
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
    dsimp only [q, u] at hsplit hmiddle' hbinary ⊢
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

/-! ## Exact `P51` / `P53+` specialization -/

/-- Tail-specific Schur coercivity at the exact `P51` cutoff.  This is the
remaining analytic interface: the retained vector and scale are arbitrary,
while `r` is a genuine smooth odd `P53+` tail. -/
def FourCellOddP51P53PlusMiddleCoerciveAt (kappaTail : ℝ) : Prop :=
  ∀ (a : FourCellOddP51RetainedIndex → ℝ) (t : ℝ) (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    FourCellOddP53PlusMomentConditions r →
      t ^ 2 * (kappaTail * (∫ x : ℝ in 0..1, r x ^ 2)) ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP51RetainedProfile a + fun x ↦ t * r x)

theorem fourCellOddP51P53PlusMiddleCoerciveAt_iff
    (kappaTail : ℝ) :
    FourCellOddP51P53PlusMiddleCoerciveAt kappaTail ↔
      FourCellOddFiniteLegendreTailMiddleCoerciveAt 24 kappaTail := by
  rfl

/-- The tail-specific middle estimate and the existing finite-pivot/residual
certificate close the complete form-dual target without global coercivity. -/
theorem fourCellOddP1OrthogonalFormDualBound_of_P51HighTailGalerkinRiesz
    (kappaTail : ℝ) (hkappaTail : 0 ≤ kappaTail)
    (hmiddle : FourCellOddP51P53PlusMiddleCoerciveAt kappaTail)
    (hpivot : FourCellOddP51GalerkinPivotNonnegative)
    (hdual : FourCellOddP51GalerkinP53PlusResidualDual kappaTail) :
    FourCellOddP1OrthogonalFormDualBound := by
  apply
    fourCellOddP1OrthogonalFormDualBound_of_finiteSolvedHighTailGalerkinRiesz
      24 kappaTail hkappaTail
  · exact
      (fourCellOddP51P53PlusMiddleCoerciveAt_iff kappaTail).1 hmiddle
  · exact hpivot
  · exact hdual

/-- Certificate-form handoff using the existing `P51` pivot-plus-dual
certificate at the stronger tail constant. -/
theorem fourCellOddP1OrthogonalFormDualBound_of_P51HighTailCertificate
    (kappaTail : ℝ) (hkappaTail : 0 ≤ kappaTail)
    (hmiddle : FourCellOddP51P53PlusMiddleCoerciveAt kappaTail)
    (hcert : FourCellOddP51GalerkinRieszCertificate kappaTail) :
    FourCellOddP1OrthogonalFormDualBound :=
  fourCellOddP1OrthogonalFormDualBound_of_P51HighTailGalerkinRiesz
    kappaTail hkappaTail hmiddle hcert.1 hcert.2

/-- Production handoff: the high-tail middle estimate, nonnegative P51
pivot, and residual dual imply the corrected odd Riesz defect. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_P51HighTailGalerkinRiesz
    (kappaTail : ℝ) (hkappaTail : 0 ≤ kappaTail)
    (hmiddle : FourCellOddP51P53PlusMiddleCoerciveAt kappaTail)
    (hpivot : FourCellOddP51GalerkinPivotNonnegative)
    (hdual : FourCellOddP51GalerkinP53PlusResidualDual kappaTail) :
    FourCellOddP11CoupledRieszDefectNonnegative :=
  (fourCellOddP11CoupledRieszDefectNonnegative_iff_P1OrthogonalFormDual).2
    (fourCellOddP1OrthogonalFormDualBound_of_P51HighTailGalerkinRiesz
      kappaTail hkappaTail hmiddle hpivot hdual)

/-- Certificate-form production handoff. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_P51HighTailCertificate
    (kappaTail : ℝ) (hkappaTail : 0 ≤ kappaTail)
    (hmiddle : FourCellOddP51P53PlusMiddleCoerciveAt kappaTail)
    (hcert : FourCellOddP51GalerkinRieszCertificate kappaTail) :
    FourCellOddP11CoupledRieszDefectNonnegative :=
  fourCellOddP11CoupledRieszDefectNonnegative_of_P51HighTailGalerkinRiesz
    kappaTail hkappaTail hmiddle hcert.1 hcert.2

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailGalerkinRieszStructural
