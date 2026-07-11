/-
  The real-space archimedean contribution in Bombieri's explicit formula.

  Its apparent pole at `x = 1` is removable because the numerator vanishes
  there.  At infinity, inversion exposes the integrable `x⁻²` Jacobian and
  correction terms.  Thus the source formula defines an honest Bochner
  integral on every positive-half-line test function.  The normalization is
  Bombieri, *Remarks on Weil's quadratic functional*, p. 186.
-/

import ArithmeticHodge.Analysis.MultiplicativeWeil
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- Bombieri's real-space archimedean integrand on `(1, ∞)`. -/
def bombieriArchIntegrand (f : BombieriTest) (x : ℝ) : ℂ :=
  (f x + transpose (f : ℝ → ℂ) x -
      (2 / (x : ℂ)) * f 1) *
    (x : ℂ) / ((x : ℂ) ^ 2 - 1)

/-- On the positive half-line this is the numerator after expanding the
linear transpose. -/
private def bombieriArchNumerator (f : BombieriTest) (x : ℝ) : ℂ :=
  f x + f x⁻¹ / (x : ℂ) - (2 / (x : ℂ)) * f 1

@[simp]
private theorem bombieriArchNumerator_one (f : BombieriTest) :
    bombieriArchNumerator f 1 = 0 := by
  simp [bombieriArchNumerator]
  ring

private theorem bombieriArchNumerator_contDiffOn (f : BombieriTest) :
    ContDiffOn ℝ ∞ (bombieriArchNumerator f) (Ioi 0) := by
  intro x hx
  unfold bombieriArchNumerator
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hfinv : ContDiffAt ℝ ∞ (fun y : ℝ ↦ f y⁻¹) x := by
    exact f.contDiff.contDiffAt.comp x (contDiffAt_id.inv hx0)
  have hcast : ContDiff ℝ ∞ (fun y : ℝ ↦ (y : ℂ)) :=
    Complex.ofRealCLM.contDiff
  have hcastInv : ContDiffAt ℝ ∞ (fun y : ℝ ↦ ((y : ℂ)⁻¹)) x := by
    exact hcast.contDiffAt.inv (Complex.ofReal_ne_zero.mpr hx0)
  have htwoInv : ContDiffAt ℝ ∞ (fun y : ℝ ↦ (2 : ℂ) * (y : ℂ)⁻¹) x := by
    fun_prop
  simpa only [div_eq_mul_inv] using
    ((f.contDiff.contDiffAt.add (hfinv.mul hcastInv)).sub
      (htwoInv.mul contDiffAt_const)).contDiffWithinAt

/-- The numerator's divided difference supplies the removable value at `1`. -/
private def bombieriArchLocalExtension (f : BombieriTest) (x : ℝ) : ℂ :=
  ((x : ℂ) / ((x : ℂ) + 1)) *
    dslope (bombieriArchNumerator f) 1 x

private theorem bombieriArchLocalExtension_continuousOn (f : BombieriTest) :
    ContinuousOn (bombieriArchLocalExtension f) (Ioi 0) := by
  have hNcont : ContinuousOn (bombieriArchNumerator f) (Ioi 0) :=
    (bombieriArchNumerator_contDiffOn f).continuousOn
  have hNdiff : DifferentiableAt ℝ (bombieriArchNumerator f) 1 :=
    (bombieriArchNumerator_contDiffOn f).differentiableOn (by simp) 1
      (show (1 : ℝ) ∈ Ioi 0 by norm_num)
      |>.differentiableAt (Ioi_mem_nhds zero_lt_one)
  have hslope : ContinuousOn
      (dslope (bombieriArchNumerator f) 1) (Ioi 0) :=
    (continuousOn_dslope (Ioi_mem_nhds zero_lt_one)).2 ⟨hNcont, hNdiff⟩
  intro x hx
  apply ContinuousWithinAt.mul _ (hslope x hx)
  have hxpos : 0 < x := hx
  have hden : (x : ℂ) + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  exact ((Complex.ofRealCLM.continuous.continuousAt.div
    (Complex.ofRealCLM.continuous.continuousAt.add continuousAt_const)
    hden).continuousWithinAt)

private theorem bombieriArchIntegrand_eq_localExtension
    (f : BombieriTest) {x : ℝ} (hx : 1 < x) :
    bombieriArchIntegrand f x = bombieriArchLocalExtension f x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hx1 : x ≠ 1 := ne_of_gt hx
  rw [bombieriArchIntegrand, transpose_apply_of_pos _ hx0]
  unfold bombieriArchLocalExtension
  have hslope : dslope (bombieriArchNumerator f) 1 x =
      bombieriArchNumerator f x / ((x : ℂ) - 1) := by
    rw [dslope_of_ne _ hx1, slope_def_module,
      bombieriArchNumerator_one, sub_zero]
    change (((x - 1)⁻¹ : ℝ) : ℂ) * bombieriArchNumerator f x = _
    push_cast
    rw [div_eq_mul_inv]
    ring
  rw [hslope]
  unfold bombieriArchNumerator
  field_simp
  ring

private theorem bombieriArchIntegrableOn_Ioc_one_two (f : BombieriTest) :
    IntegrableOn (bombieriArchIntegrand f) (Ioc 1 2) := by
  have hextContinuous : ContinuousOn (bombieriArchLocalExtension f) (Icc 1 2) :=
    (bombieriArchLocalExtension_continuousOn f).mono (by
      intro x hx
      exact zero_lt_one.trans_le hx.1)
  have hextIntegrable :
      IntegrableOn (bombieriArchLocalExtension f) (Ioc 1 2) :=
    (hextContinuous.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  refine hextIntegrable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact (bombieriArchIntegrand_eq_localExtension f hx.1).symm

private def bombieriArchDirectTail (f : BombieriTest) (x : ℝ) : ℂ :=
  (x / (x ^ 2 - 1)) • f x

private def bombieriArchReflectedTail (f : BombieriTest) (x : ℝ) : ℂ :=
  (x ^ 2 / (x ^ 2 - 1)) •
    (x ^ (-2 : ℝ) • f (x ^ (-1 : ℝ)))

private def bombieriArchCorrectionTail (f : BombieriTest) (x : ℝ) : ℂ :=
  (-2 : ℝ) • ((x ^ 2 / (x ^ 2 - 1)) •
    (x ^ (-2 : ℝ) • f 1))

private theorem bombieriArchIntegrand_eq_tail_sum
    (f : BombieriTest) {x : ℝ} (hx : 2 < x) :
    bombieriArchIntegrand f x =
      bombieriArchDirectTail f x + bombieriArchReflectedTail f x +
        bombieriArchCorrectionTail f x := by
  have hx0 : 0 < x := by linarith
  have hxne : x ≠ 0 := hx0.ne'
  have hdenR : x ^ 2 - 1 ≠ 0 := by
    nlinarith [sq_nonneg (x - 1)]
  have hdenC : (x : ℂ) ^ 2 - 1 ≠ 0 := by
    have hcast : (((x ^ 2 - 1 : ℝ) : ℂ)) = (x : ℂ) ^ 2 - 1 := by
      push_cast
      rfl
    rw [← hcast]
    exact Complex.ofReal_ne_zero.mpr hdenR
  rw [bombieriArchIntegrand, transpose_apply_of_pos _ hx0]
  unfold bombieriArchDirectTail bombieriArchReflectedTail
    bombieriArchCorrectionTail
  rw [Real.rpow_neg hx0.le, Real.rpow_two, Real.rpow_neg_one]
  simp only [Complex.real_smul]
  push_cast
  field_simp [hxne, hdenR, hdenC]
  ring

private theorem directTail_integrableOn_Ioi_two (f : BombieriTest) :
    IntegrableOn (bombieriArchDirectTail f) (Ioi 2) := by
  have hf : Integrable (f : ℝ → ℂ) :=
    f.contDiff.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hcoeffContinuous : ContinuousOn
      (fun x : ℝ ↦ x / (x ^ 2 - 1)) (Ioi 2) := by
    intro x hx
    have hx' : 2 < x := hx
    have hden : x ^ 2 - 1 ≠ 0 := by
      nlinarith [sq_nonneg (x - 1)]
    exact (continuousAt_id.div
      ((continuousAt_id.pow 2).sub continuousAt_const) hden).continuousWithinAt
  have hcoeffMeas : AEStronglyMeasurable
      (fun x : ℝ ↦ x / (x ^ 2 - 1)) (volume.restrict (Ioi 2)) :=
    hcoeffContinuous.aestronglyMeasurable measurableSet_Ioi
  have hcoeffBound : ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioi 2)),
      ‖x / (x ^ 2 - 1)‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : 2 < x := hx
    have hxpos : 0 < x := by linarith
    have hdenpos : 0 < x ^ 2 - 1 := by
      nlinarith [sq_nonneg (x - 1)]
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hxpos hdenpos)]
    apply (div_le_one hdenpos).2
    nlinarith [sq_nonneg (x - 1)]
  have h := hf.integrableOn.bdd_smul 1 hcoeffMeas hcoeffBound
  unfold bombieriArchDirectTail
  change IntegrableOn
    ((fun x : ℝ ↦ x / (x ^ 2 - 1)) • (f : ℝ → ℂ)) (Ioi 2)
  exact h

private theorem reflectedTail_integrableOn_Ioi_two (f : BombieriTest) :
    IntegrableOn (bombieriArchReflectedTail f) (Ioi 2) := by
  have hf : Integrable (f : ℝ → ℂ) :=
    f.contDiff.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hbase : IntegrableOn
      (fun x : ℝ ↦ x ^ (-2 : ℝ) • f (x ^ (-1 : ℝ))) (Ioi 2) := by
    have hbase0 : IntegrableOn
        (fun x : ℝ ↦ x ^ ((-1 : ℝ) - 1) • f (x ^ (-1 : ℝ))) (Ioi 0) :=
      (integrableOn_Ioi_comp_rpow_iff' (f : ℝ → ℂ)
        (by norm_num : (-1 : ℝ) ≠ 0)).2 hf.integrableOn
    exact (hbase0.congr_fun (fun x _ ↦ by norm_num) measurableSet_Ioi).mono_set
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 2))
  have hcoeffContinuous : ContinuousOn
      (fun x : ℝ ↦ x ^ 2 / (x ^ 2 - 1)) (Ioi 2) := by
    intro x hx
    have hx' : 2 < x := hx
    have hden : x ^ 2 - 1 ≠ 0 := by
      nlinarith [sq_nonneg (x - 1)]
    exact ((continuousAt_id.pow 2).div
      ((continuousAt_id.pow 2).sub continuousAt_const) hden).continuousWithinAt
  have hcoeffMeas : AEStronglyMeasurable
      (fun x : ℝ ↦ x ^ 2 / (x ^ 2 - 1)) (volume.restrict (Ioi 2)) :=
    hcoeffContinuous.aestronglyMeasurable measurableSet_Ioi
  have hcoeffBound : ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioi 2)),
      ‖x ^ 2 / (x ^ 2 - 1)‖ ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : 2 < x := hx
    have hxpos : 0 < x := by linarith
    have hdenpos : 0 < x ^ 2 - 1 := by
      nlinarith [sq_nonneg (x - 1)]
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (sq_pos_of_pos hxpos) hdenpos)]
    apply (div_le_iff₀ hdenpos).2
    nlinarith [sq_nonneg (x - 1)]
  have h := hbase.bdd_smul 2 hcoeffMeas hcoeffBound
  unfold bombieriArchReflectedTail
  change IntegrableOn
    ((fun x : ℝ ↦ x ^ 2 / (x ^ 2 - 1)) •
      (fun x : ℝ ↦ x ^ (-2 : ℝ) • f (x ^ (-1 : ℝ)))) (Ioi 2)
  exact h

private theorem correctionTail_integrableOn_Ioi_two (f : BombieriTest) :
    IntegrableOn (bombieriArchCorrectionTail f) (Ioi 2) := by
  have hbase : IntegrableOn
      (fun x : ℝ ↦ x ^ (-2 : ℝ) • f 1) (Ioi 2) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 2)).smul_const (f 1)
  have hcoeffContinuous : ContinuousOn
      (fun x : ℝ ↦ x ^ 2 / (x ^ 2 - 1)) (Ioi 2) := by
    intro x hx
    have hx' : 2 < x := hx
    have hden : x ^ 2 - 1 ≠ 0 := by
      nlinarith [sq_nonneg (x - 1)]
    exact ((continuousAt_id.pow 2).div
      ((continuousAt_id.pow 2).sub continuousAt_const) hden).continuousWithinAt
  have hscaled : IntegrableOn
      (fun x : ℝ ↦ (x ^ 2 / (x ^ 2 - 1)) •
        (x ^ (-2 : ℝ) • f 1)) (Ioi 2) := by
    have hcoeffMeas : AEStronglyMeasurable
        (fun x : ℝ ↦ x ^ 2 / (x ^ 2 - 1)) (volume.restrict (Ioi 2)) :=
      hcoeffContinuous.aestronglyMeasurable measurableSet_Ioi
    have hcoeffBound : ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioi 2)),
        ‖x ^ 2 / (x ^ 2 - 1)‖ ≤ 2 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : 2 < x := hx
      have hxpos : 0 < x := by linarith
      have hdenpos : 0 < x ^ 2 - 1 := by
        nlinarith [sq_nonneg (x - 1)]
      rw [Real.norm_eq_abs, abs_of_pos (div_pos (sq_pos_of_pos hxpos) hdenpos)]
      apply (div_le_iff₀ hdenpos).2
      nlinarith [sq_nonneg (x - 1)]
    have h := hbase.bdd_smul 2 hcoeffMeas hcoeffBound
    simpa only [Pi.smul_apply] using h
  exact hscaled.smul (-2 : ℝ)

private theorem bombieriArchIntegrableOn_Ioi_two (f : BombieriTest) :
    IntegrableOn (bombieriArchIntegrand f) (Ioi 2) := by
  have hsum := (directTail_integrableOn_Ioi_two f).add
    (reflectedTail_integrableOn_Ioi_two f) |>.add
      (correctionTail_integrableOn_Ioi_two f)
  refine hsum.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (bombieriArchIntegrand_eq_tail_sum f hx).symm

/-- Bombieri's real-space archimedean kernel is Bochner integrable.  Near
`1` the proof uses its removable divided-difference extension; at infinity
it uses compact support after the inversion substitution and the integrable
Jacobian/correction `x⁻²`. -/
theorem bombieriArchIntegrand_integrable (f : BombieriTest) :
    IntegrableOn (bombieriArchIntegrand f) (Ioi 1) := by
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 2)]
  exact (bombieriArchIntegrableOn_Ioc_one_two f).union
    (bombieriArchIntegrableOn_Ioi_two f)

/-- Bombieri's real-space archimedean contribution, including its local
constant term. -/
def bombieriArchTerm (f : BombieriTest) : ℂ :=
  -((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) * f 1 -
    ∫ x : ℝ in Ioi 1, bombieriArchIntegrand f x

private theorem bombieriArchIntegrand_add
    (f g : BombieriTest) (x : ℝ) :
    bombieriArchIntegrand (f + g) x =
      bombieriArchIntegrand f x + bombieriArchIntegrand g x := by
  simp only [bombieriArchIntegrand, TestFunction.coe_add, Pi.add_apply,
    transpose]
  ring

private theorem bombieriArchIntegrand_smul
    (c : ℂ) (f : BombieriTest) (x : ℝ) :
    bombieriArchIntegrand (c • f) x = c * bombieriArchIntegrand f x := by
  simp only [bombieriArchIntegrand, TestFunction.coe_smul, Pi.smul_apply,
    smul_eq_mul, transpose]
  ring

/-- The convergent archimedean integral, packaged as a complex-linear map. -/
def bombieriArchIntegralLinearMap : BombieriTest →ₗ[ℂ] ℂ where
  toFun f := ∫ x : ℝ in Ioi 1, bombieriArchIntegrand f x
  map_add' f g := by
    rw [show bombieriArchIntegrand (f + g) = fun x ↦
        bombieriArchIntegrand f x + bombieriArchIntegrand g x by
      funext x
      exact bombieriArchIntegrand_add f g x]
    exact integral_add (bombieriArchIntegrand_integrable f)
      (bombieriArchIntegrand_integrable g)
  map_smul' c f := by
    rw [show bombieriArchIntegrand (c • f) = fun x ↦
        c * bombieriArchIntegrand f x by
      funext x
      exact bombieriArchIntegrand_smul c f x]
    exact integral_const_mul c (bombieriArchIntegrand f)

@[simp]
theorem bombieriArchIntegralLinearMap_apply (f : BombieriTest) :
    bombieriArchIntegralLinearMap f =
      ∫ x : ℝ in Ioi 1, bombieriArchIntegrand f x := rfl

private def bombieriEvaluationAtOne : BombieriTest →ₗ[ℂ] ℂ where
  toFun f := f 1
  map_add' f g := by simp
  map_smul' c f := by simp

/-- The full constant-plus-integral archimedean contribution as a complex-
linear functional. -/
def bombieriArchTermLinearMap : BombieriTest →ₗ[ℂ] ℂ :=
  (-((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ)) •
      bombieriEvaluationAtOne -
    bombieriArchIntegralLinearMap

@[simp]
theorem bombieriArchTermLinearMap_apply (f : BombieriTest) :
    bombieriArchTermLinearMap f = bombieriArchTerm f := rfl

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
