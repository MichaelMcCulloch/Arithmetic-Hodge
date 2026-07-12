import ArithmeticHodge.Analysis.YoshidaOddCoercivityAssembly
import ArithmeticHodge.Analysis.HermitianFormCompletionBasic

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaOddHomogeneousCoercivity

open YoshidaOddCoercivityAssembly
open YoshidaCoercivityNumerics
open YoshidaClippedCircleBridge
open YoshidaClippedCircleFaithful
open YoshidaSectionSixAnalytic
open YoshidaWeightedTailBounds

/-!
# Homogeneous coercivity on Yoshida's tenth odd tail

The normalized Section 6 estimate is promoted to every vector in the actual
periodic odd tail by exact quadratic scaling.  The zero-energy case is handled
through faithfulness of the centered-circle coordinate, not by a positivity
assumption on the critical form.
-/

/-- Source `L²` energy on the clipped interval. -/
def clippedIntervalEnergy
    {a : ℝ} (f : YoshidaClippedSmooth a) : ℝ :=
  ∫ x : ℝ in -a..a, ‖(f : ℝ → ℂ) x‖ ^ 2

theorem clippedIntervalEnergy_smul
    {a : ℝ} (c : ℂ) (f : YoshidaClippedSmooth a) :
    clippedIntervalEnergy (c • f) = ‖c‖ ^ 2 * clippedIntervalEnergy f := by
  unfold clippedIntervalEnergy
  calc
    (∫ x : ℝ in -a..a, ‖((c • f : YoshidaClippedSmooth a) : ℝ → ℂ) x‖ ^ 2) =
        ∫ x : ℝ in -a..a, ‖c‖ ^ 2 * ‖(f : ℝ → ℂ) x‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x _
      change ‖c • (f : ℝ → ℂ) x‖ ^ 2 = _
      rw [norm_smul]
      ring
    _ = ‖c‖ ^ 2 * ∫ x : ℝ in -a..a, ‖(f : ℝ → ℂ) x‖ ^ 2 := by
      rw [intervalIntegral.integral_const_mul]

/-- The real diagonal of the clipped sesquilinear form scales exactly by the
scalar norm square. -/
theorem clippedCriticalFormValue_smul
    {a : ℝ} (ha : 0 < a) (c : ℂ) (f : YoshidaClippedSmooth a) :
    clippedCriticalFormValue a ha (c • f) =
      ‖c‖ ^ 2 * clippedCriticalFormValue a ha f := by
  unfold clippedCriticalFormValue
  rw [map_smul, LinearMap.map_smulₛₗ₂]
  simp only [smul_eq_mul]
  rw [← mul_assoc, Complex.mul_conj]
  simp [Complex.sq_norm]

/-- Vanishing clipped interval energy forces the function itself to vanish.
This is the zero-energy input needed for honest homogenization. -/
theorem eq_zero_of_clippedIntervalEnergy_eq_zero
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (henergy : clippedIntervalEnergy f = 0) :
    f = 0 := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  have hscaled :
      (2 * a) * ‖yoshidaClippedCircleL2 ha f‖ ^ 2 = 0 := by
    have hcircle := lebesgueNormSq_yoshidaClippedCircleL2 ha f
    rw [lebesgueNormSq] at hcircle
    rw [show (∫ x : ℝ in -a..a, ‖(f : ℝ → ℂ) x‖ ^ 2) = 0 by
      simpa only [clippedIntervalEnergy] using henergy] at hcircle
    exact hcircle
  have hnormSq : ‖yoshidaClippedCircleL2 ha f‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖yoshidaClippedCircleL2 ha f‖]
  have hcircleZero : yoshidaClippedCircleL2 ha f = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)
  apply yoshidaClippedCircleL2_injective ha
  simpa using hcircleZero

/-- The normalized odd-tail estimate scales to every vector in the tenth odd
tail. -/
theorem oddTenTail_clipped_form_value_coercive
    (f : YoshidaClippedPeriodicCore yoshidaA)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10) :
    (38 / 25 : ℝ) *
        (∫ x : ℝ in -yoshidaA..yoshidaA,
          ‖((f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) x‖ ^ 2) ≤
      clippedCriticalFormValue yoshidaA yoshidaA_pos
        (f : YoshidaClippedSmooth yoshidaA) := by
  change (38 / 25 : ℝ) *
      clippedIntervalEnergy (f : YoshidaClippedSmooth yoshidaA) ≤
    clippedCriticalFormValue yoshidaA yoshidaA_pos
      (f : YoshidaClippedSmooth yoshidaA)
  let E : ℝ := clippedIntervalEnergy
    (f : YoshidaClippedSmooth yoshidaA)
  have hEnonneg : 0 ≤ E := by
    dsimp only [E, clippedIntervalEnergy]
    exact intervalIntegral.integral_nonneg (by linarith [yoshidaA_pos])
      (fun _ _ ↦ sq_nonneg _)
  by_cases hEzero : E = 0
  · have hfSmoothZero : (f : YoshidaClippedSmooth yoshidaA) = 0 :=
      eq_zero_of_clippedIntervalEnergy_eq_zero yoshidaA_pos
        (f : YoshidaClippedSmooth yoshidaA) (by simpa only [E] using hEzero)
    have hfZero : f = 0 := Subtype.ext hfSmoothZero
    subst f
    simp [clippedIntervalEnergy, clippedCriticalFormValue]
  · have hEpos : 0 < E := lt_of_le_of_ne hEnonneg (Ne.symm hEzero)
    let c : ℂ := (((Real.sqrt E)⁻¹ : ℝ) : ℂ)
    let g : YoshidaClippedPeriodicCore yoshidaA := c • f
    have hgf : g ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10 := by
      dsimp only [g]
      exact (yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10).smul_mem c hf
    have hscale : E * ‖c‖ ^ 2 = 1 := by
      dsimp only [c]
      rw [Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg E)),
        inv_pow, Real.sq_sqrt hEpos.le]
      exact mul_inv_cancel₀ hEpos.ne'
    have hgEnergy : clippedIntervalEnergy
        (g : YoshidaClippedSmooth yoshidaA) = 1 := by
      change clippedIntervalEnergy
          (c • (f : YoshidaClippedSmooth yoshidaA)) = 1
      rw [clippedIntervalEnergy_smul, mul_comm, hscale]
    have hunit : (38 / 25 : ℝ) ≤
        clippedCriticalFormValue yoshidaA yoshidaA_pos
          (g : YoshidaClippedSmooth yoshidaA) := by
      apply oddTenTail_clipped_form_value_ge_38_div_25_of_unit_energy g hgf
      simpa only [clippedIntervalEnergy] using hgEnergy
    have hmul := mul_le_mul_of_nonneg_left hunit hEnonneg
    dsimp only [E] at hmul ⊢
    calc
      (38 / 25 : ℝ) * clippedIntervalEnergy
          (f : YoshidaClippedSmooth yoshidaA) =
          clippedIntervalEnergy (f : YoshidaClippedSmooth yoshidaA) *
            (38 / 25 : ℝ) := by ring
      _ ≤ clippedIntervalEnergy (f : YoshidaClippedSmooth yoshidaA) *
          clippedCriticalFormValue yoshidaA yoshidaA_pos
            (g : YoshidaClippedSmooth yoshidaA) := hmul
      _ = clippedIntervalEnergy (f : YoshidaClippedSmooth yoshidaA) *
          (‖c‖ ^ 2 * clippedCriticalFormValue yoshidaA yoshidaA_pos
            (f : YoshidaClippedSmooth yoshidaA)) := by
        congr 1
        change clippedCriticalFormValue yoshidaA yoshidaA_pos
            (c • (f : YoshidaClippedSmooth yoshidaA)) = _
        exact clippedCriticalFormValue_smul yoshidaA_pos c
          (f : YoshidaClippedSmooth yoshidaA)
      _ = clippedCriticalFormValue yoshidaA yoshidaA_pos
          (f : YoshidaClippedSmooth yoshidaA) := by
        rw [← mul_assoc]
        change E * ‖c‖ ^ 2 * _ = _
        rw [hscale, one_mul]

/-! ## Bundled form on the actual odd tail -/

/-- The actual periodic tenth odd tail, as a complex vector space. -/
abbrev YoshidaOddTenTail :=
  yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10

instance oddTenTailAddCommGroup : AddCommGroup YoshidaOddTenTail := by
  change AddCommGroup
    ↥(yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)
  exact Submodule.addCommGroup
    (R := ℂ) (M := YoshidaClippedPeriodicCore yoshidaA)
    (yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)

instance oddTenTailModule :
    @Module ℂ YoshidaOddTenTail Complex.instSemiring
      (@AddCommGroup.toAddCommMonoid YoshidaOddTenTail
        oddTenTailAddCommGroup) := by
  letI : AddCommGroup YoshidaOddTenTail := oddTenTailAddCommGroup
  exact Submodule.module
    (R := ℂ) (M := YoshidaClippedPeriodicCore yoshidaA)
    (yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)

/-- The canonical linear inclusion of the periodic odd tail into the clipped
smooth carrier on which the local critical form is defined. -/
def oddTenTailToClippedSmooth :
    YoshidaOddTenTail →ₗ[ℂ] YoshidaClippedSmooth yoshidaA :=
  (yoshidaClippedPeriodicCoreSubmodule yoshidaA).subtype.comp
    (yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10).subtype

@[simp] theorem oddTenTailToClippedSmooth_apply
    (f : YoshidaOddTenTail) :
    oddTenTailToClippedSmooth f =
      ((f : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) :=
  rfl

/-- Yoshida's clipped local critical form restricted to the actual periodic
tenth odd tail. -/
def oddTenTailCriticalForm :
    YoshidaOddTenTail →ₗ⋆[ℂ] YoshidaOddTenTail →ₗ[ℂ] ℂ :=
  (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos).comp
      oddTenTailToClippedSmooth
    |>.compl₂ oddTenTailToClippedSmooth

@[simp] theorem oddTenTailCriticalForm_apply
    (f g : YoshidaOddTenTail) :
    oddTenTailCriticalForm f g =
      yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (oddTenTailToClippedSmooth f) (oddTenTailToClippedSmooth g) :=
  rfl

/-- Source `L²` coercivity of the restricted odd-tail critical form. -/
theorem oddTenTailCriticalForm_coercive (f : YoshidaOddTenTail) :
    (38 / 25 : ℝ) * clippedIntervalEnergy
        (oddTenTailToClippedSmooth f) ≤
      (oddTenTailCriticalForm f f).re := by
  exact oddTenTail_clipped_form_value_coercive
    (f : YoshidaClippedPeriodicCore yoshidaA) f.property

private theorem oddTenTailIntervalEnergy_nonneg (f : YoshidaOddTenTail) :
    0 ≤ clippedIntervalEnergy (oddTenTailToClippedSmooth f) := by
  unfold clippedIntervalEnergy
  exact intervalIntegral.integral_nonneg (by linarith [yoshidaA_pos])
    (fun _ _ ↦ sq_nonneg _)

/-- The restricted odd-tail critical form is positive and definite as a
consequence of the proved coercive estimate and source faithfulness.  No
positivity or definiteness premise is added. -/
def oddTenTailPositiveHermitianForm :
    @PositiveHermitianForm YoshidaOddTenTail
      oddTenTailAddCommGroup oddTenTailModule where
  form := oddTenTailCriticalForm
  conj_apply f g := by
    exact yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos
      (oddTenTailToClippedSmooth f) (oddTenTailToClippedSmooth g)
  re_apply_self_nonneg f := by
    have hcoercive := oddTenTailCriticalForm_coercive f
    have henergy := oddTenTailIntervalEnergy_nonneg f
    have hC : 0 < (38 / 25 : ℝ) := by norm_num
    exact (mul_nonneg hC.le henergy).trans hcoercive
  definite f hform := by
    have hcoercive := oddTenTailCriticalForm_coercive f
    have henergy := oddTenTailIntervalEnergy_nonneg f
    have hC : 0 < (38 / 25 : ℝ) := by norm_num
    have hformRe : (oddTenTailCriticalForm f f).re = 0 := by
      simpa using congrArg Complex.re hform
    have henergyZero : clippedIntervalEnergy
        (oddTenTailToClippedSmooth f) = 0 := by
      apply le_antisymm
      · apply nonpos_of_mul_nonpos_right
        · simpa only [hformRe] using hcoercive
        · exact hC
      · exact henergy
    have hfSmooth : oddTenTailToClippedSmooth f = 0 :=
      eq_zero_of_clippedIntervalEnergy_eq_zero yoshidaA_pos
        (oddTenTailToClippedSmooth f) henergyZero
    apply Subtype.ext
    apply Subtype.ext
    exact hfSmooth

/-- The bundled positive Hermitian form retains the explicit source `L²`
coercivity constant. -/
theorem oddTenTailPositiveHermitianForm_coercive
    (f : YoshidaOddTenTail) :
    (38 / 25 : ℝ) * clippedIntervalEnergy
        (oddTenTailToClippedSmooth f) ≤
      ((@PositiveHermitianForm.form YoshidaOddTenTail
        oddTenTailAddCommGroup oddTenTailModule
        oddTenTailPositiveHermitianForm) f f).re :=
  by
    simpa [oddTenTailPositiveHermitianForm] using
      oddTenTailCriticalForm_coercive f

end ArithmeticHodge.Analysis.YoshidaOddHomogeneousCoercivity
