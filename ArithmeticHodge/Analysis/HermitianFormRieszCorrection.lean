import ArithmeticHodge.Analysis.HermitianFormCompletionBasic
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false

open scoped ComplexConjugate InnerProductSpace

namespace ArithmeticHodge.Analysis

noncomputable section

namespace FormSpace

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {q : PositiveHermitianForm V}

def algebraicFunctional
    (ell : V →ₗ[ℂ] ℂ) :
    FormSpace q →ₗ[ℂ] ℂ where
  toFun x := ell x.toV
  map_add' x y := by simp
  map_smul' c x := by simp

noncomputable def boundedFunctional
    (ell : V →ₗ[ℂ] ℂ) (C : ℝ)
    (h : ∀ x : FormSpace q,
      ‖ell x.toV‖ ≤ C * ‖x‖) :
    StrongDual ℂ (FormSpace q) :=
  (algebraicFunctional ell).mkContinuous C h

@[simp] theorem boundedFunctional_apply
    (ell : V →ₗ[ℂ] ℂ) (C : ℝ)
    (h : ∀ x : FormSpace q,
      ‖ell x.toV‖ ≤ C * ‖x‖)
    (x : FormSpace q) :
    boundedFunctional ell C h x = ell x.toV := rfl

noncomputable def completedFunctional
    (ell : V →ₗ[ℂ] ℂ) (C : ℝ)
    (h : ∀ x : FormSpace q,
      ‖ell x.toV‖ ≤ C * ‖x‖) :
    StrongDual ℂ (Completion q) :=
  completionExtension (boundedFunctional ell C h)

@[simp] theorem completedFunctional_coe
    (ell : V →ₗ[ℂ] ℂ) (C : ℝ)
    (h : ∀ x : FormSpace q,
      ‖ell x.toV‖ ≤ C * ‖x‖)
    (x : FormSpace q) :
    completedFunctional ell C h
      (x : Completion q) = ell x.toV := by
  simp [completedFunctional]

noncomputable def rieszCorrection
    (ell : V →ₗ[ℂ] ℂ) (C : ℝ)
    (h : ∀ x : FormSpace q,
      ‖ell x.toV‖ ≤ C * ‖x‖) :
    Completion q :=
  (InnerProductSpace.toDual ℂ
    (Completion q)).symm
      (completedFunctional ell C h)

@[simp] theorem rieszCorrection_inner
    (ell : V →ₗ[ℂ] ℂ) (C : ℝ)
    (h : ∀ x : FormSpace q,
      ‖ell x.toV‖ ≤ C * ‖x‖)
    (z : Completion q) :
    ⟪rieszCorrection ell C h, z⟫_ℂ =
      completedFunctional ell C h z := by
  exact InnerProductSpace.toDual_symm_apply

@[simp] theorem rieszCorrection_inner_coe
    (ell : V →ₗ[ℂ] ℂ) (C : ℝ)
    (h : ∀ x : FormSpace q,
      ‖ell x.toV‖ ≤ C * ‖x‖)
    (x : FormSpace q) :
    ⟪rieszCorrection ell C h,
      (x : Completion q)⟫_ℂ =
        ell x.toV := by
  simp

theorem norm_rieszCorrection_le
    (ell : V →ₗ[ℂ] ℂ) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ x : FormSpace q,
      ‖ell x.toV‖ ≤ C * ‖x‖) :
    ‖rieszCorrection ell C h‖ ≤ C := by
  calc
    ‖rieszCorrection ell C h‖ =
        ‖completedFunctional ell C h‖ := by
      exact (InnerProductSpace.toDual ℂ
        (Completion q)).symm.norm_map _
    _ ≤ C :=
      norm_completionExtension_le
        (boundedFunctional ell C h) hC h

theorem pairing_bound_of_sq_bound
    (ell : V →ₗ[ℂ] ℂ) {S : ℝ}
    (hS : 0 ≤ S)
    (h : ∀ x : FormSpace q,
      ‖ell x.toV‖ ^ 2 ≤ S * ‖x‖ ^ 2)
    (x : FormSpace q) :
    ‖ell x.toV‖ ≤ Real.sqrt S * ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _)
      (norm_nonneg _))]
  simpa [mul_pow, Real.sq_sqrt hS] using h x

noncomputable def rieszCorrectionOfSqBound
    (ell : V →ₗ[ℂ] ℂ) {S : ℝ}
    (hS : 0 ≤ S)
    (h : ∀ x : FormSpace q,
      ‖ell x.toV‖ ^ 2 ≤ S * ‖x‖ ^ 2) :
    Completion q :=
  rieszCorrection ell (Real.sqrt S)
    (pairing_bound_of_sq_bound ell hS h)

@[simp] theorem rieszCorrectionOfSqBound_inner_coe
    (ell : V →ₗ[ℂ] ℂ) {S : ℝ}
    (hS : 0 ≤ S)
    (h : ∀ x : FormSpace q,
      ‖ell x.toV‖ ^ 2 ≤ S * ‖x‖ ^ 2)
    (x : FormSpace q) :
    ⟪rieszCorrectionOfSqBound ell hS h,
      (x : Completion q)⟫_ℂ =
        ell x.toV := by
  simp [rieszCorrectionOfSqBound]

theorem norm_sq_rieszCorrectionOfSqBound_le
    (ell : V →ₗ[ℂ] ℂ) {S : ℝ}
    (hS : 0 ≤ S)
    (h : ∀ x : FormSpace q,
      ‖ell x.toV‖ ^ 2 ≤ S * ‖x‖ ^ 2) :
    ‖rieszCorrectionOfSqBound ell hS h‖ ^ 2 ≤ S := by
  calc
    ‖rieszCorrectionOfSqBound ell hS h‖ ^ 2 ≤
        (Real.sqrt S) ^ 2 := by
      gcongr
      exact norm_rieszCorrection_le ell
        (Real.sqrt_nonneg S)
        (pairing_bound_of_sq_bound ell hS h)
    _ = S := Real.sq_sqrt hS

theorem norm_form_apply_comm (w x : V) :
    ‖q.form w x‖ = ‖q.form x w‖ := by
  rw [← q.conj_apply w x]
  exact norm_star _

noncomputable def formRieszCorrectionOfSqBound
    (w : V) {S : ℝ} (hS : 0 ≤ S)
    (h : ∀ x : FormSpace q,
      ‖q.form x.toV w‖ ^ 2 ≤
        S * ‖x‖ ^ 2) :
    Completion q :=
  rieszCorrectionOfSqBound (q.form w) hS
    fun x ↦ by
      simpa [norm_form_apply_comm] using h x

@[simp] theorem formRieszCorrectionOfSqBound_inner_coe
    (w : V) {S : ℝ} (hS : 0 ≤ S)
    (h : ∀ x : FormSpace q,
      ‖q.form x.toV w‖ ^ 2 ≤
        S * ‖x‖ ^ 2)
    (x : FormSpace q) :
    ⟪formRieszCorrectionOfSqBound w hS h,
      (x : Completion q)⟫_ℂ =
        q.form w x.toV := by
  simp [formRieszCorrectionOfSqBound]

@[simp] theorem coe_inner_formRieszCorrectionOfSqBound
    (w : V) {S : ℝ} (hS : 0 ≤ S)
    (h : ∀ x : FormSpace q,
      ‖q.form x.toV w‖ ^ 2 ≤
        S * ‖x‖ ^ 2)
    (x : FormSpace q) :
    ⟪(x : Completion q),
      formRieszCorrectionOfSqBound
        w hS h⟫_ℂ =
          q.form x.toV w := by
  rw [← inner_conj_symm]
  rw [formRieszCorrectionOfSqBound_inner_coe]
  exact q.conj_apply x.toV w

theorem norm_sq_formRieszCorrectionOfSqBound_le
    (w : V) {S : ℝ} (hS : 0 ≤ S)
    (h : ∀ x : FormSpace q,
      ‖q.form x.toV w‖ ^ 2 ≤
        S * ‖x‖ ^ 2) :
    ‖formRieszCorrectionOfSqBound
      w hS h‖ ^ 2 ≤ S := by
  exact norm_sq_rieszCorrectionOfSqBound_le
    (q.form w) hS fun x ↦ by
      simpa [norm_form_apply_comm] using h x

section ExternalLowMode

variable {A : Type*} [AddCommGroup A] [Module ℂ A]

def externalLowFunctional
    (B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ)
    (incl : V →ₗ[ℂ] A) (w : A) :
    V →ₗ[ℂ] ℂ :=
  (B w).comp incl

@[simp] theorem externalLowFunctional_apply
    (B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ)
    (incl : V →ₗ[ℂ] A)
    (w : A) (x : V) :
    externalLowFunctional B incl w x =
      B w (incl x) := rfl

noncomputable def externalLowRieszCorrectionOfSqBound
    (B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ)
    (hB : ∀ x y, star (B y x) = B x y)
    (incl : V →ₗ[ℂ] A) (w : A)
    {S : ℝ} (hS : 0 ≤ S)
    (h : ∀ x : FormSpace q,
      ‖B (incl x.toV) w‖ ^ 2 ≤
        S * ‖x‖ ^ 2) :
    Completion q :=
  rieszCorrectionOfSqBound
    (externalLowFunctional B incl w) hS
      fun x ↦ by
        have hnorm :
            ‖B w (incl x.toV)‖ =
              ‖B (incl x.toV) w‖ := by
          rw [← hB w (incl x.toV)]
          exact norm_star _
        simpa [externalLowFunctional, hnorm]
          using h x

@[simp] theorem externalLowRieszCorrection_inner_coe
    (B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ)
    (hB : ∀ x y, star (B y x) = B x y)
    (incl : V →ₗ[ℂ] A) (w : A)
    {S : ℝ} (hS : 0 ≤ S)
    (h : ∀ x : FormSpace q,
      ‖B (incl x.toV) w‖ ^ 2 ≤
        S * ‖x‖ ^ 2)
    (x : FormSpace q) :
    ⟪externalLowRieszCorrectionOfSqBound
        B hB incl w hS h,
      (x : Completion q)⟫_ℂ =
        B w (incl x.toV) := by
  simp [externalLowRieszCorrectionOfSqBound,
    externalLowFunctional]

@[simp] theorem coe_inner_externalLowRieszCorrection
    (B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ)
    (hB : ∀ x y, star (B y x) = B x y)
    (incl : V →ₗ[ℂ] A) (w : A)
    {S : ℝ} (hS : 0 ≤ S)
    (h : ∀ x : FormSpace q,
      ‖B (incl x.toV) w‖ ^ 2 ≤
        S * ‖x‖ ^ 2)
    (x : FormSpace q) :
    ⟪(x : Completion q),
      externalLowRieszCorrectionOfSqBound
        B hB incl w hS h⟫_ℂ =
          B (incl x.toV) w := by
  rw [← inner_conj_symm,
    externalLowRieszCorrection_inner_coe]
  exact hB (incl x.toV) w

theorem norm_sq_externalLowRieszCorrection_le
    (B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ)
    (hB : ∀ x y, star (B y x) = B x y)
    (incl : V →ₗ[ℂ] A) (w : A)
    {S : ℝ} (hS : 0 ≤ S)
    (h : ∀ x : FormSpace q,
      ‖B (incl x.toV) w‖ ^ 2 ≤
        S * ‖x‖ ^ 2) :
    ‖externalLowRieszCorrectionOfSqBound
      B hB incl w hS h‖ ^ 2 ≤ S := by
  apply norm_sq_rieszCorrectionOfSqBound_le

end ExternalLowMode

end FormSpace

end

end ArithmeticHodge.Analysis
