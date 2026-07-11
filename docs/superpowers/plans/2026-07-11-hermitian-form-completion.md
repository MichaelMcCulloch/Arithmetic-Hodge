# Hermitian Form Completion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize Yoshida's source-faithful form-norm completion, bounded low-tail pairing extension, Riesz correction, and coercive continuous map to the ambient Hilbert space.

**Architecture:** Put the algebraic positive Hermitian form, isolated form-norm wrapper, Hilbert completion, and continuous-extension helper in a basic module. Build squared-bound and external-low-mode Riesz corrections in a second module. Put the coercive map to an ambient complete normed space in a third module, deliberately without an injectivity claim, and expose the three through a thin facade.

**Tech Stack:** Lean 4, Mathlib `InnerProductSpace.Core`, `UniformSpace.Completion`, normed-additive-hom extension, complex Fréchet--Riesz duality, and continuous linear maps.

## Global Constraints

- No `sorry`, `admit`, custom `axiom`, unsafe declaration, `native_decide`, or RH-equivalent proof bypass.
- Preserve all 159 inventoried legacy untracked Lean research files byte-for-byte.
- Work directly on `main` as explicitly authorized by the user; commit and independently review each task separately.
- Run only one implementation subagent at a time; each task owns only its named production and temporary scratch files.
- Every production theorem must first have a strict RED that fails for the expected missing declaration or module.
- Every production module and interface scratch must pass `lake env lean -DwarningAsError=true`; the repository must pass `lake build ArithmeticHodge`.
- Run global forbidden-proof and scratch-naming scans, exact legacy-inventory comparison, dependency inspection, and `#print axioms` audits before every commit.
- Every public theorem must use only `[propext, Classical.choice, Quot.sound]` or a subset.
- Keep these modules independent of circle `L²`, Fourier normalization, Yoshida cutoffs/constants, finite Gram matrices, Bombieri tests, and RH statements.
- `FormSpace` must remain a genuine wrapper structure; do not use a reducible type synonym that could inherit an ambient norm or topology.
- Do not assume that the Hermitian form is bounded for an ambient `L²` norm.
- Do not assert that the completed coercive map to the ambient space is injective; that requires Yoshida Proposition 4's separate closability/separation argument.
- Respect Mathlib's convention that complex inner products and sesquilinear forms are conjugate-linear in the first slot.

---

### Task 1: Form-generated Hilbert completion and continuous extension

**Files:**

- Create: `ArithmeticHodge/Analysis/HermitianFormCompletionBasic.lean`
- Test: `HermitianFormCompletionBasicScratch.lean` (temporary; delete before commit)

**Interfaces:**

- Consumes: Mathlib algebraic sesquilinear forms, `InnerProductSpace.Core`, `UniformSpace.Completion`, and `NormedAddGroupHom.extension`.
- Produces: `PositiveHermitianForm`; `FormSpace`; its algebraic, normed-group, and inner-product instances; `FormSpace.Completion`; `completion_inner_coe`; `completion_norm_coe`; `completionExtension`; and its pointwise/op-norm bounds.

- [ ] **Step 1: Write and run the strict missing-module RED**

Create `HermitianFormCompletionBasicScratch.lean`:

```lean
import ArithmeticHodge.Analysis.HermitianFormCompletionBasic

set_option autoImplicit false

namespace ArithmeticHodge.Analysis

#check PositiveHermitianForm
#check FormSpace
#check FormSpace.inner_eq_form
#check FormSpace.norm_sq_eq_form_re
#check FormSpace.Completion
#check FormSpace.completion_inner_coe
#check FormSpace.completion_norm_coe
#check FormSpace.completionExtension
#check FormSpace.completionExtension_coe
#check FormSpace.norm_completionExtension_apply_le
#check FormSpace.norm_completionExtension_le

end ArithmeticHodge.Analysis
```

- [ ] **Step 2: Run RED and record the expected failure**

Run:

```bash
lake env lean -DwarningAsError=true HermitianFormCompletionBasicScratch.lean
```

Expected: nonzero exit because `ArithmeticHodge.Analysis.HermitianFormCompletionBasic` does not exist. Any syntax or unrelated elaboration error is not an acceptable RED.

- [ ] **Step 3: Implement the production module**

Create `ArithmeticHodge/Analysis/HermitianFormCompletionBasic.lean`:

```lean
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Group.HomCompletion
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

set_option autoImplicit false

open scoped ComplexConjugate InnerProductSpace

namespace ArithmeticHodge.Analysis

noncomputable section

structure PositiveHermitianForm
    (V : Type*) [AddCommGroup V] [Module ℂ V] where
  form : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ
  conj_apply : ∀ x y, star (form y x) = form x y
  re_apply_self_nonneg : ∀ x, 0 ≤ (form x x).re
  definite : ∀ x, form x x = 0 → x = 0

structure FormSpace
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (q : PositiveHermitianForm V) where
  of :: toV : V

namespace FormSpace

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {q : PositiveHermitianForm V}

def equiv : FormSpace q ≃ V where
  toFun := toV
  invFun := of
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

instance : AddCommGroup (FormSpace q) := Equiv.addCommGroup equiv
instance : Module ℂ (FormSpace q) := Equiv.module ℂ equiv

@[simp] theorem toV_zero : (0 : FormSpace q).toV = 0 := rfl

@[simp] theorem toV_add (x y : FormSpace q) :
    (x + y).toV = x.toV + y.toV := rfl

@[simp] theorem toV_smul (c : ℂ) (x : FormSpace q) :
    (c • x).toV = c • x.toV := rfl

def toUnderlyingLinear : FormSpace q →ₗ[ℂ] V where
  toFun := toV
  map_add' x y := by simp
  map_smul' c x := by simp

@[implicit_reducible] def core :
    InnerProductSpace.Core ℂ (FormSpace q) where
  inner x y := q.form x.toV y.toV
  conj_inner_symm x y := q.conj_apply x.toV y.toV
  re_inner_nonneg x := q.re_apply_self_nonneg x.toV
  add_left x y z := LinearMap.map_add₂ q.form x.toV y.toV z.toV
  smul_left x y c := LinearMap.map_smulₛₗ₂ q.form c x.toV y.toV
  definite x hx := by
    rcases x with ⟨x⟩
    exact congrArg FormSpace.of (q.definite x hx)

instance : NormedAddCommGroup (FormSpace q) :=
  letI : InnerProductSpace.Core ℂ (FormSpace q) := core (q := q)
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (FormSpace q) :=
  InnerProductSpace.ofCore (𝕜 := ℂ) (core (q := q)).toCore

@[simp] theorem inner_eq_form (x y : FormSpace q) :
    ⟪x, y⟫_ℂ = q.form x.toV y.toV := rfl

@[simp] theorem norm_sq_eq_form_re (x : FormSpace q) :
    ‖x‖ ^ 2 = (q.form x.toV x.toV).re := by
  exact InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x

abbrev Completion (q : PositiveHermitianForm V) :=
  UniformSpace.Completion (FormSpace q)

@[simp] theorem completion_inner_coe (x y : FormSpace q) :
    ⟪(x : Completion q), (y : Completion q)⟫_ℂ =
      q.form x.toV y.toV := by
  simp

@[simp] theorem completion_norm_coe (x : FormSpace q) :
    ‖(x : Completion q)‖ = ‖x‖ := by
  exact UniformSpace.Completion.norm_coe x

section CompletionExtension

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F]

private def asNormedAddGroupHom
    (f : FormSpace q →L[ℂ] F) :
    NormedAddGroupHom (FormSpace q) F where
  toFun := f
  map_add' := f.map_add
  bound' := ⟨‖f‖, f.le_opNorm⟩

noncomputable def completionExtension
    (f : FormSpace q →L[ℂ] F) :
    Completion q →L[ℂ] F where
  toFun := (asNormedAddGroupHom f).extension
  map_add' := (asNormedAddGroupHom f).extension.map_add'
  map_smul' c x := by
    let g := (asNormedAddGroupHom f).extension
    have heq :
        (fun z : Completion q ↦ g (c • z)) =
          fun z ↦ c • g z := by
      apply UniformSpace.Completion.denseRange_coe.equalizer
      · exact g.continuous.comp (continuous_const_smul c)
      · exact (continuous_const_smul c).comp g.continuous
      · funext y
        change (asNormedAddGroupHom f).extension
            (c • (y : Completion q)) =
          c • (asNormedAddGroupHom f).extension
            (y : Completion q)
        rw [← UniformSpace.Completion.coe_smul,
          NormedAddGroupHom.extension_coe,
          NormedAddGroupHom.extension_coe]
        exact f.map_smul c y
    exact congrFun heq x
  cont := (asNormedAddGroupHom f).extension.continuous

@[simp] theorem completionExtension_coe
    (f : FormSpace q →L[ℂ] F) (x : FormSpace q) :
    completionExtension f (x : Completion q) = f x := by
  exact NormedAddGroupHom.extension_coe
    (asNormedAddGroupHom f) x

theorem norm_completionExtension_apply_le
    (f : FormSpace q →L[ℂ] F) {C : ℝ}
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖)
    (z : Completion q) :
    ‖completionExtension f z‖ ≤ C * ‖z‖ := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_le ?_ ?_) ?_
  · fun_prop
  · fun_prop
  · intro x
    simpa using h x

theorem norm_completionExtension_le
    (f : FormSpace q →L[ℂ] F) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖completionExtension f‖ ≤ C := by
  exact (completionExtension f).opNorm_le_bound hC
    (norm_completionExtension_apply_le f h)

end CompletionExtension

end FormSpace

end

end ArithmeticHodge.Analysis
```

- [ ] **Step 4: Verify GREEN, axioms, and repository invariants**

Run:

```bash
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/HermitianFormCompletionBasic.lean
lake build ArithmeticHodge.Analysis.HermitianFormCompletionBasic
lake env lean -DwarningAsError=true HermitianFormCompletionBasicScratch.lean
lake build ArithmeticHodge
```

Expected: all exit zero; the two strict commands produce no warnings. Audit
`inner_eq_form`, `norm_sq_eq_form_re`, `completion_inner_coe`,
`completion_norm_coe`, `completionExtension_coe`,
`norm_completionExtension_apply_le`, and
`norm_completionExtension_le`. Delete the scratch, run the global proof and
naming scans, compare exactly 159 legacy files to the archive ref, and inspect
the one-file diff.

- [ ] **Step 5: Commit**

```bash
git add ArithmeticHodge/Analysis/HermitianFormCompletionBasic.lean
git commit -m "add Hermitian form-norm completion"
```

---

### Task 2: Squared-bound and external-low-mode Riesz correction

**Files:**

- Create: `ArithmeticHodge/Analysis/HermitianFormRieszCorrection.lean`
- Test: `HermitianFormRieszCorrectionScratch.lean` (temporary; delete before commit)

**Interfaces:**

- Consumes: Task 1's `FormSpace.Completion` and `completionExtension`, plus Mathlib's complex Fréchet--Riesz equivalence.
- Produces: algebraic/bounded/completed functionals; ordinary and squared-bound Riesz corrections; same-space Hermitian convenience results; and the external-low-mode correction with both pairing orientations and an exact squared norm budget.

- [ ] **Step 1: Write and run the strict missing-module RED**

Create `HermitianFormRieszCorrectionScratch.lean`:

```lean
import ArithmeticHodge.Analysis.HermitianFormRieszCorrection

set_option autoImplicit false

namespace ArithmeticHodge.Analysis
namespace FormSpace

#check algebraicFunctional
#check boundedFunctional
#check completedFunctional
#check rieszCorrection
#check rieszCorrection_inner_coe
#check norm_rieszCorrection_le
#check pairing_bound_of_sq_bound
#check rieszCorrectionOfSqBound
#check norm_sq_rieszCorrectionOfSqBound_le
#check formRieszCorrectionOfSqBound
#check coe_inner_formRieszCorrectionOfSqBound
#check norm_sq_formRieszCorrectionOfSqBound_le
#check externalLowRieszCorrectionOfSqBound
#check coe_inner_externalLowRieszCorrection
#check externalLowRieszCorrection_inner_coe
#check norm_sq_externalLowRieszCorrection_le

end FormSpace
end ArithmeticHodge.Analysis
```

Run:

```bash
lake env lean -DwarningAsError=true HermitianFormRieszCorrectionScratch.lean
```

Expected: nonzero exit because the production module does not exist.

- [ ] **Step 2: Implement bounded functionals and squared Riesz bounds**

Create `ArithmeticHodge/Analysis/HermitianFormRieszCorrection.lean`:

```lean
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
```

- [ ] **Step 3: Verify GREEN, axioms, and repository invariants**

Run:

```bash
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/HermitianFormRieszCorrection.lean
lake build ArithmeticHodge.Analysis.HermitianFormRieszCorrection
lake env lean -DwarningAsError=true HermitianFormRieszCorrectionScratch.lean
lake build ArithmeticHodge
```

Expected: all exit zero. Audit every theorem named in the scratch, with special
attention to both pairing orientations and
`norm_sq_externalLowRieszCorrection_le`. Delete the scratch, run the global
proof/naming scans, compare exactly 159 legacy files to the archive ref, and
inspect the one-file diff.

- [ ] **Step 4: Commit**

```bash
git add ArithmeticHodge/Analysis/HermitianFormRieszCorrection.lean
git commit -m "represent bounded form-tail pairings"
```

---

### Task 3: Coercive ambient map and facade

**Files:**

- Create: `ArithmeticHodge/Analysis/HermitianFormCompletionEmbedding.lean`
- Create: `ArithmeticHodge/Analysis/HermitianFormCompletion.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `HermitianFormCompletionEmbeddingScratch.lean` (temporary; delete before commit)

**Interfaces:**

- Consumes: Task 1's `FormSpace.toUnderlyingLinear`, `completionExtension`, and norm bounds.
- Produces: the bounded algebraic underlying map; its extension to `FormSpace.Completion`; coercivity-to-norm estimates; source-shaped coercive completion maps; their canonical-image equations and op-norm estimate; and a facade importing all three form-completion modules.
- Explicitly does not produce an injectivity theorem.

- [ ] **Step 1: Write and run the strict missing-module RED**

Create `HermitianFormCompletionEmbeddingScratch.lean`:

```lean
import ArithmeticHodge.Analysis.HermitianFormCompletionEmbedding

set_option autoImplicit false

namespace ArithmeticHodge.Analysis
namespace FormSpace

#check boundedUnderlyingMap
#check completionToUnderlying
#check norm_completionToUnderlying_le
#check completionToUnderlying_coe
#check coercive_underlying_bound
#check coercive_underlying_bound_of_form
#check coerciveCompletionToUnderlying
#check coerciveCompletionToUnderlyingOfForm
#check norm_coerciveCompletionToUnderlyingOfForm_le
#check coerciveCompletionToUnderlying_coe
#check coerciveCompletionToUnderlyingOfForm_coe

end FormSpace
end ArithmeticHodge.Analysis
```

Run:

```bash
lake env lean -DwarningAsError=true HermitianFormCompletionEmbeddingScratch.lean
```

Expected: nonzero exit because the production module does not exist.

- [ ] **Step 2: Implement the coercive continuous map without injectivity**

Create `ArithmeticHodge/Analysis/HermitianFormCompletionEmbedding.lean`:

```lean
import ArithmeticHodge.Analysis.HermitianFormCompletionBasic

set_option autoImplicit false

namespace ArithmeticHodge.Analysis

noncomputable section

namespace FormSpace

variable {U : Type*} [NormedAddCommGroup U]
  [NormedSpace ℂ U] [CompleteSpace U]
variable {p : PositiveHermitianForm U}

noncomputable def boundedUnderlyingMap
    (C : ℝ)
    (h : ∀ x : FormSpace p,
      ‖x.toV‖ ≤ C * ‖x‖) :
    FormSpace p →L[ℂ] U :=
  (toUnderlyingLinear (q := p)).mkContinuous C h

noncomputable def completionToUnderlying
    (C : ℝ)
    (h : ∀ x : FormSpace p,
      ‖x.toV‖ ≤ C * ‖x‖) :
    Completion p →L[ℂ] U :=
  completionExtension (boundedUnderlyingMap C h)

theorem norm_completionToUnderlying_le
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : FormSpace p,
      ‖x.toV‖ ≤ C * ‖x‖) :
    ‖completionToUnderlying C h‖ ≤ C := by
  exact norm_completionExtension_le
    (boundedUnderlyingMap C h) hC h

@[simp] theorem completionToUnderlying_coe
    (C : ℝ)
    (h : ∀ x : FormSpace p,
      ‖x.toV‖ ≤ C * ‖x‖)
    (x : FormSpace p) :
    completionToUnderlying C h
      (x : Completion p) = x.toV := by
  simp [completionToUnderlying, boundedUnderlyingMap,
    toUnderlyingLinear]

omit [CompleteSpace U] in
theorem coercive_underlying_bound
    {mu : ℝ} (hmu : 0 < mu)
    (hcoercive : ∀ x : FormSpace p,
      mu * ‖x.toV‖ ^ 2 ≤ ‖x‖ ^ 2)
    (x : FormSpace p) :
    ‖x.toV‖ ≤
      (1 / Real.sqrt mu) * ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by positivity) (norm_nonneg _))]
  calc
    ‖x.toV‖ ^ 2 ≤ ‖x‖ ^ 2 / mu :=
      (le_div_iff₀ hmu).2 (by
        simpa [mul_comm] using hcoercive x)
    _ = ((1 / Real.sqrt mu) * ‖x‖) ^ 2 := by
      rw [mul_pow, div_pow, one_pow,
        Real.sq_sqrt hmu.le]
      ring

omit [CompleteSpace U] in
theorem coercive_underlying_bound_of_form
    {mu : ℝ} (hmu : 0 < mu)
    (hcoercive : ∀ x : FormSpace p,
      mu * ‖x.toV‖ ^ 2 ≤
        (p.form x.toV x.toV).re)
    (x : FormSpace p) :
    ‖x.toV‖ ≤
      (1 / Real.sqrt mu) * ‖x‖ := by
  apply coercive_underlying_bound hmu
  intro y
  simpa using hcoercive y

noncomputable def coerciveCompletionToUnderlying
    {mu : ℝ} (hmu : 0 < mu)
    (hcoercive : ∀ x : FormSpace p,
      mu * ‖x.toV‖ ^ 2 ≤ ‖x‖ ^ 2) :
    Completion p →L[ℂ] U :=
  completionToUnderlying (1 / Real.sqrt mu)
    (coercive_underlying_bound hmu hcoercive)

noncomputable def coerciveCompletionToUnderlyingOfForm
    {mu : ℝ} (hmu : 0 < mu)
    (hcoercive : ∀ x : FormSpace p,
      mu * ‖x.toV‖ ^ 2 ≤
        (p.form x.toV x.toV).re) :
    Completion p →L[ℂ] U :=
  completionToUnderlying (1 / Real.sqrt mu)
    (coercive_underlying_bound_of_form
      hmu hcoercive)

theorem norm_coerciveCompletionToUnderlyingOfForm_le
    {mu : ℝ} (hmu : 0 < mu)
    (hcoercive : ∀ x : FormSpace p,
      mu * ‖x.toV‖ ^ 2 ≤
        (p.form x.toV x.toV).re) :
    ‖coerciveCompletionToUnderlyingOfForm
      hmu hcoercive‖ ≤
        1 / Real.sqrt mu := by
  exact norm_completionToUnderlying_le
    (by positivity)
    (coercive_underlying_bound_of_form
      hmu hcoercive)

@[simp] theorem coerciveCompletionToUnderlying_coe
    {mu : ℝ} (hmu : 0 < mu)
    (hcoercive : ∀ x : FormSpace p,
      mu * ‖x.toV‖ ^ 2 ≤ ‖x‖ ^ 2)
    (x : FormSpace p) :
    coerciveCompletionToUnderlying hmu hcoercive
      (x : Completion p) = x.toV := by
  simp [coerciveCompletionToUnderlying]

@[simp] theorem coerciveCompletionToUnderlyingOfForm_coe
    {mu : ℝ} (hmu : 0 < mu)
    (hcoercive : ∀ x : FormSpace p,
      mu * ‖x.toV‖ ^ 2 ≤
        (p.form x.toV x.toV).re)
    (x : FormSpace p) :
    coerciveCompletionToUnderlyingOfForm
      hmu hcoercive (x : Completion p) =
        x.toV := by
  simp [coerciveCompletionToUnderlyingOfForm]

end FormSpace

end

end ArithmeticHodge.Analysis
```

Do not add any theorem claiming that `completionToUnderlying` or either
coercive specialization is injective.

- [ ] **Step 3: Add the facade and umbrella import**

Create `ArithmeticHodge/Analysis/HermitianFormCompletion.lean`:

```lean
import ArithmeticHodge.Analysis.HermitianFormCompletionBasic
import ArithmeticHodge.Analysis.HermitianFormRieszCorrection
import ArithmeticHodge.Analysis.HermitianFormCompletionEmbedding
```

Add exactly one umbrella import immediately after
`ArithmeticHodge.Analysis.HilbertTailSchur`:

```lean
import ArithmeticHodge.Analysis.HermitianFormCompletion
```

- [ ] **Step 4: Verify GREEN, facade, axioms, and repository invariants**

Run:

```bash
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/HermitianFormCompletionEmbedding.lean
lake build ArithmeticHodge.Analysis.HermitianFormCompletionEmbedding
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/HermitianFormCompletion.lean
lake build ArithmeticHodge.Analysis.HermitianFormCompletion
lake env lean -DwarningAsError=true HermitianFormCompletionEmbeddingScratch.lean
lake build ArithmeticHodge
```

Expected: all exit zero. Audit every theorem named in the scratch. Confirm by
source search that no injectivity theorem was added for the completion-to-
underlying maps. Delete the scratch, run the global proof/naming scans, compare
exactly 159 legacy files to the archive ref, and inspect only the embedding,
facade, and umbrella-import diffs.

- [ ] **Step 5: Commit**

```bash
git add ArithmeticHodge/Analysis/HermitianFormCompletionEmbedding.lean \
  ArithmeticHodge/Analysis/HermitianFormCompletion.lean ArithmeticHodge.lean
git commit -m "map coercive form completions to ambient space"
```
