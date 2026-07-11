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
