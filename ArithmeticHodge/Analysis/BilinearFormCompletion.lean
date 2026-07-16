import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false

namespace ArithmeticHodge.Analysis

noncomputable section

open UniformSpace

/-!
# Extension of bounded bilinear maps to normed completions

The completion API extends one continuous linear map at a time.  A bounded
bilinear map is extended first in its second variable and then in its first;
the norm is not increased at either step.  This packages the construction
needed for phase forms on products of completed Fourier tails.
-/

section

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

private theorem denseRange_toComplL (H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H] :
    DenseRange (Completion.toComplL : H →L[ℝ] Completion H) := by
  simpa only [Completion.coe_toComplL] using
    (Completion.isDenseInducing_coe (α := H)).dense

private theorem isUniformInducing_toComplL (H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H] :
    IsUniformInducing (Completion.toComplL : H →L[ℝ] Completion H) := by
  simpa only [Completion.coe_toComplL] using
    Completion.isUniformInducing_coe H

private noncomputable def completionBilinearExtendRight
    (B : E →L[ℝ] F →L[ℝ] G) (x : E) :
    Completion F →L[ℝ] G :=
  (B x).extend (Completion.toComplL : F →L[ℝ] Completion F)

@[simp] private theorem completionBilinearExtendRight_coe
    (B : E →L[ℝ] F →L[ℝ] G) (x : E) (y : F) :
    completionBilinearExtendRight B x (y : Completion F) = B x y := by
  exact ContinuousLinearMap.extend_eq (B x)
    (denseRange_toComplL F) (isUniformInducing_toComplL F) y

private theorem norm_completionBilinearExtendRight_le
    (B : E →L[ℝ] F →L[ℝ] G) (x : E) :
    ‖completionBilinearExtendRight B x‖ ≤ ‖B x‖ := by
  simpa only [completionBilinearExtendRight, NNReal.coe_one, one_mul] using
    (ContinuousLinearMap.opNorm_extend_le (B x)
      (N := 1) (denseRange_toComplL F) (fun y ↦ by simp))

private noncomputable def completionBilinearExtendRightLinear
    (B : E →L[ℝ] F →L[ℝ] G) :
    E →ₗ[ℝ] (Completion F →L[ℝ] G) where
  toFun := completionBilinearExtendRight B
  map_add' x y := by
    ext z
    refine Completion.induction_on z
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro w
    simp
  map_smul' c x := by
    ext z
    refine Completion.induction_on z
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro w
    simp

private noncomputable def completionBilinearExtendRightContinuous
    (B : E →L[ℝ] F →L[ℝ] G) :
    E →L[ℝ] (Completion F →L[ℝ] G) :=
  (completionBilinearExtendRightLinear B).mkContinuous ‖B‖ (fun x ↦
    (norm_completionBilinearExtendRight_le B x).trans (B.le_opNorm x))

@[simp] private theorem completionBilinearExtendRightContinuous_apply
    (B : E →L[ℝ] F →L[ℝ] G) (x : E) :
    completionBilinearExtendRightContinuous B x =
      completionBilinearExtendRight B x :=
  rfl

private theorem norm_completionBilinearExtendRightContinuous_le
    (B : E →L[ℝ] F →L[ℝ] G) :
    ‖completionBilinearExtendRightContinuous B‖ ≤ ‖B‖ := by
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg B) _

/-- Extend a bounded real bilinear map to the normed completions of both
source spaces. -/
noncomputable def completionBilinearExtension
    (B : E →L[ℝ] F →L[ℝ] G) :
    Completion E →L[ℝ] Completion F →L[ℝ] G :=
  (completionBilinearExtendRightContinuous B).extend
    (Completion.toComplL : E →L[ℝ] Completion E)

@[simp] theorem completionBilinearExtension_coe_coe
    (B : E →L[ℝ] F →L[ℝ] G) (x : E) (y : F) :
    completionBilinearExtension B (x : Completion E) (y : Completion F) =
      B x y := by
  change completionBilinearExtension B
      ((Completion.toComplL : E →L[ℝ] Completion E) x)
      ((Completion.toComplL : F →L[ℝ] Completion F) y) = B x y
  rw [completionBilinearExtension,
    ContinuousLinearMap.extend_eq _
      (denseRange_toComplL E) (isUniformInducing_toComplL E)]
  exact completionBilinearExtendRight_coe B x y

/-- Extending a bounded bilinear map to completions does not increase its
operator norm. -/
theorem norm_completionBilinearExtension_le
    (B : E →L[ℝ] F →L[ℝ] G) :
    ‖completionBilinearExtension B‖ ≤ ‖B‖ := by
  have h := ContinuousLinearMap.opNorm_extend_le
    (completionBilinearExtendRightContinuous B)
    (N := 1) (denseRange_toComplL E) (fun x ↦ by simp)
  have h' : ‖completionBilinearExtension B‖ ≤
      ‖completionBilinearExtendRightContinuous B‖ := by
    simpa only [completionBilinearExtension, NNReal.coe_one, one_mul] using h
  exact h'.trans (norm_completionBilinearExtendRightContinuous_le B)

/-- Pointwise norm bound for the completed bilinear map. -/
theorem norm_completionBilinearExtension_apply_le
    (B : E →L[ℝ] F →L[ℝ] G)
    (x : Completion E) (y : Completion F) :
    ‖completionBilinearExtension B x y‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ := by
  calc
    ‖completionBilinearExtension B x y‖ ≤
        ‖completionBilinearExtension B‖ * ‖x‖ * ‖y‖ :=
      (completionBilinearExtension B).le_opNorm₂ x y
    _ ≤ ‖B‖ * ‖x‖ * ‖y‖ := by
      gcongr
      exact norm_completionBilinearExtension_le B

end

end

end ArithmeticHodge.Analysis
