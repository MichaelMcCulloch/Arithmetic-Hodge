import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false

namespace ArithmeticHodge.Analysis

noncomputable section

open UniformSpace

/-!
# Extension of bounded linear maps to normed completions

A bounded real linear map into a complete normed space extends uniquely from
its source to the normed completion.  This module packages the extension,
its value on the dense algebraic carrier, and the inherited norm bounds.
-/

section

variable {E G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
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

/-- Extend a bounded real linear map to the normed completion of its source. -/
noncomputable def completionLinearExtension
    (B : E →L[ℝ] G) : Completion E →L[ℝ] G :=
  B.extend (Completion.toComplL : E →L[ℝ] Completion E)

@[simp] theorem completionLinearExtension_coe
    (B : E →L[ℝ] G) (x : E) :
    completionLinearExtension B (x : Completion E) = B x := by
  change completionLinearExtension B
      ((Completion.toComplL : E →L[ℝ] Completion E) x) = B x
  exact ContinuousLinearMap.extend_eq B
    (denseRange_toComplL E) (isUniformInducing_toComplL E) x

/-- Extending a bounded linear map to the source completion does not increase
its operator norm. -/
theorem norm_completionLinearExtension_le (B : E →L[ℝ] G) :
    ‖completionLinearExtension B‖ ≤ ‖B‖ := by
  simpa only [completionLinearExtension, NNReal.coe_one, one_mul] using
    (ContinuousLinearMap.opNorm_extend_le B
      (N := 1) (denseRange_toComplL E) (fun x ↦ by simp))

/-- Pointwise norm bound for the completed linear map. -/
theorem norm_completionLinearExtension_apply_le
    (B : E →L[ℝ] G) (x : Completion E) :
    ‖completionLinearExtension B x‖ ≤ ‖B‖ * ‖x‖ := by
  calc
    ‖completionLinearExtension B x‖ ≤
        ‖completionLinearExtension B‖ * ‖x‖ :=
      (completionLinearExtension B).le_opNorm x
    _ ≤ ‖B‖ * ‖x‖ := by
      gcongr
      exact norm_completionLinearExtension_le B

end

end


end ArithmeticHodge.Analysis
