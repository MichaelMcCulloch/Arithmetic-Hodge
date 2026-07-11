import ArithmeticHodge.Analysis.CoerciveRieszCorrection

namespace ArithmeticHodge.Analysis

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
local instance : IsScalarTower ℝ ℂ E := RestrictScalars.isScalarTower ℝ ℂ E

/-- The real part of a bounded complex sesquilinear form, viewed as a real bilinear form. -/
noncomputable def complexToRealForm
    (B : E →L⋆[ℂ] E →L[ℂ] ℂ) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun x y ↦ (B x y).re)
      (fun _ _ _ ↦ by simp)
      (fun c x y ↦ by
        change (B ((c : ℂ) • x) y).re = c * (B x y).re
        rw [B.map_smulₛₗ₂]
        simp)
      (fun _ _ _ ↦ by simp)
      (fun _ _ _ ↦ by simp))
    ‖B‖ fun x y ↦
      (Complex.abs_re_le_norm (B x y)).trans (B.le_opNorm₂ x y)

@[simp] theorem complexToRealForm_apply
    (B : E →L⋆[ℂ] E →L[ℂ] ℂ) (x y : E) :
    complexToRealForm B x y = (B x y).re :=
  rfl

theorem complexToRealForm_isCoercive
    (B : E →L⋆[ℂ] E →L[ℂ] ℂ) {mu : ℝ} (hmu : 0 < mu)
    (hcoercive : ∀ x, mu * ‖x‖ * ‖x‖ ≤ (B x x).re) :
    IsCoercive (complexToRealForm B) :=
  ⟨mu, hmu, by simpa using hcoercive⟩

/-- The real part of a bounded complex-linear functional. -/
noncomputable def realPartFunctional
    (ell : StrongDual ℂ E) : StrongDual ℝ E :=
  Complex.reCLM.comp (ell.restrictScalars ℝ)

@[simp] theorem realPartFunctional_apply
    (ell : StrongDual ℂ E) (x : E) :
    realPartFunctional ell x = (ell x).re :=
  rfl

/-- The complex solution obtained by applying real Lax--Milgram to real parts. -/
noncomputable def complexLaxMilgramSolution
    [CompleteSpace E] {B : E →L⋆[ℂ] E →L[ℂ] ℂ}
    (hB : IsCoercive (complexToRealForm B))
    (ell : StrongDual ℂ E) : E :=
  coerciveRieszCorrection hB (realPartFunctional ell)

theorem complexLaxMilgramSolution_real_apply
    [CompleteSpace E] {B : E →L⋆[ℂ] E →L[ℂ] ℂ}
    (hB : IsCoercive (complexToRealForm B))
    (ell : StrongDual ℂ E) (x : E) :
    complexToRealForm B (complexLaxMilgramSolution hB ell) x =
      (ell x).re := by
  simpa [complexLaxMilgramSolution] using
    coerciveRieszCorrection_apply hB (realPartFunctional ell) x

theorem complexLaxMilgramSolution_apply
    [CompleteSpace E] {B : E →L⋆[ℂ] E →L[ℂ] ℂ}
    (hB : IsCoercive (complexToRealForm B))
    (ell : StrongDual ℂ E) (x : E) :
    B (complexLaxMilgramSolution hB ell) x = ell x := by
  apply Complex.ext
  · exact complexLaxMilgramSolution_real_apply hB ell x
  · have hI := complexLaxMilgramSolution_real_apply hB ell (Complex.I • x)
    simpa using congrArg Neg.neg hI

theorem complexLaxMilgramSolution_apply_flip
    [CompleteSpace E] {B : E →L⋆[ℂ] E →L[ℂ] ℂ}
    (hB : IsCoercive (complexToRealForm B))
    (hHerm : B.toLinearMap₁₂.IsSymm)
    (ell : StrongDual ℂ E) (x : E) :
    B x (complexLaxMilgramSolution hB ell) = star (ell x) := by
  calc
    B x (complexLaxMilgramSolution hB ell) =
        star (B (complexLaxMilgramSolution hB ell) x) := by
      simpa using (hHerm.eq (complexLaxMilgramSolution hB ell) x).symm
    _ = star (ell x) := congrArg star (complexLaxMilgramSolution_apply hB ell x)

end

end ArithmeticHodge.Analysis
