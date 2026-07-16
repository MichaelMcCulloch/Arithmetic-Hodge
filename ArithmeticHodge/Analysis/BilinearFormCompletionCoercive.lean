import ArithmeticHodge.Analysis.BilinearFormCompletion
import ArithmeticHodge.Analysis.CoerciveRieszCorrection
import Mathlib.Analysis.InnerProductSpace.Completion

set_option autoImplicit false

namespace ArithmeticHodge.Analysis

noncomputable section

open UniformSpace

/-!
# Diagonal bounds for completed bilinear forms

A bounded real bilinear form is determined on the completion by its values on
the dense algebraic carrier.  Consequently diagonal lower and upper bounds,
symmetry, and coercivity pass to `completionBilinearExtension` with exactly
the same constants.  For real pre-Hilbert carriers, the resulting coercive
form also feeds directly into the existing Lax--Milgram Riesz correction.
-/

section Bounds

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An algebraic diagonal lower bound passes unchanged to the normed
completion. -/
theorem completionBilinearExtension_diagonal_lower_bound
    (B : E →L[ℝ] E →L[ℝ] ℝ) (mu : ℝ)
    (hB : ∀ x : E, mu * ‖x‖ * ‖x‖ ≤ B x x)
    (z : Completion E) :
    mu * ‖z‖ * ‖z‖ ≤ completionBilinearExtension B z z := by
  refine Completion.induction_on z
    (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro x
  simpa only [completionBilinearExtension_coe_coe,
    Completion.norm_coe] using hB x

/-- An algebraic diagonal upper bound passes unchanged to the normed
completion. -/
theorem completionBilinearExtension_diagonal_upper_bound
    (B : E →L[ℝ] E →L[ℝ] ℝ) (M : ℝ)
    (hB : ∀ x : E, B x x ≤ M * ‖x‖ * ‖x‖)
    (z : Completion E) :
    completionBilinearExtension B z z ≤ M * ‖z‖ * ‖z‖ := by
  refine Completion.induction_on z
    (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro x
  simpa only [completionBilinearExtension_coe_coe,
    Completion.norm_coe] using hB x

/-- A two-sided algebraic diagonal estimate passes to the completion with
both constants unchanged. -/
theorem completionBilinearExtension_diagonal_bounds
    (B : E →L[ℝ] E →L[ℝ] ℝ) (mu M : ℝ)
    (hB : ∀ x : E,
      mu * ‖x‖ * ‖x‖ ≤ B x x ∧ B x x ≤ M * ‖x‖ * ‖x‖)
    (z : Completion E) :
    mu * ‖z‖ * ‖z‖ ≤ completionBilinearExtension B z z ∧
      completionBilinearExtension B z z ≤ M * ‖z‖ * ‖z‖ := by
  constructor
  · exact completionBilinearExtension_diagonal_lower_bound B mu
      (fun x ↦ (hB x).1) z
  · exact completionBilinearExtension_diagonal_upper_bound B M
      (fun x ↦ (hB x).2) z

/-- Symmetry on the dense algebraic carrier determines symmetry of the
completed bilinear form. -/
theorem completionBilinearExtension_symm
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ x y : E, B x y = B y x)
    (x y : Completion E) :
    completionBilinearExtension B x y =
      completionBilinearExtension B y x := by
  refine Completion.induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x₀
  refine Completion.induction_on y
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro y₀
  simpa only [completionBilinearExtension_coe_coe] using hB x₀ y₀

/-- Coercivity on the algebraic carrier passes to the completed bilinear
form. -/
theorem isCoercive_completionBilinearExtension
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B) :
    IsCoercive (completionBilinearExtension B) := by
  rcases hB with ⟨mu, hmu, hdiag⟩
  exact ⟨mu, hmu,
    completionBilinearExtension_diagonal_lower_bound B mu hdiag⟩

end Bounds

section Riesz

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lax--Milgram Riesz correction for the completed extension of an
algebraically coercive bilinear form. -/
noncomputable def completionBilinearRieszCorrection
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : IsCoercive B)
    (ell : StrongDual ℝ (Completion E)) : Completion E :=
  coerciveRieszCorrection
    (isCoercive_completionBilinearExtension B hB) ell

@[simp] theorem completionBilinearRieszCorrection_apply
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : IsCoercive B)
    (ell : StrongDual ℝ (Completion E)) (w : Completion E) :
    completionBilinearExtension B
        (completionBilinearRieszCorrection hB ell) w = ell w := by
  exact coerciveRieszCorrection_apply
    (isCoercive_completionBilinearExtension B hB) ell w

/-- The algebraic coercivity constant gives the same quantitative norm bound
for the completed Riesz correction. -/
theorem norm_completionBilinearRieszCorrection_le
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : IsCoercive B)
    (ell : StrongDual ℝ (Completion E)) {mu : ℝ} (hmu : 0 < mu)
    (hdiag : ∀ x : E, mu * ‖x‖ * ‖x‖ ≤ B x x) :
    ‖completionBilinearRieszCorrection hB ell‖ ≤ ‖ell‖ / mu := by
  exact norm_coerciveRieszCorrection_le
    (isCoercive_completionBilinearExtension B hB) ell hmu
    (completionBilinearExtension_diagonal_lower_bound B mu hdiag)

/-- The completed Riesz correction also inherits the standard energy bound
with the unchanged algebraic coercivity constant. -/
theorem completionBilinearRieszCorrection_energy_le
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : IsCoercive B)
    (ell : StrongDual ℝ (Completion E)) {mu : ℝ} (hmu : 0 < mu)
    (hdiag : ∀ x : E, mu * ‖x‖ * ‖x‖ ≤ B x x) :
    completionBilinearExtension B
        (completionBilinearRieszCorrection hB ell)
        (completionBilinearRieszCorrection hB ell) ≤ ‖ell‖ ^ 2 / mu := by
  exact coerciveRieszCorrection_energy_le
    (isCoercive_completionBilinearExtension B hB) ell hmu
    (completionBilinearExtension_diagonal_lower_bound B mu hdiag)

end Riesz

end

end ArithmeticHodge.Analysis
