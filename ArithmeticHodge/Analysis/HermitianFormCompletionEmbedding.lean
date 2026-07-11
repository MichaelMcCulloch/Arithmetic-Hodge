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
