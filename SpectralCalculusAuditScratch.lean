import ArithmeticHodge.Spectral.SpectralPositivity
import ArithmeticHodge.Analysis.FourierTransform

open scoped InnerProductSpace InnerProduct
open RCLike

namespace ArithmeticHodge.Spectral.SpectralCalculusAudit

noncomputable local instance propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-!
This scratch file audits `SpectralCalculus` and the claims built on it.  All
countermodels below are independent of the adèlic interfaces.
-/

/-! ## The production existence witness does not encode its operator -/

noncomputable def multiplicationOperator (a : ℝ) : UnboundedOperator ℂ where
  domain := ⊤
  toFun := fun x => (a : ℂ) * (x : ℂ)

theorem multiplicationOperator_isSelfAdjoint (a : ℝ) :
    (multiplicationOperator a).IsSelfAdjoint := by
  constructor
  · intro x y
    simp [multiplicationOperator]
    ring
  · intro y _
    simp [multiplicationOperator]

/-- The exact construction used by `spectralCalculus_exists`, exposed so its
semantics can be tested. -/
noncomputable def evaluationAtZeroCalculus
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : UnboundedOperator H) (hD : D.IsSelfAdjoint) : SpectralCalculus H D hD where
  apply f := f 0 • ContinuousLinearMap.id ℂ H
  apply_mul f g := by
    ext x
    simp only [Pi.mul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
    exact mul_smul _ _ _
  apply_star f := by
    simp only [Function.comp_apply, starRingEnd_apply]
    rw [← ContinuousLinearMap.star_eq_adjoint, star_smul,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id]
  apply_one := one_smul ℂ _
  apply_exp_tendsto hatom x y := by
    have hzeroMap := hatom 0
    simp only [ite_true, one_smul] at hzeroMap
    have hzero : ∀ v : H, v = 0 := fun v => by
      have hv := ContinuousLinearMap.ext_iff.mp hzeroMap v
      simpa using hv
    simp only [hzero x, hzero y, inner_zero_right]
    exact tendsto_const_nhds

theorem evaluationAtZero_apply_independent_of_operator
    (f : ℝ → ℂ) :
    (evaluationAtZeroCalculus (multiplicationOperator 0)
        (multiplicationOperator_isSelfAdjoint 0)).apply f =
      (evaluationAtZeroCalculus (multiplicationOperator 1)
        (multiplicationOperator_isSelfAdjoint 1)).apply f := by
  rfl

/-- For the operator `D = 1`, the advertised existence construction sends the
coordinate function to zero even though `D` itself acts as the identity. -/
theorem evaluationAtZero_does_not_recover_operator :
    (evaluationAtZeroCalculus (multiplicationOperator 1)
      (multiplicationOperator_isSelfAdjoint 1)).apply (fun t : ℝ => (t : ℂ)) = 0 ∧
    (multiplicationOperator 1).toFun ⟨1, by simp [multiplicationOperator]⟩ = 1 := by
  constructor
  · ext
    simp [evaluationAtZeroCalculus]
  · simp [multiplicationOperator]

/-- The `apply_exp_tendsto` proof for the production witness is vacuous on a
nonzero Hilbert space: its singleton-at-zero projection is the identity. -/
theorem evaluationAtZero_atomless_premise_false :
    ¬ ∀ l₀ : ℝ,
      (evaluationAtZeroCalculus (multiplicationOperator 1)
        (multiplicationOperator_isSelfAdjoint 1)).apply
          (fun l => if l = l₀ then 1 else 0) = 0 := by
  intro hatom
  have hzero := hatom 0
  have hzeroAtOne := congrArg (fun A : ℂ →L[ℂ] ℂ => A 1) hzero
  simp [evaluationAtZeroCalculus] at hzeroAtOne

/-! ## The first three structure laws do not define a star homomorphism -/

/-- A deliberately nonadditive multiplicative/star/unital map: it remembers
only whether a function is nowhere zero. -/
noncomputable def nowhereZeroScalar (f : ℝ → ℂ) : ℂ :=
  if (∀ x, f x ≠ 0) then 1 else 0

noncomputable def nowhereZeroApply (f : ℝ → ℂ) : ℂ →L[ℂ] ℂ :=
  nowhereZeroScalar f • ContinuousLinearMap.id ℂ ℂ

theorem nowhereZeroScalar_mul (f g : ℝ → ℂ) :
    nowhereZeroScalar (f * g) = nowhereZeroScalar f * nowhereZeroScalar g := by
  have hiff : (∀ x, (f * g) x ≠ 0) ↔
      (∀ x, f x ≠ 0) ∧ (∀ x, g x ≠ 0) := by
    constructor
    · intro h
      constructor
      · intro x hx
        exact (h x) (by simp [Pi.mul_apply, hx])
      · intro x hx
        exact (h x) (by simp [Pi.mul_apply, hx])
    · rintro ⟨hf, hg⟩ x
      exact mul_ne_zero (hf x) (hg x)
  simp only [nowhereZeroScalar, hiff]
  by_cases hf : ∀ x, f x ≠ 0 <;> by_cases hg : ∀ x, g x ≠ 0 <;>
    simp [hf, hg]

theorem nowhereZeroApply_mul (f g : ℝ → ℂ) :
    nowhereZeroApply (f * g) = (nowhereZeroApply f).comp (nowhereZeroApply g) := by
  ext
  simp [nowhereZeroApply, nowhereZeroScalar_mul, mul_smul, mul_comm]

theorem nowhereZeroApply_star (f : ℝ → ℂ) :
    nowhereZeroApply (starRingEnd ℂ ∘ f) = (nowhereZeroApply f)† := by
  have hiff : (∀ x, (starRingEnd ℂ ∘ f) x ≠ 0) ↔ ∀ x, f x ≠ 0 := by
    constructor
    · intro h x hx
      exact (h x) (by simp [Function.comp_apply, hx])
    · intro h x hx
      exact (h x) (by simpa using hx)
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  simp only [nowhereZeroApply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  rw [show nowhereZeroScalar (starRingEnd ℂ ∘ f) =
      starRingEnd ℂ (nowhereZeroScalar f) by
    simp only [nowhereZeroScalar, hiff]
    by_cases hf : ∀ x, f x ≠ 0 <;> simp [hf]]
  simp
  ring

theorem nowhereZeroApply_one :
    nowhereZeroApply (fun _ => 1) = ContinuousLinearMap.id ℂ ℂ := by
  ext
  simp [nowhereZeroApply, nowhereZeroScalar]

theorem nowhereZeroApply_not_additive :
    nowhereZeroApply ((fun _ => 1) + (fun _ => (-1 : ℂ))) ≠
      nowhereZeroApply (fun _ => 1) + nowhereZeroApply (fun _ => (-1 : ℂ)) := by
  intro h
  have h1 := congrArg (fun A : ℂ →L[ℂ] ℂ => A 1) h
  norm_num [nowhereZeroApply, nowhereZeroScalar] at h1

theorem nowhereZeroApply_singletons_zero (a : ℝ) :
    nowhereZeroApply (fun x => if x = a then 1 else 0) = 0 := by
  have hnot : ¬ ∀ x : ℝ, x = a := by
    intro h
    have := h (a + 1)
    linarith
  ext
  simp [nowhereZeroApply, nowhereZeroScalar, hnot]

theorem nowhereZeroApply_exp_is_id (t : ℝ) :
    nowhereZeroApply (fun l => Complex.exp ((t : ℂ) * (l : ℂ) * Complex.I)) =
      ContinuousLinearMap.id ℂ ℂ := by
  have hnz : ∀ l : ℝ,
      Complex.exp ((t : ℂ) * (l : ℂ) * Complex.I) ≠ 0 :=
    fun l => Complex.exp_ne_zero _
  ext
  simp [nowhereZeroApply, nowhereZeroScalar, hnz]

theorem nowhereZeroApply_exp_does_not_decay :
    ¬ Filter.Tendsto
      (fun t : ℝ => inner ℂ
        (nowhereZeroApply
          (fun l => Complex.exp ((t : ℂ) * (l : ℂ) * Complex.I)) 1) 1)
      Filter.atTop (nhds 0) := by
  simp [nowhereZeroApply_exp_is_id]

/-- A single concrete map satisfies exactly the first three advertised
`SpectralCalculus` laws and kills every singleton, but its exponential matrix
coefficient is constantly one.  Hence the Wiener field is independent extra
content, not a consequence of the algebraic interface. -/
theorem algebraic_laws_and_atomlessness_do_not_imply_decay :
    (∀ f g : ℝ → ℂ,
      nowhereZeroApply (f * g) = (nowhereZeroApply f).comp (nowhereZeroApply g)) ∧
    (∀ f : ℝ → ℂ,
      nowhereZeroApply (starRingEnd ℂ ∘ f) = (nowhereZeroApply f)†) ∧
    nowhereZeroApply (fun _ => 1) = ContinuousLinearMap.id ℂ ℂ ∧
    (∀ a : ℝ, nowhereZeroApply (fun x => if x = a then 1 else 0) = 0) ∧
    ¬ Filter.Tendsto
      (fun t : ℝ => inner ℂ
        (nowhereZeroApply
          (fun l => Complex.exp ((t : ℂ) * (l : ℂ) * Complex.I)) 1) 1)
      Filter.atTop (nhds 0) := by
  exact ⟨nowhereZeroApply_mul, nowhereZeroApply_star, nowhereZeroApply_one,
    nowhereZeroApply_singletons_zero, nowhereZeroApply_exp_does_not_decay⟩

/-! ## The algebraic positivity lemma itself is sound -/

theorem star_mul_quadratic_eq_norm_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {D : UnboundedOperator H} {hD : D.IsSelfAdjoint}
    (sc : SpectralCalculus H D hD) (g : ℝ → ℂ) (x : H) :
    re (inner ℂ (sc.apply ((starRingEnd ℂ ∘ g) * g) x) x) =
      ‖sc.apply g x‖ ^ 2 := by
  rw [sc.apply_mul, sc.apply_star, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq]

/-! ## `operatorTrace` is not a trace without summability -/

noncomputable def natHilbertBasis : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ) := default

theorem identity_diagonal_not_summable :
    ¬ Summable (fun i : ℕ => re (inner ℂ
      ((ContinuousLinearMap.id ℂ ℓ²(ℕ, ℂ)) (natHilbertBasis i))
      (natHilbertBasis i))) := by
  have hterm :
      (fun i : ℕ => re (inner ℂ
        ((ContinuousLinearMap.id ℂ ℓ²(ℕ, ℂ)) (natHilbertBasis i))
        (natHilbertBasis i))) = fun _ : ℕ => (1 : ℝ) := by
    funext i
    simp only [ContinuousLinearMap.id_apply]
    rw [orthonormal_iff_ite.mp natHilbertBasis.orthonormal i i]
    simp
  rw [hterm]
  intro hs
  exact one_ne_zero ((summable_const_iff (1 : ℝ)).mp hs)

theorem operatorTrace_id_infinite_eq_zero :
    operatorTrace (ContinuousLinearMap.id ℂ ℓ²(ℕ, ℂ)) natHilbertBasis = 0 := by
  unfold operatorTrace
  have hterm :
      (fun i : ℕ => re (inner ℂ
        ((ContinuousLinearMap.id ℂ ℓ²(ℕ, ℂ)) (natHilbertBasis i))
        (natHilbertBasis i))) = fun _ : ℕ => (1 : ℝ) := by
    funext i
    simp only [ContinuousLinearMap.id_apply]
    rw [orthonormal_iff_ite.mp natHilbertBasis.orthonormal i i]
    simp
  rw [hterm]
  exact tsum_eq_zero_of_not_summable (by
    simpa only [hterm] using identity_diagonal_not_summable)

/-! ## Pointwise squares are not analytic autocorrelations -/

theorem analytic_autocorrelation_need_not_be_pointwise_square :
    ∃ f : ℝ → ℝ, Analysis.IsAutocorrelation f ∧
      ¬ ∃ g : ℝ → ℂ,
        ∀ t, (f t : ℂ) = (starRingEnd ℂ (g t)) * g t := by
  obtain ⟨f, hf, hf1⟩ := Analysis.exists_autocorrelation_with_negative_value
  refine ⟨f, hf, ?_⟩
  rintro ⟨g, hg⟩
  have hgre := congrArg re (hg 1)
  norm_num [hf1] at hgre
  nlinarith [sq_nonneg (g 1).re, sq_nonneg (g 1).im]

#print axioms multiplicationOperator_isSelfAdjoint
#print axioms evaluationAtZero_apply_independent_of_operator
#print axioms evaluationAtZero_does_not_recover_operator
#print axioms evaluationAtZero_atomless_premise_false
#print axioms nowhereZeroApply_mul
#print axioms nowhereZeroApply_star
#print axioms nowhereZeroApply_one
#print axioms nowhereZeroApply_not_additive
#print axioms nowhereZeroApply_singletons_zero
#print axioms nowhereZeroApply_exp_is_id
#print axioms nowhereZeroApply_exp_does_not_decay
#print axioms algebraic_laws_and_atomlessness_do_not_imply_decay
#print axioms star_mul_quadratic_eq_norm_sq
#print axioms identity_diagonal_not_summable
#print axioms operatorTrace_id_infinite_eq_zero
#print axioms analytic_autocorrelation_need_not_be_pointwise_square
#print axioms ArithmeticHodge.Spectral.spectralCalculus_exists
#print axioms ArithmeticHodge.Spectral.apply_star_mul_self_nonneg
#print axioms ArithmeticHodge.Spectral.apply_autocorrelation_positive
#print axioms ArithmeticHodge.Spectral.trace_nonneg_of_autocorrelation
#print axioms ArithmeticHodge.Spectral.trace_nonneg_of_real_autocorrelation

end ArithmeticHodge.Spectral.SpectralCalculusAudit
