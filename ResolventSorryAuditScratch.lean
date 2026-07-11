import ArithmeticHodge.Spectral.ResolventComputation

open scoped InnerProductSpace InnerProduct
open RCLike

namespace ArithmeticHodge.Spectral.ResolventSorryAudit

/-!
This scratch file audits the two unresolved statements in
`Spectral/ResolventComputation.lean` without using the inconsistency of the
current `AdeleClassSpaceData` interface.
-/

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

noncomputable def scalarOperator (z : ℂ) : ℂ →L[ℂ] ℂ :=
  z • ContinuousLinearMap.id ℂ ℂ

noncomputable def evaluationCalculus (a : ℝ) :
    SpectralCalculus ℂ (multiplicationOperator a)
      (multiplicationOperator_isSelfAdjoint a) where
  apply f := scalarOperator (f a)
  apply_mul f g := by
    ext
    simp [scalarOperator, Pi.mul_apply, mul_comm]
  apply_star f := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
    intro x y
    simp [scalarOperator]
    ring
  apply_one := by
    ext
    simp [scalarOperator]
  apply_exp_tendsto hatom := by
    exfalso
    have h := hatom a
    have h1 := congrArg (fun A : ℂ →L[ℂ] ℂ => A 1) h
    simp [scalarOperator] at h1

theorem evaluationCalculus_not_spectralGap (a : ℝ) :
    ¬ SpectralGap (evaluationCalculus a) := by
  intro hgap
  have h := hgap a
  have h1 := congrArg (fun A : ℂ →L[ℂ] ℂ => A 1) h
  simp [evaluationCalculus, scalarOperator] at h1

/-- The number-theoretic PNT premise is true while an unrelated valid spectral
calculus can have an atom.  This is the missing-link counterexample for Step A;
it does not construct or use `AdeleClassSpaceData`. -/
theorem pnt_holds_but_evaluation_calculus_has_an_atom (a : ℝ) :
    (∀ s : ℂ, 1 ≤ s.re → riemannZeta s ≠ 0) ∧
      ¬ SpectralGap (evaluationCalculus a) := by
  exact ⟨fun s hs => riemannZeta_ne_zero_of_one_le_re hs,
    evaluationCalculus_not_spectralGap a⟩

/-! ## Audit of `mixing_controls_boundary` -/

/-- The claimed `O(1 / Λ)` conclusion has a Λ-independent left side, so it
is equivalent to exact equality. -/
def VanishingBoundaryBound (traceVal weilVal : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 0 < Λ → ‖traceVal - weilVal‖ ≤ C / Λ

theorem vanishingBoundaryBound_iff_eq (traceVal weilVal : ℝ) :
    VanishingBoundaryBound traceVal weilVal ↔ traceVal = weilVal := by
  constructor
  · exact trace_eq_weil_of_boundary_control traceVal weilVal
  · intro h
    refine ⟨1, zero_lt_one, fun Λ hΛ => ?_⟩
    simp [h, le_of_lt hΛ]

/-- Because the measure in the premise is unconstrained, the stated mixing
hypothesis can always be witnessed by the zero measure, for every flow. -/
theorem mixing_zero_measure {X : Type*} [MeasurableSpace X] (sigma : ℝ → X → X) :
    Mixing sigma (0 : MeasureTheory.Measure X) := by
  intro f g hf hg
  simp

noncomputable def complexHilbertBasis : HilbertBasis Unit ℂ ℂ :=
  (OrthonormalBasis.singleton Unit ℂ).toHilbertBasis

theorem complexHilbertBasis_apply (i : Unit) : complexHilbertBasis i = 1 := by
  simp [complexHilbertBasis]

theorem operatorTrace_evaluationCalculus (a : ℝ) (f : ℝ → ℂ) :
    operatorTrace ((evaluationCalculus a).apply f) complexHilbertBasis = (f a).re := by
  simp [operatorTrace, evaluationCalculus, scalarOperator, complexHilbertBasis]

/-- A simple continuous function satisfying exactly the production decay
hypothesis, with distinct values at 0 and 1. -/
noncomputable def testFunction (t : ℝ) : ℝ := 1 / (1 + t ^ 2)

theorem testFunction_continuous : Continuous testFunction := by
  unfold testFunction
  refine continuous_const.div ?_ (fun x => ?_)
  · fun_prop
  · positivity

theorem testFunction_decay (x : ℝ) :
    ‖testFunction x‖ ≤ 1 / (1 + x ^ 2) := by
  rw [Real.norm_eq_abs, abs_of_pos (by unfold testFunction; positivity)]
  exact le_rfl

theorem evaluation_traces_ne :
    operatorTrace ((evaluationCalculus 0).apply (fun t => (testFunction t : ℂ)))
        complexHilbertBasis ≠
      operatorTrace ((evaluationCalculus 1).apply (fun t => (testFunction t : ℂ)))
        complexHilbertBasis := by
  rw [operatorTrace_evaluationCalculus, operatorTrace_evaluationCalculus]
  norm_num [testFunction]

/-- No fixed value can satisfy the claimed vanishing boundary estimate for
both perfectly valid evaluation calculi.  Thus mixing of an unrelated
measure-space flow cannot imply the production conclusion uniformly in `sc`.
This argument does not use `AdeleClassSpaceData`. -/
theorem evaluation_calculi_cannot_both_match_weil :
    ¬ (VanishingBoundaryBound
          (operatorTrace
            ((evaluationCalculus 0).apply (fun t => (testFunction t : ℂ)))
            complexHilbertBasis)
          (Analysis.weilFunctionalFull testFunction (Analysis.fourierCos testFunction)) ∧
       VanishingBoundaryBound
          (operatorTrace
            ((evaluationCalculus 1).apply (fun t => (testFunction t : ℂ)))
            complexHilbertBasis)
          (Analysis.weilFunctionalFull testFunction (Analysis.fourierCos testFunction))) := by
  rintro ⟨hzero, hone⟩
  have hzero' := (vanishingBoundaryBound_iff_eq _ _).1 hzero
  have hone' := (vanishingBoundaryBound_iff_eq _ _).1 hone
  exact evaluation_traces_ne (hzero'.trans hone'.symm)

/-- Direct formulation of the Step C failure: even with a fixed mixing flow,
continuity, and the required decay, there is no theorem uniform over unrelated
self-adjoint operators and their genuine one-dimensional spectral calculi. -/
theorem no_boundary_control_from_unrelated_mixing :
    ¬ (∀ (a : ℝ)
        (sc : SpectralCalculus ℂ (multiplicationOperator a)
          (multiplicationOperator_isSelfAdjoint a)),
      Mixing (fun (_ : ℝ) (x : Unit) => x) (0 : MeasureTheory.Measure Unit) →
      VanishingBoundaryBound
        (operatorTrace (sc.apply (fun t => (testFunction t : ℂ))) complexHilbertBasis)
        (Analysis.weilFunctionalFull testFunction (Analysis.fourierCos testFunction))) := by
  intro hall
  have hmix : Mixing (fun (_ : ℝ) (x : Unit) => x)
      (0 : MeasureTheory.Measure Unit) :=
    mixing_zero_measure (fun (_ : ℝ) (x : Unit) => x)
  apply evaluation_calculi_cannot_both_match_weil
  exact ⟨hall 0 (evaluationCalculus 0) hmix,
    hall 1 (evaluationCalculus 1) hmix⟩

/-- Bundled characterization: every analytic/dynamical premise that is local
to Step C can hold while the proposed conclusion still cannot be uniform in
the independently quantified spectral data. -/
theorem stepC_local_assumptions_do_not_control_spectrum :
    Continuous testFunction ∧
    (∀ x : ℝ, ‖testFunction x‖ ≤ 1 / (1 + x ^ 2)) ∧
    Mixing (fun (_ : ℝ) (x : Unit) => x) (0 : MeasureTheory.Measure Unit) ∧
    ¬ (∀ (a : ℝ)
        (sc : SpectralCalculus ℂ (multiplicationOperator a)
          (multiplicationOperator_isSelfAdjoint a)),
      VanishingBoundaryBound
        (operatorTrace (sc.apply (fun t => (testFunction t : ℂ))) complexHilbertBasis)
        (Analysis.weilFunctionalFull testFunction (Analysis.fourierCos testFunction))) := by
  refine ⟨testFunction_continuous, testFunction_decay,
    mixing_zero_measure (fun (_ : ℝ) (x : Unit) => x), ?_⟩
  intro hall
  apply evaluation_calculi_cannot_both_match_weil
  exact ⟨hall 0 (evaluationCalculus 0), hall 1 (evaluationCalculus 1)⟩

#print axioms multiplicationOperator_isSelfAdjoint
#print axioms evaluationCalculus_not_spectralGap
#print axioms pnt_holds_but_evaluation_calculus_has_an_atom
#print axioms vanishingBoundaryBound_iff_eq
#print axioms mixing_zero_measure
#print axioms operatorTrace_evaluationCalculus
#print axioms testFunction_continuous
#print axioms testFunction_decay
#print axioms evaluation_calculi_cannot_both_match_weil
#print axioms no_boundary_control_from_unrelated_mixing
#print axioms stepC_local_assumptions_do_not_control_spectrum

end ArithmeticHodge.Spectral.ResolventSorryAudit
