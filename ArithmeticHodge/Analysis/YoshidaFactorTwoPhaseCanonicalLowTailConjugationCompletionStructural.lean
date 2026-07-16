import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailConjugationStructural

set_option autoImplicit false

open Complex Real
open scoped ComplexConjugate

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailConjugationCompletionStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseCanonicalLowTailConjugationStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Conjugation on the completed canonical phase tail

The algebraic conjugation is an additive isometry, hence extends uniquely to
the canonical Hilbert completion.  Density then transports its involutivity,
conjugate-linearity, phase-form invariance, and its action on the two low-tail
coordinate functionals.
-/

/-- Algebraic conjugation, regarded as a bounded additive map into the
canonical completion. -/
def canonicalPhaseTailCoreConjNormedAddGroupHom :
    NormedAddGroupHom CanonicalPhaseTailCore CanonicalPhaseTailCompletion where
  toFun := fun x ↦
    (canonicalPhaseTailCoreConj x : CanonicalPhaseTailCompletion)
  map_add' := fun x y ↦ by
    rw [canonicalPhaseTailCoreConj_add,
      UniformSpace.Completion.coe_add]
  bound' := ⟨1, fun x ↦ by
    simpa only [UniformSpace.Completion.norm_coe,
      norm_canonicalPhaseTailCoreConj, one_mul] using (le_refl ‖x‖)⟩

/-- Continuous conjugation on the completed canonical phase tail. -/
noncomputable def canonicalPhaseTailCompletionConj :
    CanonicalPhaseTailCompletion → CanonicalPhaseTailCompletion :=
  canonicalPhaseTailCoreConjNormedAddGroupHom.extension

@[simp] theorem canonicalPhaseTailCompletionConj_coe
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailCompletionConj
        (x : CanonicalPhaseTailCompletion) =
      (canonicalPhaseTailCoreConj x : CanonicalPhaseTailCompletion) := by
  exact NormedAddGroupHom.extension_coe
    canonicalPhaseTailCoreConjNormedAddGroupHom x

theorem continuous_canonicalPhaseTailCompletionConj :
    Continuous canonicalPhaseTailCompletionConj :=
  canonicalPhaseTailCoreConjNormedAddGroupHom.extension.continuous

@[simp] theorem canonicalPhaseTailCompletionConj_add
    (z w : CanonicalPhaseTailCompletion) :
    canonicalPhaseTailCompletionConj (z + w) =
      canonicalPhaseTailCompletionConj z +
        canonicalPhaseTailCompletionConj w :=
  canonicalPhaseTailCoreConjNormedAddGroupHom.extension.map_add' z w

@[simp] theorem norm_canonicalPhaseTailCompletionConj
    (z : CanonicalPhaseTailCompletion) :
    ‖canonicalPhaseTailCompletionConj z‖ = ‖z‖ := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq
      (continuous_norm.comp continuous_canonicalPhaseTailCompletionConj)
      continuous_norm) ?_
  intro x
  simp only [canonicalPhaseTailCompletionConj_coe,
    UniformSpace.Completion.norm_coe,
    norm_canonicalPhaseTailCoreConj]

/-- Completed conjugation is conjugate-linear over `ℂ`. -/
@[simp] theorem canonicalPhaseTailCompletionConj_smul
    (c : ℂ) (z : CanonicalPhaseTailCompletion) :
    canonicalPhaseTailCompletionConj (c • z) =
      star c • canonicalPhaseTailCompletionConj z := by
  let g := canonicalPhaseTailCoreConjNormedAddGroupHom.extension
  have heq :
      (fun w : CanonicalPhaseTailCompletion ↦ g (c • w)) =
        fun w ↦ star c • g w := by
    apply UniformSpace.Completion.denseRange_coe.equalizer
    · exact g.continuous.comp (continuous_const_smul c)
    · exact (continuous_const_smul (star c)).comp g.continuous
    · funext x
      calc
        g (c • (x : CanonicalPhaseTailCompletion)) =
            g ((c • x : CanonicalPhaseTailCore) :
              CanonicalPhaseTailCompletion) :=
          congrArg (fun u : CanonicalPhaseTailCompletion ↦ g u)
            (UniformSpace.Completion.coe_smul c x).symm
        _ = (canonicalPhaseTailCoreConj (c • x) :
              CanonicalPhaseTailCompletion) :=
          NormedAddGroupHom.extension_coe
            canonicalPhaseTailCoreConjNormedAddGroupHom (c • x)
        _ = ((star c • canonicalPhaseTailCoreConj x :
              CanonicalPhaseTailCore) : CanonicalPhaseTailCompletion) := by
          exact congrArg
            (fun u : CanonicalPhaseTailCore ↦
              (u : CanonicalPhaseTailCompletion))
            (canonicalPhaseTailCoreConj_smul c x)
        _ = star c •
              (canonicalPhaseTailCoreConj x :
                CanonicalPhaseTailCompletion) :=
          UniformSpace.Completion.coe_smul (star c)
            (canonicalPhaseTailCoreConj x)
        _ = star c • g (x : CanonicalPhaseTailCompletion) := by
          exact congrArg
            (fun u : CanonicalPhaseTailCompletion ↦ star c • u)
            (NormedAddGroupHom.extension_coe
              canonicalPhaseTailCoreConjNormedAddGroupHom x).symm
  exact congrFun heq z

/-- Completed conjugation anticommutes with the canonical quarter turn. -/
@[simp] theorem canonicalPhaseTailCompletionConj_I_smul
    (z : CanonicalPhaseTailCompletion) :
    canonicalPhaseTailCompletionConj (Complex.I • z) =
      (-Complex.I) • canonicalPhaseTailCompletionConj z := by
  calc
    canonicalPhaseTailCompletionConj (Complex.I • z) =
        star Complex.I • canonicalPhaseTailCompletionConj z :=
      canonicalPhaseTailCompletionConj_smul Complex.I z
    _ = (-Complex.I) • canonicalPhaseTailCompletionConj z := by
      rw [show star (Complex.I : ℂ) = -Complex.I from Complex.conj_I]

@[simp] theorem canonicalPhaseTailCompletionConj_neg
    (z : CanonicalPhaseTailCompletion) :
    canonicalPhaseTailCompletionConj (-z) =
      -canonicalPhaseTailCompletionConj z := by
  calc
    canonicalPhaseTailCompletionConj (-z) =
        canonicalPhaseTailCompletionConj ((-1 : ℂ) • z) := by
      exact congrArg canonicalPhaseTailCompletionConj
        (neg_one_smul ℂ z).symm
    _ = star (-1 : ℂ) • canonicalPhaseTailCompletionConj z :=
      canonicalPhaseTailCompletionConj_smul (-1 : ℂ) z
    _ = (-1 : ℂ) • canonicalPhaseTailCompletionConj z := by
      rw [star_neg, star_one]
    _ = -canonicalPhaseTailCompletionConj z :=
      neg_one_smul ℂ (canonicalPhaseTailCompletionConj z)

@[simp] theorem canonicalPhaseTailCompletionConj_sub
    (z w : CanonicalPhaseTailCompletion) :
    canonicalPhaseTailCompletionConj (z - w) =
      canonicalPhaseTailCompletionConj z -
        canonicalPhaseTailCompletionConj w := by
  simp only [sub_eq_add_neg, canonicalPhaseTailCompletionConj_add,
    canonicalPhaseTailCompletionConj_neg]

/-- Completed conjugation remains an involution. -/
@[simp] theorem canonicalPhaseTailCompletionConj_involutive
    (z : CanonicalPhaseTailCompletion) :
    canonicalPhaseTailCompletionConj
        (canonicalPhaseTailCompletionConj z) = z := by
  have heq :
      (fun w : CanonicalPhaseTailCompletion ↦
        canonicalPhaseTailCompletionConj
          (canonicalPhaseTailCompletionConj w)) = id := by
    apply UniformSpace.Completion.denseRange_coe.equalizer
    · exact continuous_canonicalPhaseTailCompletionConj.comp
        continuous_canonicalPhaseTailCompletionConj
    · exact continuous_id
    · funext x
      calc
        canonicalPhaseTailCompletionConj
            (canonicalPhaseTailCompletionConj
              (x : CanonicalPhaseTailCompletion)) =
          canonicalPhaseTailCompletionConj
            (canonicalPhaseTailCoreConj x :
              CanonicalPhaseTailCompletion) := by
          exact congrArg canonicalPhaseTailCompletionConj
            (canonicalPhaseTailCompletionConj_coe x)
        _ = (canonicalPhaseTailCoreConj
              (canonicalPhaseTailCoreConj x) :
              CanonicalPhaseTailCompletion) :=
          canonicalPhaseTailCompletionConj_coe
            (canonicalPhaseTailCoreConj x)
        _ = (x : CanonicalPhaseTailCompletion) := by
          exact congrArg
            (fun u : CanonicalPhaseTailCore ↦
              (u : CanonicalPhaseTailCompletion))
            (canonicalPhaseTailCoreConj_involutive x)
        _ = id (x : CanonicalPhaseTailCompletion) := rfl
  exact congrFun heq z

/-- Simultaneous conjugation preserves the completed real phase-tail form. -/
theorem completedCanonicalPhaseTailBilinear_conj_conj
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (z w : CanonicalPhaseTailCompletion) :
    completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseTailCompletionConj z)
        (canonicalPhaseTailCompletionConj w) =
      completedCanonicalPhaseTailBilinear a b hphase z w := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq
      (((completedCanonicalPhaseTailBilinear a b hphase).continuous.comp
        continuous_canonicalPhaseTailCompletionConj).clm_apply
          continuous_const)
      ((completedCanonicalPhaseTailBilinear a b hphase).continuous.clm_apply
        continuous_const)) ?_
  intro x
  refine UniformSpace.Completion.induction_on w
    (isClosed_eq
      ((completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseTailCompletionConj
          (x : CanonicalPhaseTailCompletion))).continuous.comp
            continuous_canonicalPhaseTailCompletionConj)
      (completedCanonicalPhaseTailBilinear a b hphase
        (x : CanonicalPhaseTailCompletion)).continuous) ?_
  intro y
  calc
    completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseTailCompletionConj
          (x : CanonicalPhaseTailCompletion))
        (canonicalPhaseTailCompletionConj
          (y : CanonicalPhaseTailCompletion)) =
      canonicalPhaseTailCoreBilinearValue
        (canonicalPhaseTailCoreConj x)
        (canonicalPhaseTailCoreConj y) a b := by
      simpa only [canonicalPhaseTailCompletionConj_coe] using
        (completedCanonicalPhaseTailBilinear_coe_coe a b hphase
          (canonicalPhaseTailCoreConj x)
          (canonicalPhaseTailCoreConj y))
    _ = canonicalPhaseTailCoreBilinearValue x y a b :=
      canonicalPhaseTailCoreBilinearValue_conj_conj x y a b
    _ = completedCanonicalPhaseTailBilinear a b hphase
        (x : CanonicalPhaseTailCompletion)
        (y : CanonicalPhaseTailCompletion) :=
      (completedCanonicalPhaseTailBilinear_coe_coe a b hphase x y).symm

/-- Completed conjugation fixes the real low-tail functional. -/
theorem completedCanonicalPhaseLowBasisTailRealFunctional_conj
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (z : CanonicalPhaseTailCompletion) :
    completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase
        (canonicalPhaseTailCompletionConj z) =
      completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase z := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq
      ((completedCanonicalPhaseLowBasisTailRealFunctional
        k a b hphase).continuous.comp
          continuous_canonicalPhaseTailCompletionConj)
      (completedCanonicalPhaseLowBasisTailRealFunctional
        k a b hphase).continuous) ?_
  intro x
  calc
    completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase
        (canonicalPhaseTailCompletionConj
          (x : CanonicalPhaseTailCompletion)) =
      canonicalPhaseLowBasisTailRealMixedValue k
        (canonicalPhaseTailCoreConj x) a b := by
      simpa only [canonicalPhaseTailCompletionConj_coe] using
        (completedCanonicalPhaseLowBasisTailRealFunctional_coe
          k a b hphase (canonicalPhaseTailCoreConj x))
    _ = canonicalPhaseLowBasisTailRealMixedValue k x a b :=
      canonicalPhaseLowBasisTailRealMixedValue_conj k x a b
    _ = completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase
        (x : CanonicalPhaseTailCompletion) :=
      (completedCanonicalPhaseLowBasisTailRealFunctional_coe
        k a b hphase x).symm

/-- Completed conjugation negates the imaginary low-tail functional. -/
theorem completedCanonicalPhaseLowBasisTailImagFunctional_conj
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (z : CanonicalPhaseTailCompletion) :
    completedCanonicalPhaseLowBasisTailImagFunctional k a b hphase
        (canonicalPhaseTailCompletionConj z) =
      -completedCanonicalPhaseLowBasisTailImagFunctional k a b hphase z := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq
      ((completedCanonicalPhaseLowBasisTailImagFunctional
        k a b hphase).continuous.comp
          continuous_canonicalPhaseTailCompletionConj)
      (completedCanonicalPhaseLowBasisTailImagFunctional
        k a b hphase).continuous.neg) ?_
  intro x
  calc
    completedCanonicalPhaseLowBasisTailImagFunctional k a b hphase
        (canonicalPhaseTailCompletionConj
          (x : CanonicalPhaseTailCompletion)) =
      canonicalPhaseLowBasisTailImagMixedValue k
        (canonicalPhaseTailCoreConj x) a b := by
      simpa only [canonicalPhaseTailCompletionConj_coe] using
        (completedCanonicalPhaseLowBasisTailImagFunctional_coe
          k a b hphase (canonicalPhaseTailCoreConj x))
    _ = -canonicalPhaseLowBasisTailImagMixedValue k x a b :=
      canonicalPhaseLowBasisTailImagMixedValue_conj k x a b
    _ = -completedCanonicalPhaseLowBasisTailImagFunctional k a b hphase
        (x : CanonicalPhaseTailCompletion) := by
      exact congrArg Neg.neg
        (completedCanonicalPhaseLowBasisTailImagFunctional_coe
          k a b hphase x).symm

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailConjugationCompletionStructural
