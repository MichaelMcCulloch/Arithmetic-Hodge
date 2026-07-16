import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnStructural

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnCompletionStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseLowSchur

/-- Quarter-turn invariance survives passage to the completed tail. -/
theorem completedCanonicalPhaseTailBilinear_I_smul_I_smul
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (z w : CanonicalPhaseTailCompletion) :
  completedCanonicalPhaseTailBilinear a b hphase
        (Complex.I • z) (Complex.I • w) =
      completedCanonicalPhaseTailBilinear a b hphase z w := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq
      (((completedCanonicalPhaseTailBilinear a b hphase).continuous.comp
        (continuous_const_smul Complex.I)).clm_apply continuous_const)
      ((completedCanonicalPhaseTailBilinear a b hphase).continuous.clm_apply
        continuous_const)) ?_
  intro x
  refine UniformSpace.Completion.induction_on w
    (isClosed_eq
      ((completedCanonicalPhaseTailBilinear a b hphase
        (Complex.I • (x : CanonicalPhaseTailCompletion))).continuous.comp
          (continuous_const_smul Complex.I))
      (completedCanonicalPhaseTailBilinear a b hphase
        (x : CanonicalPhaseTailCompletion)).continuous) ?_
  intro y
  calc
    completedCanonicalPhaseTailBilinear a b hphase
        (Complex.I • (x : CanonicalPhaseTailCompletion))
        (Complex.I • (y : CanonicalPhaseTailCompletion)) =
      canonicalPhaseTailCoreBilinearValue
        (Complex.I • x) (Complex.I • y) a b := by
      simpa only [UniformSpace.Completion.coe_smul] using
        (completedCanonicalPhaseTailBilinear_coe_coe
          a b hphase (Complex.I • x) (Complex.I • y))
    _ = canonicalPhaseTailCoreBilinearValue x y a b :=
      canonicalPhaseTailCoreBilinearValue_I_smul_I_smul x y a b
    _ = completedCanonicalPhaseTailBilinear a b hphase
        (x : CanonicalPhaseTailCompletion)
        (y : CanonicalPhaseTailCompletion) :=
      (completedCanonicalPhaseTailBilinear_coe_coe
        a b hphase x y).symm

/-- Multiplication by `i` remains skew-adjoint for the completed real
bilinear form. -/
theorem completedCanonicalPhaseTailBilinear_I_smul_left
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (z w : CanonicalPhaseTailCompletion) :
    completedCanonicalPhaseTailBilinear a b hphase (Complex.I • z) w =
      -completedCanonicalPhaseTailBilinear a b hphase z (Complex.I • w) := by
  have hrotate : Complex.I • -(Complex.I • w) = w := by
    calc
      Complex.I • -(Complex.I • w) =
          -(Complex.I • (Complex.I • w)) :=
        smul_neg Complex.I (Complex.I • w)
      _ = -((Complex.I * Complex.I) • w) := by rw [smul_smul]
      _ = w := by rw [Complex.I_mul_I, neg_one_smul ℂ w, neg_neg]
  calc
    completedCanonicalPhaseTailBilinear a b hphase
        (Complex.I • z) w =
      completedCanonicalPhaseTailBilinear a b hphase
        (Complex.I • z) (Complex.I • -(Complex.I • w)) := by
      exact congrArg
        (completedCanonicalPhaseTailBilinear a b hphase (Complex.I • z))
        hrotate.symm
    _ = completedCanonicalPhaseTailBilinear a b hphase
        z (-(Complex.I • w)) :=
      completedCanonicalPhaseTailBilinear_I_smul_I_smul
        a b hphase z (-(Complex.I • w))
    _ = -completedCanonicalPhaseTailBilinear a b hphase
        z (Complex.I • w) :=
      map_neg (completedCanonicalPhaseTailBilinear a b hphase z)
        (Complex.I • w)

/-- The completed real low-tail functional rotates to minus the imaginary
functional. -/
theorem completedCanonicalPhaseLowBasisTailRealFunctional_I_smul
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (z : CanonicalPhaseTailCompletion) :
  completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase
        (Complex.I • z) =
      -completedCanonicalPhaseLowBasisTailImagFunctional k a b hphase z := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq
      ((completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase).continuous.comp
        (continuous_const_smul Complex.I))
      (completedCanonicalPhaseLowBasisTailImagFunctional k a b hphase).continuous.neg) ?_
  intro x
  rw [← UniformSpace.Completion.coe_smul,
    completedCanonicalPhaseLowBasisTailRealFunctional_coe,
    completedCanonicalPhaseLowBasisTailImagFunctional_coe,
    canonicalPhaseLowBasisTailRealMixedValue_I_smul]

/-- The completed imaginary low-tail functional rotates to the real
functional. -/
theorem completedCanonicalPhaseLowBasisTailImagFunctional_I_smul
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (z : CanonicalPhaseTailCompletion) :
  completedCanonicalPhaseLowBasisTailImagFunctional k a b hphase
        (Complex.I • z) =
      completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase z := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq
      ((completedCanonicalPhaseLowBasisTailImagFunctional k a b hphase).continuous.comp
        (continuous_const_smul Complex.I))
      (completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase).continuous) ?_
  intro x
  rw [← UniformSpace.Completion.coe_smul,
    completedCanonicalPhaseLowBasisTailImagFunctional_coe,
    completedCanonicalPhaseLowBasisTailRealFunctional_coe,
    canonicalPhaseLowBasisTailImagMixedValue_I_smul]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnCompletionStructural
