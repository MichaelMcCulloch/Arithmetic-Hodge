import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnCompletionStructural

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnRieszStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnCompletionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailRieszStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseLowSchur

local instance : InnerProductSpace ℝ CanonicalPhaseTailCore :=
  InnerProductSpace.rclikeToReal ℂ CanonicalPhaseTailCore

private theorem eq_of_completedCanonicalPhaseTailBilinear_apply_eq
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    {x y : CanonicalPhaseTailCompletion}
    (h : ∀ z, completedCanonicalPhaseTailBilinear a b hphase x z =
      completedCanonicalPhaseTailBilinear a b hphase y z) :
    x = y := by
  let hB := completedCanonicalPhaseTailBilinear_isCoercive a b hphase
  apply hB.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro z
  rw [hB.continuousLinearEquivOfBilin_apply,
    hB.continuousLinearEquivOfBilin_apply]
  exact h z

/-- The imaginary-coordinate Riesz correction is the quarter turn of the
real-coordinate correction. -/
theorem canonicalPhaseLowBasisTailImagRieszCorrection_eq_I_smul_real
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    canonicalPhaseLowBasisTailImagRieszCorrection k a b hphase =
      Complex.I •
        canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase := by
  apply eq_of_completedCanonicalPhaseTailBilinear_apply_eq a b hphase
  intro z
  symm
  calc
    completedCanonicalPhaseTailBilinear a b hphase
        (Complex.I •
          canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase) z =
      -completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase)
        (Complex.I • z) :=
      completedCanonicalPhaseTailBilinear_I_smul_left a b hphase
        (canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase) z
    _ = -completedCanonicalPhaseLowBasisTailRealFunctional
        k a b hphase (Complex.I • z) := by
      exact congrArg Neg.neg
        (completedCanonicalPhaseTailBilinear_realRieszCorrection_apply
          k a b hphase (Complex.I • z))
    _ = -(-completedCanonicalPhaseLowBasisTailImagFunctional
        k a b hphase z) := by
      exact congrArg Neg.neg
        (completedCanonicalPhaseLowBasisTailRealFunctional_I_smul
          k a b hphase z)
    _ = completedCanonicalPhaseLowBasisTailImagFunctional
        k a b hphase z := neg_neg _
    _ = completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseLowBasisTailImagRieszCorrection k a b hphase) z :=
      (completedCanonicalPhaseTailBilinear_imagRieszCorrection_apply
        k a b hphase z).symm

/-- Quarter-turn symmetry identifies the imaginary--imaginary correction
pairing with the corresponding real--real pairing. -/
theorem completedCanonicalPhaseTailBilinear_imagRiesz_imagRiesz
    (k l : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseLowBasisTailImagRieszCorrection k a b hphase)
        (canonicalPhaseLowBasisTailImagRieszCorrection l a b hphase) =
      completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase)
        (canonicalPhaseLowBasisTailRealRieszCorrection l a b hphase) := by
  let rRk := canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase
  let rRl := canonicalPhaseLowBasisTailRealRieszCorrection l a b hphase
  let rIk := canonicalPhaseLowBasisTailImagRieszCorrection k a b hphase
  let rIl := canonicalPhaseLowBasisTailImagRieszCorrection l a b hphase
  have hk : rIk = Complex.I • rRk :=
    canonicalPhaseLowBasisTailImagRieszCorrection_eq_I_smul_real
      k a b hphase
  have hl : rIl = Complex.I • rRl :=
    canonicalPhaseLowBasisTailImagRieszCorrection_eq_I_smul_real
      l a b hphase
  change completedCanonicalPhaseTailBilinear a b hphase rIk rIl =
    completedCanonicalPhaseTailBilinear a b hphase rRk rRl
  calc
    completedCanonicalPhaseTailBilinear a b hphase rIk rIl =
      completedCanonicalPhaseTailBilinear a b hphase
        (Complex.I • rRk) rIl := by
      exact congrArg
        (fun x ↦ completedCanonicalPhaseTailBilinear a b hphase x rIl) hk
    _ = completedCanonicalPhaseTailBilinear a b hphase
        (Complex.I • rRk) (Complex.I • rRl) := by
      exact congrArg
        (completedCanonicalPhaseTailBilinear a b hphase (Complex.I • rRk)) hl
    _ = completedCanonicalPhaseTailBilinear a b hphase rRk rRl :=
      completedCanonicalPhaseTailBilinear_I_smul_I_smul
        a b hphase rRk rRl

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnRieszStructural
