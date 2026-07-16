import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailConjugationCompletionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnRieszStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailConjugationRieszStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseCanonicalLowTailConjugationCompletionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
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

/-- Tail conjugation fixes every real-coordinate coercive Riesz
representative. -/
theorem canonicalPhaseTailCompletionConj_realRieszCorrection
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    canonicalPhaseTailCompletionConj
        (canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase) =
      canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase := by
  apply eq_of_completedCanonicalPhaseTailBilinear_apply_eq a b hphase
  intro z
  let r := canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase
  change completedCanonicalPhaseTailBilinear a b hphase
      (canonicalPhaseTailCompletionConj r) z =
    completedCanonicalPhaseTailBilinear a b hphase r z
  calc
    completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseTailCompletionConj r) z =
      completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseTailCompletionConj r)
        (canonicalPhaseTailCompletionConj
          (canonicalPhaseTailCompletionConj z)) := by
      exact congrArg
        (completedCanonicalPhaseTailBilinear a b hphase
          (canonicalPhaseTailCompletionConj r))
        (canonicalPhaseTailCompletionConj_involutive z).symm
    _ = completedCanonicalPhaseTailBilinear a b hphase r
        (canonicalPhaseTailCompletionConj z) :=
      completedCanonicalPhaseTailBilinear_conj_conj a b hphase r
        (canonicalPhaseTailCompletionConj z)
    _ = completedCanonicalPhaseLowBasisTailRealFunctional
        k a b hphase (canonicalPhaseTailCompletionConj z) :=
      completedCanonicalPhaseTailBilinear_realRieszCorrection_apply
        k a b hphase (canonicalPhaseTailCompletionConj z)
    _ = completedCanonicalPhaseLowBasisTailRealFunctional
        k a b hphase z :=
      completedCanonicalPhaseLowBasisTailRealFunctional_conj
        k a b hphase z
    _ = completedCanonicalPhaseTailBilinear a b hphase r z :=
      (completedCanonicalPhaseTailBilinear_realRieszCorrection_apply
        k a b hphase z).symm

/-- Tail conjugation negates every imaginary-coordinate coercive Riesz
representative. -/
theorem canonicalPhaseTailCompletionConj_imagRieszCorrection
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    canonicalPhaseTailCompletionConj
        (canonicalPhaseLowBasisTailImagRieszCorrection k a b hphase) =
      -canonicalPhaseLowBasisTailImagRieszCorrection k a b hphase := by
  apply eq_of_completedCanonicalPhaseTailBilinear_apply_eq a b hphase
  intro z
  let r := canonicalPhaseLowBasisTailImagRieszCorrection k a b hphase
  have hBneg :
      completedCanonicalPhaseTailBilinear a b hphase (-r) z =
        -completedCanonicalPhaseTailBilinear a b hphase r z := by
    have hmap := map_neg
      (completedCanonicalPhaseTailBilinear a b hphase) r
    exact congrArg (fun f : CanonicalPhaseTailCompletion →L[ℝ] ℝ ↦ f z) hmap
  change completedCanonicalPhaseTailBilinear a b hphase
      (canonicalPhaseTailCompletionConj r) z =
    completedCanonicalPhaseTailBilinear a b hphase (-r) z
  calc
    completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseTailCompletionConj r) z =
      completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseTailCompletionConj r)
        (canonicalPhaseTailCompletionConj
          (canonicalPhaseTailCompletionConj z)) := by
      exact congrArg
        (completedCanonicalPhaseTailBilinear a b hphase
          (canonicalPhaseTailCompletionConj r))
        (canonicalPhaseTailCompletionConj_involutive z).symm
    _ = completedCanonicalPhaseTailBilinear a b hphase r
        (canonicalPhaseTailCompletionConj z) :=
      completedCanonicalPhaseTailBilinear_conj_conj a b hphase r
        (canonicalPhaseTailCompletionConj z)
    _ = completedCanonicalPhaseLowBasisTailImagFunctional
        k a b hphase (canonicalPhaseTailCompletionConj z) :=
      completedCanonicalPhaseTailBilinear_imagRieszCorrection_apply
        k a b hphase (canonicalPhaseTailCompletionConj z)
    _ = -completedCanonicalPhaseLowBasisTailImagFunctional
        k a b hphase z :=
      completedCanonicalPhaseLowBasisTailImagFunctional_conj
        k a b hphase z
    _ = -completedCanonicalPhaseTailBilinear a b hphase r z := by
      exact congrArg Neg.neg
        (completedCanonicalPhaseTailBilinear_imagRieszCorrection_apply
          k a b hphase z).symm
    _ = completedCanonicalPhaseTailBilinear a b hphase (-r) z :=
      hBneg.symm

/-- The real and imaginary Riesz correction sectors are exactly orthogonal
for every disk phase and every pair of low indices. -/
theorem completedCanonicalPhaseTailBilinear_realRiesz_imagRiesz_eq_zero
    (k l : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase)
        (canonicalPhaseLowBasisTailImagRieszCorrection l a b hphase) = 0 := by
  let rR := canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase
  let rI := canonicalPhaseLowBasisTailImagRieszCorrection l a b hphase
  have hfix : canonicalPhaseTailCompletionConj rR = rR :=
    canonicalPhaseTailCompletionConj_realRieszCorrection k a b hphase
  have hanti : canonicalPhaseTailCompletionConj rI = -rI :=
    canonicalPhaseTailCompletionConj_imagRieszCorrection l a b hphase
  have hneg :
      completedCanonicalPhaseTailBilinear a b hphase rR (-rI) =
        -completedCanonicalPhaseTailBilinear a b hphase rR rI :=
    map_neg (completedCanonicalPhaseTailBilinear a b hphase rR) rI
  have hinv := completedCanonicalPhaseTailBilinear_conj_conj
    a b hphase rR rI
  have heq :
      completedCanonicalPhaseTailBilinear a b hphase rR rI =
        -completedCanonicalPhaseTailBilinear a b hphase rR rI := by
    calc
      completedCanonicalPhaseTailBilinear a b hphase rR rI =
          completedCanonicalPhaseTailBilinear a b hphase
            (canonicalPhaseTailCompletionConj rR)
            (canonicalPhaseTailCompletionConj rI) := hinv.symm
      _ = completedCanonicalPhaseTailBilinear a b hphase rR
          (canonicalPhaseTailCompletionConj rI) := by
        exact congrArg
          (fun x ↦ completedCanonicalPhaseTailBilinear a b hphase x
            (canonicalPhaseTailCompletionConj rI)) hfix
      _ = completedCanonicalPhaseTailBilinear a b hphase rR (-rI) := by
        exact congrArg (completedCanonicalPhaseTailBilinear a b hphase rR) hanti
      _ = -completedCanonicalPhaseTailBilinear a b hphase rR rI := hneg
  linarith

/-- Orthogonality in the reverse order follows from symmetry of the completed
tail form. -/
theorem completedCanonicalPhaseTailBilinear_imagRiesz_realRiesz_eq_zero
    (k l : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseLowBasisTailImagRieszCorrection k a b hphase)
        (canonicalPhaseLowBasisTailRealRieszCorrection l a b hphase) = 0 := by
  rw [completedCanonicalPhaseTailBilinear_symm]
  exact completedCanonicalPhaseTailBilinear_realRiesz_imagRiesz_eq_zero
    l k a b hphase

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailConjugationRieszStructural
