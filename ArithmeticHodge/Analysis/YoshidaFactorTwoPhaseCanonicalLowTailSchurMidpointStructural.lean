import ArithmeticHodge.Analysis.CoerciveBilinearSchurMidpoint
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailEndpointAdaptedFunctionalStructural

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailSchurMidpointStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionEnergyStructural
open YoshidaFactorTwoPhaseCanonicalLowTailEndpointShearStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailRieszStructural
open YoshidaFactorTwoPhaseCanonicalLowTailSchurStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur

local instance : InnerProductSpace ℝ CanonicalPhaseTailCore :=
  InnerProductSpace.rclikeToReal ℂ CanonicalPhaseTailCore

/-!
# Midpoint curvature of the canonical phase Schur complement

The uneliminated low matrix, tail form, and mixed functional are affine in
the phase.  This module combines those exact identities with coercive Riesz
duality to expose the non-affine part of the corrected Gram.
-/

/-- The canonical finite-low matrix is exactly affine under phase reversal. -/
theorem canonicalPhaseLowMatrix_add_neg_eq_two_zero
    (a b : ℝ) (i j : FactorTwoPhaseLowIndex) :
    canonicalPhaseLowMatrix a b i j +
        canonicalPhaseLowMatrix (-a) (-b) i j =
      2 * canonicalPhaseLowMatrix 0 0 i j := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [canonicalPhaseLowMatrix, factorTwoFiniteLowPhaseMatrix,
      factorTwoPhaseBlockMatrix] <;> ring

/-- The completed canonical tail form is exactly affine under phase
reversal.  The proof is made on the dense core and passed through both
completion variables. -/
theorem completedCanonicalPhaseTailBilinear_add_neg_eq_two_zero
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hneg : (-a) ^ 2 + (-b) ^ 2 ≤ 1)
    (x y : CanonicalPhaseTailCompletion) :
    completedCanonicalPhaseTailBilinear a b hphase x y +
        completedCanonicalPhaseTailBilinear (-a) (-b) hneg x y =
      2 * completedCanonicalPhaseTailBilinear 0 0 (by norm_num) x y := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro y
  simp only [completedCanonicalPhaseTailBilinear_coe_coe]
  unfold canonicalPhaseTailCoreBilinearValue
    factorTwoEndpointLowTailMixed
  ring

/-- Each completed canonical low--tail functional is exactly affine under
phase reversal. -/
theorem completedCanonicalPhaseLowBasisTailRealFunctional_add_neg_eq_two_zero
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hneg : (-a) ^ 2 + (-b) ^ 2 ≤ 1)
    (z : CanonicalPhaseTailCompletion) :
    completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase z +
        completedCanonicalPhaseLowBasisTailRealFunctional
          k (-a) (-b) hneg z =
      2 * completedCanonicalPhaseLowBasisTailRealFunctional
        k 0 0 (by norm_num) z := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x
  simp only [completedCanonicalPhaseLowBasisTailRealFunctional_coe]
  unfold canonicalPhaseLowBasisTailRealMixedValue
    factorTwoEndpointLowTailMixed
  ring

/-- Exact midpoint defect of the canonical corrected Gram.  The right side
is the sum of the two tail energies of the phase-response displacement of
the aggregate Riesz representative. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_midpoint_defect
    (c : FactorTwoPhaseLowIndex → ℝ) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let hneg : (-a) ^ 2 + (-b) ^ 2 ≤ 1 := by nlinarith
    let hzero : (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 ≤ 1 := by norm_num
    let rplus := canonicalPhaseLowTailRealRieszCombination c a b hphase
    let rminus := canonicalPhaseLowTailRealRieszCombination
      c (-a) (-b) hneg
    let rzero := canonicalPhaseLowTailRealRieszCombination c 0 0 hzero
    2 * (c ⬝ᵥ
          (completedCanonicalPhaseLowTailRealCorrectedGram
            0 0 hzero *ᵥ c)) -
        (c ⬝ᵥ
            (completedCanonicalPhaseLowTailRealCorrectedGram
              a b hphase *ᵥ c) +
          c ⬝ᵥ
            (completedCanonicalPhaseLowTailRealCorrectedGram
              (-a) (-b) hneg *ᵥ c)) =
      completedCanonicalPhaseTailBilinear a b hphase
          (rplus - rzero) (rplus - rzero) +
        completedCanonicalPhaseTailBilinear (-a) (-b) hneg
          (rminus - rzero) (rminus - rzero) := by
  dsimp only
  let hneg : (-a) ^ 2 + (-b) ^ 2 ≤ 1 := by nlinarith
  let hzero : (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 ≤ 1 := by norm_num
  have hdefect := coerciveBilinearCorrectedGram_midpoint_defect
    (canonicalPhaseLowMatrix a b)
    (canonicalPhaseLowMatrix (-a) (-b))
    (canonicalPhaseLowMatrix 0 0)
    (completedCanonicalPhaseTailBilinear a b hphase)
    (completedCanonicalPhaseTailBilinear (-a) (-b) hneg)
    (completedCanonicalPhaseTailBilinear 0 0 hzero)
    (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
    (completedCanonicalPhaseTailBilinear_isCoercive (-a) (-b) hneg)
    (completedCanonicalPhaseTailBilinear_isCoercive 0 0 hzero)
    (completedCanonicalPhaseTailBilinear_symm a b hphase)
    (completedCanonicalPhaseTailBilinear_symm (-a) (-b) hneg)
    (fun k ↦ completedCanonicalPhaseLowBasisTailRealFunctional
      k a b hphase)
    (fun k ↦ completedCanonicalPhaseLowBasisTailRealFunctional
      k (-a) (-b) hneg)
    (fun k ↦ completedCanonicalPhaseLowBasisTailRealFunctional
      k 0 0 hzero)
    (canonicalPhaseLowMatrix_add_neg_eq_two_zero a b)
    (completedCanonicalPhaseTailBilinear_add_neg_eq_two_zero
      a b hphase hneg)
    (fun k ↦
      completedCanonicalPhaseLowBasisTailRealFunctional_add_neg_eq_two_zero
        k a b hphase hneg)
    c
  simpa only [completedCanonicalPhaseLowTailRealCorrectedGram,
    coerciveBilinearCorrectedGram,
    canonicalPhaseLowBasisTailRealRieszCorrection,
    canonicalPhaseLowTailRealRieszCombination] using hdefect

/-- The canonical corrected Gram is midpoint-concave along every phase
diameter.  Thus the clean corrected Gram is an upper, not a lower, midpoint
bound for the two opposite nonzero phases. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_phase_pair_le_zero
    (c : FactorTwoPhaseLowIndex → ℝ) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let hneg : (-a) ^ 2 + (-b) ^ 2 ≤ 1 := by nlinarith
    let hzero : (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 ≤ 1 := by norm_num
    c ⬝ᵥ
          (completedCanonicalPhaseLowTailRealCorrectedGram
            a b hphase *ᵥ c) +
        c ⬝ᵥ
          (completedCanonicalPhaseLowTailRealCorrectedGram
            (-a) (-b) hneg *ᵥ c) ≤
      2 * (c ⬝ᵥ
        (completedCanonicalPhaseLowTailRealCorrectedGram
          0 0 hzero *ᵥ c)) := by
  dsimp only
  let hneg : (-a) ^ 2 + (-b) ^ 2 ≤ 1 := by nlinarith
  let hzero : (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 ≤ 1 := by norm_num
  let rplus := canonicalPhaseLowTailRealRieszCombination c a b hphase
  let rminus := canonicalPhaseLowTailRealRieszCombination
    c (-a) (-b) hneg
  let rzero := canonicalPhaseLowTailRealRieszCombination c 0 0 hzero
  have hdefect :=
    completedCanonicalPhaseLowTailRealCorrectedGram_midpoint_defect
      c a b hphase
  dsimp only at hdefect
  obtain ⟨muPlus, hmuPlus, hdiagPlus⟩ :=
    completedCanonicalPhaseTailBilinear_isCoercive a b hphase
  obtain ⟨muMinus, hmuMinus, hdiagMinus⟩ :=
    completedCanonicalPhaseTailBilinear_isCoercive (-a) (-b) hneg
  have hplus : 0 ≤ completedCanonicalPhaseTailBilinear a b hphase
      (rplus - rzero) (rplus - rzero) := by
    exact (mul_nonneg
      (mul_nonneg hmuPlus.le (norm_nonneg _)) (norm_nonneg _)).trans
        (hdiagPlus (rplus - rzero))
  have hminus : 0 ≤ completedCanonicalPhaseTailBilinear (-a) (-b) hneg
      (rminus - rzero) (rminus - rzero) := by
    exact (mul_nonneg
      (mul_nonneg hmuMinus.le (norm_nonneg _)) (norm_nonneg _)).trans
        (hdiagMinus (rminus - rzero))
  dsimp only [rplus, rminus, rzero] at hplus hminus
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailSchurMidpointStructural
