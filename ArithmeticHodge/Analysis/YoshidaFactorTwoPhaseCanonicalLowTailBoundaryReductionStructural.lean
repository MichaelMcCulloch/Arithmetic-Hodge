import ArithmeticHodge.Analysis.CoerciveBilinearSchurConcavity
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailCorrectionEnergyStructural

set_option autoImplicit false

open Matrix Real
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailBoundaryReductionStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionEnergyStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural
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
# Reduction of the canonical Schur certificate to the phase circle

The finite low block, completed tail form, and completed mixed functionals
are affine in the phase.  Hence their corrected Gram is Loewner-concave.
Every point of the closed phase disk lies on the vertical chord joining
`(a, -sqrt (1-a^2))` to `(a, sqrt (1-a^2))`.  Positivity at those two circle
points therefore implies positivity at the original disk point.
-/

/-- The canonical finite-low matrix is affine along every vertical phase
segment. -/
theorem canonicalPhaseLowMatrix_vertical_convexCombination
    (a b₀ b₁ b t : ℝ)
    (hb : b = (1 - t) * b₀ + t * b₁)
    (i j : FactorTwoPhaseLowIndex) :
    canonicalPhaseLowMatrix a b i j =
      (1 - t) * canonicalPhaseLowMatrix a b₀ i j +
        t * canonicalPhaseLowMatrix a b₁ i j := by
  rw [hb]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [canonicalPhaseLowMatrix, factorTwoFiniteLowPhaseMatrix,
      factorTwoPhaseBlockMatrix] <;> ring

/-- The completed canonical tail form is affine along every vertical phase
segment. -/
theorem completedCanonicalPhaseTailBilinear_vertical_convexCombination
    (a b₀ b₁ b t : ℝ)
    (h₀ : a ^ 2 + b₀ ^ 2 ≤ 1)
    (h₁ : a ^ 2 + b₁ ^ 2 ≤ 1)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hb : b = (1 - t) * b₀ + t * b₁)
    (x y : CanonicalPhaseTailCompletion) :
    completedCanonicalPhaseTailBilinear a b hphase x y =
      (1 - t) * completedCanonicalPhaseTailBilinear a b₀ h₀ x y +
        t * completedCanonicalPhaseTailBilinear a b₁ h₁ x y := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro y
  simp only [completedCanonicalPhaseTailBilinear_coe_coe]
  rw [hb]
  unfold canonicalPhaseTailCoreBilinearValue
    factorTwoEndpointLowTailMixed
  ring

/-- Each completed real low--tail functional is affine along every vertical
phase segment. -/
theorem completedCanonicalPhaseLowBasisTailRealFunctional_vertical_convexCombination
    (k : FactorTwoPhaseLowIndex) (a b₀ b₁ b t : ℝ)
    (h₀ : a ^ 2 + b₀ ^ 2 ≤ 1)
    (h₁ : a ^ 2 + b₁ ^ 2 ≤ 1)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hb : b = (1 - t) * b₀ + t * b₁)
    (z : CanonicalPhaseTailCompletion) :
    completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase z =
      (1 - t) *
          completedCanonicalPhaseLowBasisTailRealFunctional k a b₀ h₀ z +
        t * completedCanonicalPhaseLowBasisTailRealFunctional
          k a b₁ h₁ z := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x
  simp only [completedCanonicalPhaseLowBasisTailRealFunctional_coe]
  rw [hb]
  unfold canonicalPhaseLowBasisTailRealMixedValue
    factorTwoEndpointLowTailMixed
  ring

/-- The reduced canonical corrected Gram is Hermitian at every disk phase. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_isHermitian
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    (completedCanonicalPhaseLowTailRealCorrectedGram
      a b hphase).IsHermitian := by
  change (coerciveBilinearCorrectedGram
    (canonicalPhaseLowMatrix a b)
    (completedCanonicalPhaseTailBilinear a b hphase)
    (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
    (fun k ↦ completedCanonicalPhaseLowBasisTailRealFunctional
      k a b hphase)).IsHermitian
  exact coerciveBilinearCorrectedGram_isHermitian
    (canonicalPhaseLowMatrix a b)
    (completedCanonicalPhaseTailBilinear a b hphase)
    (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
    (fun k ↦ completedCanonicalPhaseLowBasisTailRealFunctional
      k a b hphase)
    (canonicalPhaseLowMatrix_isHermitian a b)
    (completedCanonicalPhaseTailBilinear_symm a b hphase)

/-- Circle positivity is sufficient for the canonical corrected Gram on the
whole closed phase disk.  The `sqrt (1-a^2) = 0` branch is already a circle
point; the nondegenerate branch follows from weighted Schur concavity on its
vertical chord. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_disk_posSemidef_of_circle
    (hcircle : ∀ (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1),
      a ^ 2 + b ^ 2 = 1 →
        Matrix.PosSemidef
          (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase))
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    Matrix.PosSemidef
      (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) := by
  let s : ℝ := Real.sqrt (1 - a ^ 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsSq : s ^ 2 = 1 - a ^ 2 := by
    dsimp only [s]
    rw [Real.sq_sqrt]
    nlinarith [sq_nonneg b]
  by_cases hsZero : s = 0
  · have hbZero : b = 0 := by
      nlinarith [sq_nonneg b]
    apply hcircle a b hphase
    nlinarith
  · have hsPos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hsZero)
    let t : ℝ := (b + s) / (2 * s)
    have hbLower : -s ≤ b := by
      by_contra h
      have hb : b < -s := lt_of_not_ge h
      nlinarith [sq_nonneg (b + s)]
    have hbUpper : b ≤ s := by
      by_contra h
      have hb : s < b := lt_of_not_ge h
      nlinarith [sq_nonneg (b - s)]
    have ht0 : 0 ≤ t := by
      dsimp only [t]
      exact div_nonneg (by linarith) (by positivity)
    have ht1 : t ≤ 1 := by
      dsimp only [t]
      apply (div_le_one (by positivity : 0 < 2 * s)).2
      linarith
    have hbary : b = (1 - t) * (-s) + t * s := by
      dsimp only [t]
      field_simp
      ring
    have hminusEq : a ^ 2 + (-s) ^ 2 = 1 := by
      nlinarith
    have hplusEq : a ^ 2 + s ^ 2 = 1 := by
      nlinarith
    have hminus : a ^ 2 + (-s) ^ 2 ≤ 1 := hminusEq.le
    have hplus : a ^ 2 + s ^ 2 ≤ 1 := hplusEq.le
    have hminusPSD := hcircle a (-s) hminus hminusEq
    have hplusPSD := hcircle a s hplus hplusEq
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (completedCanonicalPhaseLowTailRealCorrectedGram_isHermitian
        a b hphase)
    intro c
    simp only [star_trivial]
    have hminusNonneg := hminusPSD.dotProduct_mulVec_nonneg c
    have hplusNonneg := hplusPSD.dotProduct_mulVec_nonneg c
    simp only [star_trivial] at hminusNonneg hplusNonneg
    have hweighted :
        0 ≤ (1 - t) *
              (c ⬝ᵥ (completedCanonicalPhaseLowTailRealCorrectedGram
                a (-s) hminus *ᵥ c)) +
            t *
              (c ⬝ᵥ (completedCanonicalPhaseLowTailRealCorrectedGram
                a s hplus *ᵥ c)) :=
      add_nonneg
        (mul_nonneg (sub_nonneg.mpr ht1) hminusNonneg)
        (mul_nonneg ht0 hplusNonneg)
    have hschur := coerciveBilinearCorrectedGram_convexCombination_le
      t
      (canonicalPhaseLowMatrix a (-s))
      (canonicalPhaseLowMatrix a s)
      (canonicalPhaseLowMatrix a b)
      (completedCanonicalPhaseTailBilinear a (-s) hminus)
      (completedCanonicalPhaseTailBilinear a s hplus)
      (completedCanonicalPhaseTailBilinear a b hphase)
      (completedCanonicalPhaseTailBilinear_isCoercive a (-s) hminus)
      (completedCanonicalPhaseTailBilinear_isCoercive a s hplus)
      (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
      (completedCanonicalPhaseTailBilinear_symm a (-s) hminus)
      (completedCanonicalPhaseTailBilinear_symm a s hplus)
      (fun k ↦ completedCanonicalPhaseLowBasisTailRealFunctional
        k a (-s) hminus)
      (fun k ↦ completedCanonicalPhaseLowBasisTailRealFunctional
        k a s hplus)
      (fun k ↦ completedCanonicalPhaseLowBasisTailRealFunctional
        k a b hphase)
      (canonicalPhaseLowMatrix_vertical_convexCombination
        a (-s) s b t hbary)
      (completedCanonicalPhaseTailBilinear_vertical_convexCombination
        a (-s) s b t hminus hplus hphase hbary)
      (fun k ↦
        completedCanonicalPhaseLowBasisTailRealFunctional_vertical_convexCombination
          k a (-s) s b t hminus hplus hphase hbary)
      ht0 ht1 c
    change
      (1 - t) *
            (c ⬝ᵥ (completedCanonicalPhaseLowTailRealCorrectedGram
              a (-s) hminus *ᵥ c)) +
          t *
            (c ⬝ᵥ (completedCanonicalPhaseLowTailRealCorrectedGram
              a s hplus *ᵥ c)) ≤
        c ⬝ᵥ (completedCanonicalPhaseLowTailRealCorrectedGram
          a b hphase *ᵥ c) at hschur
    exact hweighted.trans hschur

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailBoundaryReductionStructural
