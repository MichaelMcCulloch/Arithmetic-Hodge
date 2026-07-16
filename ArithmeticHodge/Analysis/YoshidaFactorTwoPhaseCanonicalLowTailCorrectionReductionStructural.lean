import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailConjugationRieszStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnRieszStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailSchurStructural

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyClosureStructural
open YoshidaFactorTwoPhaseCanonicalLowTailConjugationRieszStructural
open YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnRieszStructural
open YoshidaFactorTwoPhaseCanonicalLowTailRieszStructural
open YoshidaFactorTwoPhaseCanonicalLowTailSchurStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseLowSchur

local instance : InnerProductSpace ℝ CanonicalPhaseTailCore :=
  InnerProductSpace.rclikeToReal ℂ CanonicalPhaseTailCore

/-- The single real `210 × 210` Schur block after quotienting the exact
real--imaginary symmetry. -/
def completedCanonicalPhaseLowTailRealCorrectedGram
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ :=
  fun k l ↦ canonicalPhaseLowMatrix a b k l -
    completedCanonicalPhaseTailBilinear a b hphase
      (canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase)
      (canonicalPhaseLowBasisTailRealRieszCorrection l a b hphase)

private theorem duplicatePhaseLowMatrix_eq_fromBlocks
    (A : Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ) :
    duplicatePhaseLowMatrix A = Matrix.fromBlocks A 0 0 A := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

private theorem duplicatePhaseLowMatrix_isHermitian
    (A : Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ)
    (hA : A.IsHermitian) :
    (duplicatePhaseLowMatrix A).IsHermitian := by
  rw [duplicatePhaseLowMatrix_eq_fromBlocks A]
  exact Matrix.IsHermitian.fromBlocks hA (by simp) hA

/-- The quadratic form of a duplicated low matrix is the sum of its real and
imaginary coordinate quadratics. -/
theorem duplicatePhaseLowMatrix_quadratic
    (A : Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ)
    (d : CanonicalPhaseLowRealImagIndex → ℝ) :
    d ⬝ᵥ (duplicatePhaseLowMatrix A *ᵥ d) =
      (d ∘ Sum.inl) ⬝ᵥ (A *ᵥ (d ∘ Sum.inl)) +
      (d ∘ Sum.inr) ⬝ᵥ (A *ᵥ (d ∘ Sum.inr)) := by
  classical
  simp only [dotProduct, mulVec, duplicatePhaseLowMatrix]
  simp_rw [Fintype.sum_sum_type]
  simp only [Function.comp_apply, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add]

/-- Positivity of one real low block implies positivity of its exact duplicated
real--imaginary block. -/
theorem duplicatePhaseLowMatrix_posSemidef
    (A : Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ)
    (hA : A.PosSemidef) :
    (duplicatePhaseLowMatrix A).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (duplicatePhaseLowMatrix_isHermitian A hA.1)
  intro d
  have hR := hA.dotProduct_mulVec_nonneg (d ∘ Sum.inl)
  have hI := hA.dotProduct_mulVec_nonneg (d ∘ Sum.inr)
  simp only [star_trivial] at hR hI ⊢
  rw [duplicatePhaseLowMatrix_quadratic]
  exact add_nonneg hR hI

/-- The honest `420 × 420` corrected Gram is exactly two copies of the
single real corrected Gram.  Quarter-turn symmetry identifies the diagonal
blocks and conjugation kills both cross blocks. -/
theorem completedCanonicalPhaseLowTailCorrectedGram_eq_duplicate
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    completedCanonicalPhaseLowTailCorrectedGram a b hphase =
      duplicatePhaseLowMatrix
        (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) := by
  ext p q
  rw [completedCanonicalPhaseLowTailCorrectedGram,
    coerciveBilinearCorrectedGram,
    ← canonicalPhaseLowRealImagRieszCorrection_eq_coercive
      a b hphase p,
    ← canonicalPhaseLowRealImagRieszCorrection_eq_coercive
      a b hphase q]
  rcases p with k | k <;> rcases q with l | l
  · rfl
  · simp only [canonicalPhaseLowRealImagMatrix, duplicatePhaseLowMatrix,
      canonicalPhaseLowRealImagRieszCorrection,
      completedCanonicalPhaseTailBilinear_realRiesz_imagRiesz_eq_zero,
      sub_zero]
  · simp only [canonicalPhaseLowRealImagMatrix, duplicatePhaseLowMatrix,
      canonicalPhaseLowRealImagRieszCorrection,
      completedCanonicalPhaseTailBilinear_imagRiesz_realRiesz_eq_zero,
      sub_zero]
  · simp only [canonicalPhaseLowRealImagMatrix, duplicatePhaseLowMatrix,
      canonicalPhaseLowRealImagRieszCorrection,
      completedCanonicalPhaseLowTailRealCorrectedGram]
    exact congrArg (fun t ↦ canonicalPhaseLowMatrix a b k l - t)
      (completedCanonicalPhaseTailBilinear_imagRiesz_imagRiesz
        k l a b hphase)

/-- A positive-semidefinite certificate for the reduced `210 × 210` block
is sufficient for the honest `420 × 420` Schur complement. -/
theorem completedCanonicalPhaseLowTailCorrectedGram_posSemidef_of_real
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hreal : Matrix.PosSemidef
      (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase)) :
    Matrix.PosSemidef
      (completedCanonicalPhaseLowTailCorrectedGram a b hphase) := by
  rw [completedCanonicalPhaseLowTailCorrectedGram_eq_duplicate]
  exact duplicatePhaseLowMatrix_posSemidef
    (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) hreal

/-- The reduced `210 × 210` PSD certificate is therefore the exact remaining
finite obligation for nonnegativity of every assembled physical canonical
low-plus-tail profile. -/
theorem canonicalPhasePhysicalLowTailValue_nonneg_of_realCorrectedGram_posSemidef
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hreal : Matrix.PosSemidef
      (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase)) :
    CanonicalPhasePhysicalLowTailNonnegative cReal cImag x a b :=
  canonicalPhasePhysicalLowTailValue_nonneg_of_correctedGram_posSemidef
    cReal cImag x a b hphase
      (completedCanonicalPhaseLowTailCorrectedGram_posSemidef_of_real
        a b hphase hreal)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural
