import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowDiskSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowToeplitz
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural

set_option autoImplicit false
set_option maxRecDepth 100000

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowUnbalancedStaticStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
open YoshidaFactorTwoPhaseConcreteCleanOddMatrix
open YoshidaFactorTwoPhaseConcreteLowDiskSchur
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
open YoshidaFactorTwoPhaseConcreteLowToeplitz
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Unbalanced static transfer for the complete concrete low block

The balanced parity split fixes the even--odd cross block to `J / 2` at both
endpoints.  Here an arbitrary transfer matrix `H` is subtracted at the
positive even endpoint and added at the negative even endpoint.  The two
transfers cancel in the square-root interpolation across the phase disk.

Consequently, positivity of two fixed real `210 x 210` matrices is enough to
certify the complete concrete low phase.  Choosing `H` is an analytic
preconditioning problem; the theorem below neither enumerates phase points
nor introduces a phase-dependent certificate.
-/

/-- The bilinear value represented by an arbitrary static transfer block. -/
def factorTwoConcreteLowTransferValue
    (H : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) : ℝ :=
  ∑ i, ∑ j, e i * H i j * o j

/-- Positive-even endpoint with the transfer removed from the cross block. -/
def factorTwoConcreteLowUnbalancedStaticPlusMatrix
    (H : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ) :
    Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ :=
  factorTwoPhaseBlockMatrix
    (factorTwoConcreteAdaptedEvenCleanMatrix +
      factorTwoConcreteEvenPerturbationMatrix)
    (factorTwoConcreteOddCleanMatrix -
      factorTwoConcreteOddPerturbationMatrix)
    (fun i j ↦ factorTwoConcreteAlternatingMatrix i j / 2 - H i j)

/-- Negative-even endpoint with the transfer restored to the cross block. -/
def factorTwoConcreteLowUnbalancedStaticMinusMatrix
    (H : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ) :
    Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ :=
  factorTwoPhaseBlockMatrix
    (factorTwoConcreteAdaptedEvenCleanMatrix -
      factorTwoConcreteEvenPerturbationMatrix)
    (factorTwoConcreteOddCleanMatrix +
      factorTwoConcreteOddPerturbationMatrix)
    (fun i j ↦ factorTwoConcreteAlternatingMatrix i j / 2 + H i j)

theorem factorTwoConcreteLowUnbalancedStaticPlusMatrix_isHermitian
    (H : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ) :
    (factorTwoConcreteLowUnbalancedStaticPlusMatrix H).IsHermitian := by
  exact factorTwoPhaseBlockMatrix_isHermitian _
    (factorTwoConcreteAdaptedEvenCleanMatrix_isHermitian.add
      factorTwoConcreteEvenPerturbationMatrix_isHermitian)
    (factorTwoConcreteOddCleanMatrix_isHermitian.sub
      factorTwoConcreteOddPerturbationMatrix_isHermitian)

theorem factorTwoConcreteLowUnbalancedStaticMinusMatrix_isHermitian
    (H : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ) :
    (factorTwoConcreteLowUnbalancedStaticMinusMatrix H).IsHermitian := by
  exact factorTwoPhaseBlockMatrix_isHermitian _
    (factorTwoConcreteAdaptedEvenCleanMatrix_isHermitian.sub
      factorTwoConcreteEvenPerturbationMatrix_isHermitian)
    (factorTwoConcreteOddCleanMatrix_isHermitian.add
      factorTwoConcreteOddPerturbationMatrix_isHermitian)

private theorem alternating_half_twice
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    2 * ∑ i, ∑ j,
        e i * (factorTwoConcreteAlternatingMatrix i j / 2) * o j =
      factorTwoConcreteAlternatingValue e o := by
  unfold factorTwoConcreteAlternatingValue
  have hhalf :
      (∑ i, ∑ j,
          e i * (factorTwoConcreteAlternatingMatrix i j / 2) * o j) =
        (∑ i, ∑ j,
          e i * factorTwoConcreteAlternatingMatrix i j * o j) / 2 := by
    simp_rw [show ∀ (x y z : ℝ), x * (y / 2) * z = (x * y * z) / 2 by
      intro x y z
      ring]
    simp_rw [Finset.sum_div]
  rw [hhalf]
  ring

private theorem alternating_transfer_sub_sum
    (H : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    2 * ∑ i, ∑ j,
        e i * (factorTwoConcreteAlternatingMatrix i j / 2 - H i j) * o j =
      factorTwoConcreteAlternatingValue e o -
        2 * factorTwoConcreteLowTransferValue H e o := by
  have hhalf := alternating_half_twice e o
  unfold factorTwoConcreteLowTransferValue
  simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [show
      2 * ((∑ i, ∑ j,
          e i * (factorTwoConcreteAlternatingMatrix i j / 2) * o j) -
        ∑ i, ∑ j, e i * H i j * o j) =
        2 * (∑ i, ∑ j,
          e i * (factorTwoConcreteAlternatingMatrix i j / 2) * o j) -
        2 * (∑ i, ∑ j, e i * H i j * o j) by ring,
    hhalf]

private theorem alternating_transfer_add_sum
    (H : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    2 * ∑ i, ∑ j,
        e i * (factorTwoConcreteAlternatingMatrix i j / 2 + H i j) * o j =
      factorTwoConcreteAlternatingValue e o +
        2 * factorTwoConcreteLowTransferValue H e o := by
  have hhalf := alternating_half_twice e o
  unfold factorTwoConcreteLowTransferValue
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  rw [show
      2 * ((∑ i, ∑ j,
          e i * (factorTwoConcreteAlternatingMatrix i j / 2) * o j) +
        ∑ i, ∑ j, e i * H i j * o j) =
        2 * (∑ i, ∑ j,
          e i * (factorTwoConcreteAlternatingMatrix i j / 2) * o j) +
        2 * (∑ i, ∑ j, e i * H i j * o j) by ring,
    hhalf]

/-- Exact quadratic represented by the corrected positive static endpoint. -/
theorem factorTwoConcreteLowUnbalancedStaticPlusMatrix_quadratic
    (H : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    let c := factorTwoPhaseLowCoefficients e o
    c ⬝ᵥ (factorTwoConcreteLowUnbalancedStaticPlusMatrix H *ᵥ c) =
      factorTwoConcreteEvenPencilValue 1 e +
        factorTwoConcreteOddPencilValue (-1) o +
        factorTwoConcreteAlternatingValue e o -
        2 * factorTwoConcreteLowTransferValue H e o := by
  dsimp only
  rw [factorTwoConcreteLowUnbalancedStaticPlusMatrix,
    factorTwoPhaseBlockMatrix_quadratic]
  simp only [add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub]
  rw [alternating_transfer_sub_sum]
  unfold factorTwoConcreteEvenPencilValue factorTwoConcreteOddPencilValue
  simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  ring

/-- Exact quadratic represented by the corrected negative static endpoint. -/
theorem factorTwoConcreteLowUnbalancedStaticMinusMatrix_quadratic
    (H : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    let c := factorTwoPhaseLowCoefficients e o
    c ⬝ᵥ (factorTwoConcreteLowUnbalancedStaticMinusMatrix H *ᵥ c) =
      factorTwoConcreteEvenPencilValue (-1) e +
        factorTwoConcreteOddPencilValue 1 o +
        factorTwoConcreteAlternatingValue e o +
        2 * factorTwoConcreteLowTransferValue H e o := by
  dsimp only
  rw [factorTwoConcreteLowUnbalancedStaticMinusMatrix,
    factorTwoPhaseBlockMatrix_quadratic]
  simp only [add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub]
  rw [alternating_transfer_add_sum]
  unfold factorTwoConcreteEvenPencilValue factorTwoConcreteOddPencilValue
  simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  ring

private theorem matrixBilinearValue_scale
    (M : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (r s : ℝ) :
    (∑ i, ∑ j, (r • e) i * M i j * (s • o) j) =
      r * s * ∑ i, ∑ j, e i * M i j * o j := by
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, ∑ j, r * e i * M i j * (s * o j)) =
        ∑ i, ∑ j, (r * s) * (e i * M i j * o j) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = ∑ i, (r * s) * ∑ j, e i * M i j * o j := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    _ = r * s * ∑ i, ∑ j, e i * M i j * o j := by
      rw [Finset.mul_sum]

theorem factorTwoConcreteLowTransferValue_scale
    (H : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (r s : ℝ) :
    factorTwoConcreteLowTransferValue H (r • e) (s • o) =
      r * s * factorTwoConcreteLowTransferValue H e o := by
  unfold factorTwoConcreteLowTransferValue
  exact matrixBilinearValue_scale H e o r s

theorem factorTwoConcreteEvenPencilValue_scale
    (a r : ℝ) (e : YoshidaEvenIndex → ℝ) :
    factorTwoConcreteEvenPencilValue a (r • e) =
      r ^ 2 * factorTwoConcreteEvenPencilValue a e := by
  unfold factorTwoConcreteEvenPencilValue
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

theorem factorTwoConcreteOddPencilValue_scale
    (a s : ℝ) (o : YoshidaOddIndex → ℝ) :
    factorTwoConcreteOddPencilValue a (s • o) =
      s ^ 2 * factorTwoConcreteOddPencilValue a o := by
  unfold factorTwoConcreteOddPencilValue
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

theorem factorTwoConcreteAlternatingValue_scale
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (r s : ℝ) :
    factorTwoConcreteAlternatingValue (r • e) (s • o) =
      r * s * factorTwoConcreteAlternatingValue e o := by
  unfold factorTwoConcreteAlternatingValue
  exact matrixBilinearValue_scale factorTwoConcreteAlternatingMatrix e o r s

private theorem factorTwoConcreteAlternatingValue_eq_coupling
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    factorTwoConcreteAlternatingValue e o =
      factorTwoCenteredAlternatingCoupling
        (factorTwoAdaptedEvenLowSynthesis e) (factorTwoOddLowSynthesis o) := by
  unfold factorTwoConcreteAlternatingValue
  exact (factorTwoConcreteAlternatingMatrix_represents e o).symm

private theorem factorTwoConcreteEvenPencilValue_eq_phaseDiagonal
    (a : ℝ) (e : YoshidaEvenIndex → ℝ) :
    factorTwoConcreteEvenPencilValue a e =
      factorTwoEndpointPhaseDiagonal (factorTwoAdaptedEvenLowSynthesis e) a := by
  unfold factorTwoConcreteEvenPencilValue factorTwoEndpointPhaseDiagonal
  simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  rw [← factorTwoConcreteAdaptedEvenCleanMatrix_represents,
    ← factorTwoConcreteEvenPerturbationMatrix_represents]

private theorem factorTwoConcreteOddPencilValue_eq_phaseDiagonal
    (a : ℝ) (o : YoshidaOddIndex → ℝ) :
    factorTwoConcreteOddPencilValue a o =
      factorTwoEndpointPhaseDiagonal (factorTwoOddLowSynthesis o) a := by
  unfold factorTwoConcreteOddPencilValue factorTwoEndpointPhaseDiagonal
  simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  rw [← factorTwoConcreteOddCleanMatrix_represents,
    ← factorTwoConcreteOddPerturbationMatrix_represents]

/-- Two fixed corrected static matrices close the entire concrete low phase
on the closed disk.  The transfer `H` is arbitrary and phase-independent. -/
theorem factorTwoConcreteLowPhase_nonneg_of_unbalanced_static
    (H : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (hPlus : (factorTwoConcreteLowUnbalancedStaticPlusMatrix H).PosSemidef)
    (hMinus : (factorTwoConcreteLowUnbalancedStaticMinusMatrix H).PosSemidef)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoAdaptedEvenLowSynthesis e)
      (factorTwoOddLowSynthesis o) a b := by
  let h := factorTwoConcreteLowTransferValue H e o
  apply factorTwoEndpointChannelPhase_nonneg_of_unbalanced_profile_static_splits
    (factorTwoAdaptedEvenLowSynthesis e)
    (factorTwoOddLowSynthesis o) h a b hab
  · intro r s
    have hPSD : 0 ≤ factorTwoPhaseLowCoefficients (r • e) (s • o) ⬝ᵥ
        (factorTwoConcreteLowUnbalancedStaticPlusMatrix H *ᵥ
          factorTwoPhaseLowCoefficients (r • e) (s • o)) := by
      simpa only [star_trivial] using hPlus.dotProduct_mulVec_nonneg
        (factorTwoPhaseLowCoefficients (r • e) (s • o))
    rw [factorTwoConcreteLowUnbalancedStaticPlusMatrix_quadratic] at hPSD
    rw [factorTwoConcreteEvenPencilValue_scale,
      factorTwoConcreteOddPencilValue_scale,
      factorTwoConcreteAlternatingValue_scale,
      factorTwoConcreteLowTransferValue_scale] at hPSD
    rw [factorTwoConcreteEvenPencilValue_eq_phaseDiagonal,
      factorTwoConcreteOddPencilValue_eq_phaseDiagonal,
      factorTwoConcreteAlternatingValue_eq_coupling] at hPSD
    dsimp only [h]
    nlinarith [hPSD]
  · intro r s
    have hPSD : 0 ≤ factorTwoPhaseLowCoefficients (r • e) (s • o) ⬝ᵥ
        (factorTwoConcreteLowUnbalancedStaticMinusMatrix H *ᵥ
          factorTwoPhaseLowCoefficients (r • e) (s • o)) := by
      simpa only [star_trivial] using hMinus.dotProduct_mulVec_nonneg
        (factorTwoPhaseLowCoefficients (r • e) (s • o))
    rw [factorTwoConcreteLowUnbalancedStaticMinusMatrix_quadratic] at hPSD
    rw [factorTwoConcreteEvenPencilValue_scale,
      factorTwoConcreteOddPencilValue_scale,
      factorTwoConcreteAlternatingValue_scale,
      factorTwoConcreteLowTransferValue_scale] at hPSD
    rw [factorTwoConcreteEvenPencilValue_eq_phaseDiagonal,
      factorTwoConcreteOddPencilValue_eq_phaseDiagonal,
      factorTwoConcreteAlternatingValue_eq_coupling] at hPSD
    dsimp only [h]
    nlinarith [hPSD]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowUnbalancedStaticStructural
