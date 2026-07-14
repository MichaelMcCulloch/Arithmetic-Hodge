import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedLow
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddRealDecomposition
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLowSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRadiusClosure

set_option autoImplicit false
set_option maxRecDepth 100000

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowMatrix

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddRealDecomposition
open YoshidaFactorTwoPhaseRadiusClosure
open YoshidaOddInfiniteSchur
open YoshidaOddModeRegularity
open YoshidaWeightedTailBounds

/-!
# Concrete finite low phase matrix

This module instantiates the perturbation and alternating blocks of the
`200 + 10` finite phase matrix on the endpoint-adapted real Fourier bases.
It deliberately does not define the clean blocks: identifying the endpoint
clean quadratic with a finite Gram matrix remains a separate obligation.
-/

/-- The centered real profile of an endpoint-adapted even low mode. -/
def factorTwoCenteredAdaptedEvenLowProfile
    (i : YoshidaEvenIndex) : ℝ → ℝ :=
  centeredRescale yoshidaA
    (fun y ↦ (endpointAdaptedEvenLowMode i y).re)

/-- The centered real profile of a canonical odd low mode. -/
def factorTwoCenteredOddLowProfile
    (i : YoshidaOddIndex) : ℝ → ℝ :=
  centeredRescale yoshidaA
    (fun y ↦ (yoshidaClippedOddLowMode yoshidaA i y).re)

/-- A real even coefficient vector synthesized in the endpoint-adapted
centered basis. -/
def factorTwoAdaptedEvenLowSynthesis
    (e : YoshidaEvenIndex → ℝ) : ℝ → ℝ :=
  ∑ i, e i • factorTwoCenteredAdaptedEvenLowProfile i

/-- A real odd coefficient vector synthesized in the canonical centered
sine basis. -/
def factorTwoOddLowSynthesis
    (o : YoshidaOddIndex → ℝ) : ℝ → ℝ :=
  ∑ i, o i • factorTwoCenteredOddLowProfile i

theorem continuous_factorTwoCenteredAdaptedEvenLowProfile
    (i : YoshidaEvenIndex) :
    Continuous (factorTwoCenteredAdaptedEvenLowProfile i) := by
  let r : YoshidaClippedPeriodicCore yoshidaA :=
    endpointAdaptedEvenLowModePeriodicCore i
  simpa only [factorTwoCenteredAdaptedEvenLowProfile, r,
    endpointAdaptedEvenLowModePeriodicCore_toSmooth] using
      continuous_centeredRescale_re_of_endpoints_zero yoshidaA_pos r
        (endpointAdaptedEvenLowMode_apply_neg i)
        (endpointAdaptedEvenLowMode_apply_pos i)

theorem continuous_factorTwoCenteredOddLowProfile
    (i : YoshidaOddIndex) :
    Continuous (factorTwoCenteredOddLowProfile i) := by
  unfold factorTwoCenteredOddLowProfile centeredRescale
  rw [yoshidaClippedOddLowMode]
  exact (Complex.continuous_re.comp
      (continuous_yoshidaClippedOddMode yoshidaA_pos (i.1 + 1))).comp
    (continuous_const.mul continuous_id)

theorem continuous_factorTwoAdaptedEvenLowSynthesis
    (e : YoshidaEvenIndex → ℝ) :
    Continuous (factorTwoAdaptedEvenLowSynthesis e) := by
  unfold factorTwoAdaptedEvenLowSynthesis
  change Continuous (fun x ↦
    ∑ i, e i * factorTwoCenteredAdaptedEvenLowProfile i x)
  exact continuous_finset_sum Finset.univ fun i _ ↦
    continuous_const.mul (continuous_factorTwoCenteredAdaptedEvenLowProfile i)

theorem continuous_factorTwoOddLowSynthesis
    (o : YoshidaOddIndex → ℝ) :
    Continuous (factorTwoOddLowSynthesis o) := by
  unfold factorTwoOddLowSynthesis
  change Continuous (fun x ↦
    ∑ i, o i * factorTwoCenteredOddLowProfile i x)
  exact continuous_finset_sum Finset.univ fun i _ ↦
    continuous_const.mul (continuous_factorTwoCenteredOddLowProfile i)

/-- The concrete even symmetric-perturbation block. -/
def factorTwoConcreteEvenPerturbationMatrix :
    Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ :=
  fun i j ↦ factorTwoCenteredSymmetricPerturbationBilinear
    (factorTwoCenteredAdaptedEvenLowProfile i)
    (factorTwoCenteredAdaptedEvenLowProfile j)

/-- The concrete odd symmetric-perturbation block. -/
def factorTwoConcreteOddPerturbationMatrix :
    Matrix YoshidaOddIndex YoshidaOddIndex ℝ :=
  fun i j ↦ factorTwoCenteredSymmetricPerturbationBilinear
    (factorTwoCenteredOddLowProfile i)
    (factorTwoCenteredOddLowProfile j)

/-- The concrete ordered even--odd alternating block. -/
def factorTwoConcreteAlternatingMatrix :
    Matrix YoshidaEvenIndex YoshidaOddIndex ℝ :=
  fun i j ↦ factorTwoCenteredAlternatingCoupling
    (factorTwoCenteredAdaptedEvenLowProfile i)
    (factorTwoCenteredOddLowProfile j)

private theorem symmetricPerturbationBilinear_comm
    (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear u v =
      factorTwoCenteredSymmetricPerturbationBilinear v u := by
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_comm u v]

private theorem continuous_finset_smul_sum
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → ℝ → ℝ)
    (hu : ∀ i, Continuous (u i)) :
    Continuous (∑ i ∈ s, c i • u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℝ)))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact ((hu i).const_smul (c i)).add ih

private theorem symmetricPerturbationBilinear_sum_left
    {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (u : ι → ℝ → ℝ) (v : ℝ → ℝ)
    (hu : ∀ i, Continuous (u i)) (hv : Continuous v) :
    factorTwoCenteredSymmetricPerturbationBilinear
        (∑ i, c i • u i) v =
      ∑ i, c i * factorTwoCenteredSymmetricPerturbationBilinear (u i) v := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa using
        factorTwoCenteredSymmetricPerturbationBilinear_smul_left
          0 v v
  | @insert i s hi ih =>
      have hsContinuous : Continuous (∑ j ∈ s, c j • u j) := by
        exact continuous_finset_smul_sum s c u hu
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        factorTwoCenteredSymmetricPerturbationBilinear_add_left
          (c i • u i) (∑ j ∈ s, c j • u j) v
          ((hu i).const_smul (c i))
          hsContinuous hv,
        factorTwoCenteredSymmetricPerturbationBilinear_smul_left, ih]

private theorem symmetricPerturbationBilinear_sum_right
    {ι : Type*} [Fintype ι]
    (u : ℝ → ℝ) (c : ι → ℝ) (v : ι → ℝ → ℝ)
    (hu : Continuous u) (hv : ∀ i, Continuous (v i)) :
    factorTwoCenteredSymmetricPerturbationBilinear u
        (∑ i, c i • v i) =
      ∑ i, c i * factorTwoCenteredSymmetricPerturbationBilinear u (v i) := by
  rw [symmetricPerturbationBilinear_comm,
    symmetricPerturbationBilinear_sum_left c v u hv hu]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [symmetricPerturbationBilinear_comm (v i) u]

private theorem alternatingCoupling_sum_left
    {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (u : ι → ℝ → ℝ) (v : ℝ → ℝ)
    (hu : ∀ i, Continuous (u i)) (hv : Continuous v) :
    factorTwoCenteredAlternatingCoupling (∑ i, c i • u i) v =
      ∑ i, c i * factorTwoCenteredAlternatingCoupling (u i) v := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa using factorTwoCenteredAlternatingCoupling_smul_left 0 v v
  | @insert i s hi ih =>
      have hsContinuous : Continuous (∑ j ∈ s, c j • u j) := by
        exact continuous_finset_smul_sum s c u hu
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        factorTwoCenteredAlternatingCoupling_add_left
          (c i • u i) (∑ j ∈ s, c j • u j) v
          ((hu i).const_smul (c i))
          hsContinuous hv,
        factorTwoCenteredAlternatingCoupling_smul_left, ih]

private theorem alternatingCoupling_sum_right
    {ι : Type*} [Fintype ι]
    (u : ℝ → ℝ) (c : ι → ℝ) (v : ι → ℝ → ℝ)
    (hu : Continuous u) (hv : ∀ i, Continuous (v i)) :
    factorTwoCenteredAlternatingCoupling u (∑ i, c i • v i) =
      ∑ i, c i * factorTwoCenteredAlternatingCoupling u (v i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa using factorTwoCenteredAlternatingCoupling_smul_right 0 u u
  | @insert i s hi ih =>
      have hsContinuous : Continuous (∑ j ∈ s, c j • v j) := by
        exact continuous_finset_smul_sum s c v hv
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        factorTwoCenteredAlternatingCoupling_add_right u
          (c i • v i) (∑ j ∈ s, c j • v j) hu
          ((hv i).const_smul (c i))
          hsContinuous,
        factorTwoCenteredAlternatingCoupling_smul_right, ih]

/-- Exact symmetric-perturbation synthesis identity on the adapted even
low block. -/
theorem factorTwoConcreteEvenPerturbationMatrix_represents
    (e : YoshidaEvenIndex → ℝ) :
    factorTwoCenteredSymmetricPerturbation
        (factorTwoAdaptedEvenLowSynthesis e) =
      e ⬝ᵥ (factorTwoConcreteEvenPerturbationMatrix *ᵥ e) := by
  rw [← factorTwoCenteredSymmetricPerturbationBilinear_self,
    factorTwoAdaptedEvenLowSynthesis,
    symmetricPerturbationBilinear_sum_left e
      factorTwoCenteredAdaptedEvenLowProfile
      (∑ i, e i • factorTwoCenteredAdaptedEvenLowProfile i)
      continuous_factorTwoCenteredAdaptedEvenLowProfile
      (continuous_factorTwoAdaptedEvenLowSynthesis e)]
  simp only [dotProduct, mulVec, factorTwoConcreteEvenPerturbationMatrix]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [symmetricPerturbationBilinear_sum_right
    (factorTwoCenteredAdaptedEvenLowProfile i) e
    factorTwoCenteredAdaptedEvenLowProfile
    (continuous_factorTwoCenteredAdaptedEvenLowProfile i)
    continuous_factorTwoCenteredAdaptedEvenLowProfile]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Exact symmetric-perturbation synthesis identity on the odd low block. -/
theorem factorTwoConcreteOddPerturbationMatrix_represents
    (o : YoshidaOddIndex → ℝ) :
    factorTwoCenteredSymmetricPerturbation (factorTwoOddLowSynthesis o) =
      o ⬝ᵥ (factorTwoConcreteOddPerturbationMatrix *ᵥ o) := by
  rw [← factorTwoCenteredSymmetricPerturbationBilinear_self,
    factorTwoOddLowSynthesis,
    symmetricPerturbationBilinear_sum_left o
      factorTwoCenteredOddLowProfile
      (∑ i, o i • factorTwoCenteredOddLowProfile i)
      continuous_factorTwoCenteredOddLowProfile
      (continuous_factorTwoOddLowSynthesis o)]
  simp only [dotProduct, mulVec, factorTwoConcreteOddPerturbationMatrix]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [symmetricPerturbationBilinear_sum_right
    (factorTwoCenteredOddLowProfile i) o factorTwoCenteredOddLowProfile
    (continuous_factorTwoCenteredOddLowProfile i)
    continuous_factorTwoCenteredOddLowProfile]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Exact alternating synthesis identity on the coupled low blocks. -/
theorem factorTwoConcreteAlternatingMatrix_represents
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    factorTwoCenteredAlternatingCoupling
        (factorTwoAdaptedEvenLowSynthesis e)
        (factorTwoOddLowSynthesis o) =
      ∑ i, ∑ j, e i * factorTwoConcreteAlternatingMatrix i j * o j := by
  rw [factorTwoAdaptedEvenLowSynthesis,
    alternatingCoupling_sum_left e factorTwoCenteredAdaptedEvenLowProfile
      (factorTwoOddLowSynthesis o)
      continuous_factorTwoCenteredAdaptedEvenLowProfile
      (continuous_factorTwoOddLowSynthesis o)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [factorTwoOddLowSynthesis,
    alternatingCoupling_sum_right
      (factorTwoCenteredAdaptedEvenLowProfile i) o
      factorTwoCenteredOddLowProfile
      (continuous_factorTwoCenteredAdaptedEvenLowProfile i)
      continuous_factorTwoCenteredOddLowProfile,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [factorTwoConcreteAlternatingMatrix]
  ring

/-- Once clean and perturbation synthesis identities are supplied, the
generic finite matrix represents the complete low phase form exactly.  In
this module `hPE`, `hPO`, and `hJ` are discharged by the concrete theorems
above; `hQE` and `hQO` remain the explicit clean-block obligation. -/
theorem factorTwoFiniteLowPhaseMatrix_represents
    (QE PE : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (QO PO : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (J : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (u v : ℝ → ℝ) (a b : ℝ)
    (hQE : yoshidaEndpointOddCleanQuadratic u = e ⬝ᵥ (QE *ᵥ e))
    (hQO : yoshidaEndpointOddCleanQuadratic v = o ⬝ᵥ (QO *ᵥ o))
    (hPE : factorTwoCenteredSymmetricPerturbation u = e ⬝ᵥ (PE *ᵥ e))
    (hPO : factorTwoCenteredSymmetricPerturbation v = o ⬝ᵥ (PO *ᵥ o))
    (hJ : factorTwoCenteredAlternatingCoupling u v =
      ∑ i, ∑ j, e i * J i j * o j) :
    factorTwoEndpointChannelPhase u v a b =
      let c := factorTwoPhaseLowCoefficients e o
      c ⬝ᵥ (factorTwoFiniteLowPhaseMatrix QE PE QO PO J a b *ᵥ c) := by
  rw [factorTwoEndpointChannelPhase, factorTwoEndpointChannelCleanSum,
    factorTwoEndpointChannelSymmetricSum, hQE, hQO, hPE, hPO, hJ,
    factorTwoFiniteLowPhaseMatrix_quadratic]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowMatrix
