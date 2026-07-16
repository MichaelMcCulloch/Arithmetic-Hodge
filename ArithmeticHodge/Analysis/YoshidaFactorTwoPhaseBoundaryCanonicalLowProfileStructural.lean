import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousPhaseCongruenceStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanEvenMomentFormula
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanOddMatrix

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open Complex Matrix Real Set
open scoped BigOperators ComplexConjugate

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaClippedEvenMomentBridge
open YoshidaCoercivityNumerics
open YoshidaEndpointEvenBoundaryProductionBridge
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaEvenDistributionReduction
open YoshidaEvenIntervalCertificate
open YoshidaOddGramPrefix
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousPhaseCongruenceStructural
open YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseConcreteCleanEvenMomentFormula
open YoshidaFactorTwoPhaseConcreteCleanOddMatrix
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPhaseLowSchur
open YoshidaPointwiseParityCore
open YoshidaSectionSixAnalytic
open YoshidaWeightedTailBounds

/-!
# Canonical finite-low profiles on the boundary-continuous carrier

The boundary-continuous representative of a clipped cosine is its endpoint
constant outside `[-1,1]`, so it is not literally the global cosine there.
All factor-two forms are local to `[-1,1]`, however.  This file proves the
exact restriction equality and transports the complete finite-low form to
the original canonical `Fin 200` coordinates.
-/

/-- The globally continuous cosine synthesis in the original canonical
`Fin 200` even coordinates. -/
def factorTwoCanonicalEvenLowSynthesis
    (e : YoshidaEvenIndex → ℝ) : ℝ → ℝ :=
  ∑ i, e i • factorTwoCenteredCanonicalEvenProfile
    (factorTwoCanonicalEvenLowIndex i)

/-- The boundary-continuous synthesis of the same canonical clipped low
block. -/
def factorTwoBoundaryCanonicalEvenLowProfile
    (e : YoshidaEvenIndex → ℝ) : ℝ → ℝ :=
  boundaryContinuousEvenProfile (canonicalEvenRealLowPointwise e)

theorem continuous_factorTwoCanonicalEvenLowSynthesis
    (e : YoshidaEvenIndex → ℝ) :
    Continuous (factorTwoCanonicalEvenLowSynthesis e) := by
  classical
  unfold factorTwoCanonicalEvenLowSynthesis
  exact continuous_finset_sum Finset.univ fun i _ ↦
    (continuous_factorTwoCenteredCanonicalEvenProfile _).const_smul (e i)

theorem continuous_factorTwoBoundaryCanonicalEvenLowProfile
    (e : YoshidaEvenIndex → ℝ) :
    Continuous (factorTwoBoundaryCanonicalEvenLowProfile e) := by
  exact continuous_boundaryContinuousEvenProfile
    (canonicalEvenRealLowPointwise e)

private theorem canonicalEvenRealLowPointwise_im_zero
    (e : YoshidaEvenIndex → ℝ) (x : ℝ) :
    ((((canonicalEvenRealLowPointwise e).1 :
        YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) x).im = 0 := by
  classical
  simp only [canonicalEvenRealLowPointwise,
    canonicalEvenRealLowPeriodicCore_toSmooth, Submodule.coe_sum,
    Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [evenLowMode_im_zero]
    ring

/-- On the only interval seen by the factor-two channel, a centered clipped
canonical even mode is its global normalized cosine representative. -/
theorem centeredRescale_canonicalEvenLowMode_eq_canonical
    (i : YoshidaEvenIndex) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    centeredRescale yoshidaA
        (fun y ↦ (yoshidaClippedEvenLowMode yoshidaA i y).re) x =
      factorTwoCenteredCanonicalEvenProfile
        (factorTwoCanonicalEvenLowIndex i) x := by
  have hAx : yoshidaA * x ∈ Icc (-yoshidaA) yoshidaA := by
    constructor
    · nlinarith [yoshidaA_pos, hx.1]
    · nlinarith [yoshidaA_pos, hx.2]
  have harg (n : ℕ) :
      Real.pi * (n : ℝ) * (yoshidaA * x) / yoshidaA =
        Real.pi * (n : ℝ) * x := by
    field_simp [yoshidaA_pos.ne']
  have hcenterC (n : ℕ) :
      (Real.pi : ℂ) * (n : ℂ) * (x : ℂ) =
        ((Real.pi * (n : ℝ) * x : ℝ) : ℂ) := by
    push_cast
    rfl
  have hinvSqrtTwo : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
    have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [hsqrt]
    nlinarith
  by_cases hi : i.1 = 0
  · simp [centeredRescale, yoshidaClippedEvenLowMode, hi,
      yoshidaClippedEvenZeroMode_apply_of_mem hAx,
      factorTwoCenteredCanonicalEvenProfile,
      factorTwoCanonicalEvenLowIndex, hinvSqrtTwo]
  · simp [centeredRescale, yoshidaClippedEvenLowMode, hi,
      yoshidaClippedEvenMode_apply_of_mem yoshidaA_pos i.1 hAx,
      factorTwoCenteredCanonicalEvenProfile,
      factorTwoCanonicalEvenLowIndex, harg]
    left
    rw [hcenterC i.1, Complex.cos_ofReal_re]

/-- A single canonical retained mode bundled with its literal even parity. -/
def canonicalEvenLowModePointwise (i : YoshidaEvenIndex) :
    yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
  ⟨canonicalEvenLowModePeriodicCore i,
    canonicalEvenLowMode_pointwise_even i⟩

/-- The boundary-continuous profile of each canonical retained mode agrees
with its global cosine representative on `[-1,1]`. -/
theorem boundaryContinuousEvenProfile_canonicalEvenLowMode_eq_canonical
    (i : YoshidaEvenIndex) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    boundaryContinuousEvenProfile
        (canonicalEvenLowModePointwise i) x =
      factorTwoCenteredCanonicalEvenProfile
        (factorTwoCanonicalEvenLowIndex i) x := by
  rw [boundaryContinuousEvenProfile_eq_centeredRescale _
    (fun y ↦ by
      simpa only [canonicalEvenLowModePointwise,
        canonicalEvenLowModePeriodicCore_toSmooth] using
          evenLowMode_im_zero i y) hx]
  change centeredRescale yoshidaA
      (fun y ↦ (yoshidaClippedEvenLowMode yoshidaA i y).re) x = _
  exact centeredRescale_canonicalEvenLowMode_eq_canonical i hx

/-- The preceding mode identity extends exactly to every real coefficient
synthesis. -/
theorem factorTwoBoundaryCanonicalEvenLowProfile_eq_canonical_Icc
    (e : YoshidaEvenIndex → ℝ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoBoundaryCanonicalEvenLowProfile e x =
      factorTwoCanonicalEvenLowSynthesis e x := by
  rw [factorTwoBoundaryCanonicalEvenLowProfile,
    boundaryContinuousEvenProfile_eq_centeredRescale _
      (canonicalEvenRealLowPointwise_im_zero e) hx]
  classical
  unfold factorTwoCanonicalEvenLowSynthesis centeredRescale
  simp only [canonicalEvenRealLowPointwise,
    canonicalEvenRealLowPeriodicCore_toSmooth, Submodule.coe_sum,
    Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  have hi := centeredRescale_canonicalEvenLowMode_eq_canonical i hx
  unfold centeredRescale at hi
  exact congrArg (fun z : ℝ ↦ e i * z) hi

/-! ## Locality bridges -/

theorem factorTwoBoundaryCanonicalEvenLowProfile_clean_eq_canonical
    (e : YoshidaEvenIndex → ℝ) :
    yoshidaEndpointOddCleanQuadratic
        (factorTwoBoundaryCanonicalEvenLowProfile e) =
      yoshidaEndpointOddCleanQuadratic
        (factorTwoCanonicalEvenLowSynthesis e) := by
  apply yoshidaEndpointOddCleanQuadratic_congr_Icc
  exact fun x hx ↦ factorTwoBoundaryCanonicalEvenLowProfile_eq_canonical_Icc e hx

theorem factorTwoBoundaryCanonicalEvenLowProfile_symmetric_eq_canonical
    (e : YoshidaEvenIndex → ℝ) :
    factorTwoCenteredSymmetricPerturbation
        (factorTwoBoundaryCanonicalEvenLowProfile e) =
      factorTwoCenteredSymmetricPerturbation
        (factorTwoCanonicalEvenLowSynthesis e) := by
  apply factorTwoCenteredSymmetricPerturbation_congr_Icc
  exact fun x hx ↦ factorTwoBoundaryCanonicalEvenLowProfile_eq_canonical_Icc e hx

theorem factorTwoBoundaryCanonicalEvenLowProfile_alternating_eq_canonical
    (e : YoshidaEvenIndex → ℝ) (v : ℝ → ℝ) :
    factorTwoCenteredAlternatingCoupling
        (factorTwoBoundaryCanonicalEvenLowProfile e) v =
      factorTwoCenteredAlternatingCoupling
        (factorTwoCanonicalEvenLowSynthesis e) v := by
  apply factorTwoCenteredAlternatingCoupling_congr_Icc
  · exact fun x hx ↦
      factorTwoBoundaryCanonicalEvenLowProfile_eq_canonical_Icc e hx
  · exact fun _ _ ↦ rfl

theorem factorTwoBoundaryCanonicalEvenLowProfile_phase_eq_canonical
    (e : YoshidaEvenIndex → ℝ) (v : ℝ → ℝ) (a b : ℝ) :
    factorTwoEndpointChannelPhase
        (factorTwoBoundaryCanonicalEvenLowProfile e) v a b =
      factorTwoEndpointChannelPhase
        (factorTwoCanonicalEvenLowSynthesis e) v a b := by
  apply factorTwoEndpointChannelPhase_congr_Icc
  · exact fun x hx ↦
      factorTwoBoundaryCanonicalEvenLowProfile_eq_canonical_Icc e hx
  · exact fun _ _ ↦ rfl

/-! ## Canonical finite matrices -/

/-- The clean matrix in the original canonical `Fin 200` cosine basis. -/
def factorTwoCanonicalEvenCleanMatrix :
    Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ :=
  fun i j ↦
    (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
      (yoshidaClippedEvenLowMode yoshidaA i)
      (yoshidaClippedEvenLowMode yoshidaA j)).re / yoshidaA

/-- The canonical clean entry is the already-existing Section-6 moment entry,
scaled only by the endpoint length. -/
theorem factorTwoCanonicalEvenCleanMatrix_apply
    (i j : YoshidaEvenIndex) :
    factorTwoCanonicalEvenCleanMatrix i j =
      evenMomentFullGram yoshidaSineMoment yoshidaDiagonalMoment i j /
        yoshidaA := by
  let li := clippedEvenUnifiedMode i.1
  let lj := clippedEvenUnifiedMode j.1
  have hli : yoshidaClippedEvenLowMode yoshidaA i = li := by
    simpa only [li, yoshidaHalfLength, yoshidaLength, yoshidaA] using
      (clippedEvenUnifiedMode_eq_lowMode i).symm
  have hlj : yoshidaClippedEvenLowMode yoshidaA j = lj := by
    simpa only [lj, yoshidaHalfLength, yoshidaLength, yoshidaA] using
      (clippedEvenUnifiedMode_eq_lowMode j).symm
  unfold factorTwoCanonicalEvenCleanMatrix evenMomentFullGram
  rw [hli, hlj,
    yoshidaClippedLocalCriticalForm_unifiedEven_eq_evenMomentGram]
  norm_num

/-- The symmetric perturbation matrix is the canonical entry table already
used by the frequency-`200` endpoint-adaptation formulas, restricted to the
original retained indices. -/
def factorTwoCanonicalEvenPerturbationMatrix :
    Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ :=
  fun i j ↦ factorTwoCanonicalEvenPerturbationEntry
    (factorTwoCanonicalEvenLowIndex i)
    (factorTwoCanonicalEvenLowIndex j)

/-- The canonical even--odd alternating entry table. -/
def factorTwoCanonicalAlternatingMatrix :
    Matrix YoshidaEvenIndex YoshidaOddIndex ℝ :=
  fun i j ↦ factorTwoCenteredAlternatingCoupling
    (factorTwoCenteredCanonicalEvenProfile
      (factorTwoCanonicalEvenLowIndex i))
    (factorTwoCenteredOddLowProfile j)

private theorem continuous_finset_smul_sum
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → ℝ → ℝ)
    (hu : ∀ i, Continuous (u i)) :
    Continuous (∑ i ∈ s, c i • u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℝ)))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact ((hu i).const_smul (c i)).add ih

private theorem symmetricPerturbationBilinear_comm
    (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear u v =
      factorTwoCenteredSymmetricPerturbationBilinear v u := by
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_comm u v]

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
        factorTwoCenteredSymmetricPerturbationBilinear_smul_left 0 v v
  | @insert i s hi ih =>
      have hsContinuous : Continuous (∑ j ∈ s, c j • u j) :=
        continuous_finset_smul_sum s c u hu
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        factorTwoCenteredSymmetricPerturbationBilinear_add_left
          (c i • u i) (∑ j ∈ s, c j • u j) v
          ((hu i).const_smul (c i)) hsContinuous hv,
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
  intro i _
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
      have hsContinuous : Continuous (∑ j ∈ s, c j • u j) :=
        continuous_finset_smul_sum s c u hu
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        factorTwoCenteredAlternatingCoupling_add_left
          (c i • u i) (∑ j ∈ s, c j • u j) v
          ((hu i).const_smul (c i)) hsContinuous hv,
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
      have hsContinuous : Continuous (∑ j ∈ s, c j • v j) :=
        continuous_finset_smul_sum s c v hv
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        factorTwoCenteredAlternatingCoupling_add_right u
          (c i • v i) (∑ j ∈ s, c j • v j) hu
          ((hv i).const_smul (c i)) hsContinuous,
        factorTwoCenteredAlternatingCoupling_smul_right, ih]

private theorem canonicalEvenLowSmoothSynthesis_critical_value
    (e : YoshidaEvenIndex → ℝ) :
    clippedCriticalFormValue yoshidaA yoshidaA_pos
        (∑ i, (e i : ℂ) • yoshidaClippedEvenLowMode yoshidaA i) =
      ∑ i, ∑ j, e i * e j *
        (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
          (yoshidaClippedEvenLowMode yoshidaA i)
          (yoshidaClippedEvenLowMode yoshidaA j)).re := by
  classical
  simp only [clippedCriticalFormValue, map_sum, map_smul, map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Complex.conj_ofReal, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact clean quadratic representation on the boundary-continuous
canonical low block. -/
theorem factorTwoCanonicalEvenCleanMatrix_represents
    (e : YoshidaEvenIndex → ℝ) :
    yoshidaEndpointOddCleanQuadratic
        (factorTwoBoundaryCanonicalEvenLowProfile e) =
      e ⬝ᵥ (factorTwoCanonicalEvenCleanMatrix *ᵥ e) := by
  let f := canonicalEvenRealLowPointwise e
  have hbridge := clippedCriticalFormValue_even_eq_clean_add_boundary f
    (canonicalEvenRealLowPointwise_im_zero e)
  have hbridge' :
      clippedCriticalFormValue yoshidaA yoshidaA_pos
          (∑ i, (e i : ℂ) • yoshidaClippedEvenLowMode yoshidaA i) =
        yoshidaA * yoshidaEndpointOddCleanQuadratic
          (factorTwoBoundaryCanonicalEvenLowProfile e) := by
    simpa only [f, factorTwoBoundaryCanonicalEvenLowProfile,
      canonicalEvenRealLowPointwise,
      canonicalEvenRealLowPeriodicCore_toSmooth,
      YoshidaEndpointHyperbolicBound.yoshidaEndpointA,
      YoshidaWeightedTailBounds.yoshidaA,
      boundaryContinuousEvenProfile] using hbridge
  rw [canonicalEvenLowSmoothSynthesis_critical_value] at hbridge'
  have hmatrix :
      yoshidaA * (e ⬝ᵥ (factorTwoCanonicalEvenCleanMatrix *ᵥ e)) =
        ∑ i, ∑ j, e i * e j *
          (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (yoshidaClippedEvenLowMode yoshidaA i)
            (yoshidaClippedEvenLowMode yoshidaA j)).re := by
    simp only [dotProduct, mulVec, factorTwoCanonicalEvenCleanMatrix]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [yoshidaA_pos.ne']
  nlinarith [yoshidaA_pos]

/-- Exact symmetric-perturbation representation through the existing
canonical entry table. -/
theorem factorTwoCanonicalEvenPerturbationMatrix_represents
    (e : YoshidaEvenIndex → ℝ) :
    factorTwoCenteredSymmetricPerturbation
        (factorTwoBoundaryCanonicalEvenLowProfile e) =
      e ⬝ᵥ (factorTwoCanonicalEvenPerturbationMatrix *ᵥ e) := by
  rw [factorTwoBoundaryCanonicalEvenLowProfile_symmetric_eq_canonical,
    ← factorTwoCenteredSymmetricPerturbationBilinear_self,
    factorTwoCanonicalEvenLowSynthesis,
    symmetricPerturbationBilinear_sum_left e
      (fun i ↦ factorTwoCenteredCanonicalEvenProfile
        (factorTwoCanonicalEvenLowIndex i))
      (∑ i, e i • factorTwoCenteredCanonicalEvenProfile
        (factorTwoCanonicalEvenLowIndex i))
      (fun i ↦ continuous_factorTwoCenteredCanonicalEvenProfile _)
      (continuous_factorTwoCanonicalEvenLowSynthesis e)]
  simp only [dotProduct, mulVec, factorTwoCanonicalEvenPerturbationMatrix,
    factorTwoCanonicalEvenPerturbationEntry]
  apply Finset.sum_congr rfl
  intro i _
  rw [symmetricPerturbationBilinear_sum_right
    (factorTwoCenteredCanonicalEvenProfile
      (factorTwoCanonicalEvenLowIndex i)) e
    (fun j ↦ factorTwoCenteredCanonicalEvenProfile
      (factorTwoCanonicalEvenLowIndex j))
    (continuous_factorTwoCenteredCanonicalEvenProfile _)
    (fun j ↦ continuous_factorTwoCenteredCanonicalEvenProfile _)]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact alternating representation between the boundary-continuous
canonical even low block and the existing canonical odd synthesis. -/
theorem factorTwoCanonicalAlternatingMatrix_represents
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    factorTwoCenteredAlternatingCoupling
        (factorTwoBoundaryCanonicalEvenLowProfile e)
        (factorTwoOddLowSynthesis o) =
      ∑ i, ∑ j, e i * factorTwoCanonicalAlternatingMatrix i j * o j := by
  rw [factorTwoBoundaryCanonicalEvenLowProfile_alternating_eq_canonical,
    factorTwoCanonicalEvenLowSynthesis,
    alternatingCoupling_sum_left e
      (fun i ↦ factorTwoCenteredCanonicalEvenProfile
        (factorTwoCanonicalEvenLowIndex i))
      (factorTwoOddLowSynthesis o)
      (fun i ↦ continuous_factorTwoCenteredCanonicalEvenProfile _)
      (continuous_factorTwoOddLowSynthesis o)]
  apply Finset.sum_congr rfl
  intro i _
  rw [factorTwoOddLowSynthesis,
    alternatingCoupling_sum_right
      (factorTwoCenteredCanonicalEvenProfile
        (factorTwoCanonicalEvenLowIndex i)) o
      factorTwoCenteredOddLowProfile
      (continuous_factorTwoCenteredCanonicalEvenProfile _)
      continuous_factorTwoCenteredOddLowProfile,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [factorTwoCanonicalAlternatingMatrix]
  ring

/-- The complete boundary-continuous canonical finite-low phase is exactly
the generic `Fin 200 + Fin 10` phase matrix with canonical even blocks. -/
theorem factorTwoBoundaryCanonicalFiniteLowPhaseMatrix_represents
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) :
    factorTwoEndpointChannelPhase
        (factorTwoBoundaryCanonicalEvenLowProfile e)
        (factorTwoOddLowSynthesis o) a b =
      let c := factorTwoPhaseLowCoefficients e o
      c ⬝ᵥ (factorTwoFiniteLowPhaseMatrix
        factorTwoCanonicalEvenCleanMatrix
        factorTwoCanonicalEvenPerturbationMatrix
        factorTwoConcreteOddCleanMatrix
        factorTwoConcreteOddPerturbationMatrix
        factorTwoCanonicalAlternatingMatrix a b *ᵥ c) := by
  apply factorTwoFiniteLowPhaseMatrix_represents
  · exact factorTwoCanonicalEvenCleanMatrix_represents e
  · exact factorTwoConcreteOddCleanMatrix_represents o
  · exact factorTwoCanonicalEvenPerturbationMatrix_represents e
  · exact factorTwoConcreteOddPerturbationMatrix_represents o
  · exact factorTwoCanonicalAlternatingMatrix_represents e o

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
