import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailEndpointAdaptedRieszStructural
import ArithmeticHodge.Analysis.YoshidaOddInfiniteSchur

set_option autoImplicit false

open Complex Matrix Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalCleanSchurStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaEndpointEvenBoundaryProductionBridge
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaEvenHomogeneousCoercivity
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
open YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyClosureStructural
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionEnergyStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailEndpointShearStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailRieszStructural
open YoshidaFactorTwoPhaseCanonicalLowTailSchurStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddRealDecomposition
open YoshidaFactorTwoPhaseTailRealImagStructural
open YoshidaOddInfiniteSchur
open YoshidaOddHomogeneousCoercivity
open YoshidaOddModeRegularity
open YoshidaPointwiseParityCore
open YoshidaWeightedTailBounds
open YoshidaSectionSixAnalytic

local instance : InnerProductSpace ℝ CanonicalPhaseTailCore :=
  InnerProductSpace.rclikeToReal ℂ CanonicalPhaseTailCore

/-- The boundary-continuous clean quadratic is nonnegative for every real
pointwise-even periodic source. -/
private theorem boundaryContinuousEvenProfile_clean_nonneg
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA)
    (hreal : ∀ x : ℝ,
      ((((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0)) :
    0 ≤ yoshidaEndpointOddCleanQuadratic
      (boundaryContinuousEvenProfile f) := by
  have hform := clippedCriticalFormValue_even_nonneg_of_clean f hreal
  have hform' : 0 ≤ clippedCriticalFormValue yoshidaA yoshidaA_pos
      ((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) := by
    simpa only [YoshidaEndpointHyperbolicBound.yoshidaEndpointA,
      YoshidaWeightedTailBounds.yoshidaA] using hform
  have hbridge := clippedCriticalFormValue_even_eq_clean_add_boundary f hreal
  change clippedCriticalFormValue yoshidaA yoshidaA_pos
      ((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) =
    yoshidaA * yoshidaEndpointOddCleanQuadratic
      (boundaryContinuousEvenProfile f) at hbridge
  rw [hbridge] at hform'
  nlinarith [yoshidaA_pos]

/-- The complete odd low-plus-tail clean quadratic is nonnegative without
examining any finite Gram entries. -/
private theorem oddLow_add_tail_clean_nonneg
    (o : YoshidaOddIndex → ℝ) (f : YoshidaOddTenTail)
    (hfReal : ∀ x : ℝ,
      (oddTenTailToClippedSmooth f x).im = 0) :
    0 ≤ yoshidaEndpointOddCleanQuadratic
      (factorTwoOddLowSynthesis o + canonicalOddTailProfile f) := by
  classical
  let r : YoshidaClippedPeriodicCore yoshidaA :=
    canonicalOddRealLowPeriodicCore o +
      (f : YoshidaClippedPeriodicCore yoshidaA)
  have hrReal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    change (((canonicalOddRealLowPeriodicCore o :
        YoshidaClippedSmooth yoshidaA) x) +
      oddTenTailToClippedSmooth f x).im = 0
    rw [Complex.add_im, hfReal x, add_zero]
    simp only [canonicalOddRealLowPeriodicCore_toSmooth,
      Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact Finset.sum_eq_zero fun j _ ↦ by
      rw [oddLowMode_im_zero]
      ring
  obtain ⟨hfNeg, hfPos⟩ := oddTenTail_endpoints_zero f
  have hrNeg : (r : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0 := by
    change (canonicalOddRealLowPeriodicCore o :
        YoshidaClippedSmooth yoshidaA) (-yoshidaA) +
      oddTenTailToClippedSmooth f (-yoshidaA) = 0
    rw [hfNeg, add_zero]
    simp only [canonicalOddRealLowPeriodicCore_toSmooth,
      Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply]
    exact Finset.sum_eq_zero fun j _ ↦ by
      change (o j : ℂ) •
        yoshidaClippedOddMode yoshidaA (j.1 + 1) (-yoshidaA) = 0
      rw [yoshidaClippedOddMode_left_endpoint yoshidaA_pos (j.1 + 1)]
      simp
  have hrPos : (r : YoshidaClippedSmooth yoshidaA) yoshidaA = 0 := by
    change (canonicalOddRealLowPeriodicCore o :
        YoshidaClippedSmooth yoshidaA) yoshidaA +
      oddTenTailToClippedSmooth f yoshidaA = 0
    rw [hfPos, add_zero]
    simp only [canonicalOddRealLowPeriodicCore_toSmooth,
      Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply]
    exact Finset.sum_eq_zero fun j _ ↦ by
      change (o j : ℂ) •
        yoshidaClippedOddMode yoshidaA (j.1 + 1) yoshidaA = 0
      rw [yoshidaClippedOddMode_right_endpoint yoshidaA_pos (j.1 + 1)]
      simp
  have hprofile : centeredRescale yoshidaA (fun x ↦
      ((r : YoshidaClippedSmooth yoshidaA) x).re) =
      factorTwoOddLowSynthesis o + canonicalOddTailProfile f := by
    calc
      centeredRescale yoshidaA (fun x ↦
          ((r : YoshidaClippedSmooth yoshidaA) x).re) =
          centeredRescale yoshidaA (fun x ↦
            ((canonicalOddRealLowPeriodicCore o :
              YoshidaClippedSmooth yoshidaA) x).re) +
          canonicalOddTailProfile f := by
            funext x
            simp only [r, centeredRescale, Submodule.coe_add, Pi.add_apply,
              Complex.add_re, Pi.add_apply, canonicalOddTailProfile]
      _ = factorTwoOddLowSynthesis o + canonicalOddTailProfile f := by
        rw [canonicalOddRealLowPeriodicCore_profile]
  have hbridge :=
    clippedCriticalFormValue_eq_endpoint_mul_clean_of_real_endpoints_zero
      r hrReal hrNeg hrPos
  have hform : 0 ≤ clippedCriticalFormValue yoshidaA yoshidaA_pos
      (r : YoshidaClippedSmooth yoshidaA) := by
    let c : YoshidaOddIndex → ℂ := fun j ↦ o j
    by_cases hne : c ≠ 0 ∨ f ≠ 0
    · have hpos := clippedCriticalForm_oddLow_add_tail_re_pos c f hne
      simpa only [clippedCriticalFormValue, r,
        canonicalOddRealLowPeriodicCore_toSmooth, Submodule.coe_add,
        c] using hpos.le
    · push_neg at hne
      obtain ⟨hc, hf⟩ := hne
      have ho : o = 0 := by
        funext j
        have hj := congrFun hc j
        have hjRe := congrArg Complex.re hj
        simpa only [c, Complex.ofReal_re, map_zero] using hjRe
      have hrzero : r = 0 := by
        dsimp only [r]
        rw [ho, hf]
        classical
        simp [canonicalOddRealLowPeriodicCore]
      rw [hrzero]
      simp [clippedCriticalFormValue]
  change clippedCriticalFormValue yoshidaA yoshidaA_pos
      (r : YoshidaClippedSmooth yoshidaA) =
    yoshidaA * yoshidaEndpointOddCleanQuadratic
      (centeredRescale yoshidaA (fun x ↦
        ((r : YoshidaClippedSmooth yoshidaA) x).re)) at hbridge
  rw [hprofile] at hbridge
  rw [hbridge] at hform
  nlinarith [yoshidaA_pos]

/-- At zero phase, the literal canonical low-plus-tail physical form is
nonnegative by the global clean even and odd production theorems. -/
theorem canonicalPhasePhysicalLowTailValue_zero_phase_nonneg
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) :
    0 ≤ canonicalPhasePhysicalLowTailValue cReal cImag x 0 0 := by
  let er : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
    canonicalEvenRealLowPointwise
        (canonicalPhaseLowEvenCoefficients cReal) +
      canonicalEvenTailPointwise (evenTailRealPart x.fst.toV)
  let ei : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
    canonicalEvenRealLowPointwise
        (canonicalPhaseLowEvenCoefficients cImag) +
      canonicalEvenTailPointwise (evenTailImagPart x.fst.toV)
  have herReal : ∀ t : ℝ,
      ((((er.1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) t).im = 0) := by
    intro t
    change (((canonicalEvenRealLowPeriodicCore
        (canonicalPhaseLowEvenCoefficients cReal) :
          YoshidaClippedSmooth yoshidaA) t) +
      evenOneNinetyNineTailToClippedSmooth
        (evenTailRealPart x.fst.toV) t).im = 0
    rw [Complex.add_im, evenTailRealPart_apply]
    simp only [Complex.ofReal_im, add_zero,
      canonicalEvenRealLowPeriodicCore_toSmooth, Submodule.coe_sum,
      Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
      zero_mul, evenLowMode_im_zero,
      mul_zero]
    exact Finset.sum_eq_zero fun _ _ ↦ rfl
  have heiReal : ∀ t : ℝ,
      ((((ei.1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) t).im = 0) := by
    intro t
    change (((canonicalEvenRealLowPeriodicCore
        (canonicalPhaseLowEvenCoefficients cImag) :
          YoshidaClippedSmooth yoshidaA) t) +
      evenOneNinetyNineTailToClippedSmooth
        (evenTailImagPart x.fst.toV) t).im = 0
    rw [Complex.add_im, evenTailImagPart_apply]
    simp only [Complex.ofReal_im, add_zero,
      canonicalEvenRealLowPeriodicCore_toSmooth, Submodule.coe_sum,
      Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
      zero_mul, evenLowMode_im_zero,
      mul_zero]
    exact Finset.sum_eq_zero fun _ _ ↦ rfl
  have her := boundaryContinuousEvenProfile_clean_nonneg er herReal
  have hei := boundaryContinuousEvenProfile_clean_nonneg ei heiReal
  have hor := oddLow_add_tail_clean_nonneg
    (canonicalPhaseLowOddCoefficients cReal)
    (oddTailRealPart x.snd.toV) (by
      intro t
      change (((((oddTenTailToClippedSmooth x.snd.toV t).re : ℝ) :
        ℂ)).im) = 0
      simp)
  have hoi := oddLow_add_tail_clean_nonneg
    (canonicalPhaseLowOddCoefficients cImag)
    (oddTailImagPart x.snd.toV) (by
      intro t
      change (((((oddTenTailToClippedSmooth x.snd.toV t).im : ℝ) :
        ℂ)).im) = 0
      simp)
  have her' : 0 ≤ yoshidaEndpointOddCleanQuadratic
      (factorTwoBoundaryCanonicalEvenLowProfile
          (canonicalPhaseLowEvenCoefficients cReal) +
        canonicalPhaseTailEvenRealProfile x) := by
    simpa only [er, factorTwoBoundaryCanonicalEvenLowProfile,
      canonicalPhaseTailEvenRealProfile, boundaryCanonicalEvenTailProfile,
      boundaryContinuousEvenProfile_add] using her
  have hei' : 0 ≤ yoshidaEndpointOddCleanQuadratic
      (factorTwoBoundaryCanonicalEvenLowProfile
          (canonicalPhaseLowEvenCoefficients cImag) +
        canonicalPhaseTailEvenImagProfile x) := by
    simpa only [ei, factorTwoBoundaryCanonicalEvenLowProfile,
      canonicalPhaseTailEvenImagProfile, boundaryCanonicalEvenTailProfile,
      boundaryContinuousEvenProfile_add] using hei
  have hor' : 0 ≤ yoshidaEndpointOddCleanQuadratic
      (factorTwoOddLowSynthesis (canonicalPhaseLowOddCoefficients cReal) +
        canonicalPhaseTailOddRealProfile x) := by
    simpa only [canonicalPhaseTailOddRealProfile] using hor
  have hoi' : 0 ≤ yoshidaEndpointOddCleanQuadratic
      (factorTwoOddLowSynthesis (canonicalPhaseLowOddCoefficients cImag) +
        canonicalPhaseTailOddImagProfile x) := by
    simpa only [canonicalPhaseTailOddImagProfile] using hoi
  unfold canonicalPhasePhysicalLowTailValue factorTwoEndpointChannelPhase
    factorTwoEndpointChannelCleanSum
  simp only [zero_mul]
  nlinarith [her', hor', hei', hoi']

set_option maxHeartbeats 800000 in
/-- The canonical inverse-free low-tail corrected Gram is positive
semidefinite at the clean phase.  This is an infinite-dimensional Schur
statement obtained from global clean positivity, not a finite certificate. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_zero_phase_posSemidef :
    Matrix.PosSemidef
      (completedCanonicalPhaseLowTailRealCorrectedGram 0 0 (by norm_num)) := by
  rw [completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_energy]
  intro c
  let r := canonicalPhaseLowTailRealRieszCombination c 0 0 (by norm_num)
  have hcore (x : CanonicalPhaseTailCore) :
      0 ≤ c ⬝ᵥ (canonicalPhaseLowMatrix 0 0 *ᵥ c) +
          2 * ∑ k, c k *
            completedCanonicalPhaseLowBasisTailRealFunctional
              k 0 0 (by norm_num) (x : CanonicalPhaseTailCompletion) +
          completedCanonicalPhaseTailBilinear 0 0 (by norm_num)
            (x : CanonicalPhaseTailCompletion)
            (x : CanonicalPhaseTailCompletion) := by
    have hphysical := canonicalPhasePhysicalLowTailValue_zero_phase_nonneg
      c 0 x
    have hassembly := canonicalPhasePhysicalLowTailValue_eq_schurQuadratic
      c 0 x 0 0 (by norm_num)
    unfold CanonicalPhasePhysicalLowTailAssembly at hassembly
    unfold canonicalPhaseLowTailSchurQuadratic at hassembly
    dsimp only at hassembly
    rw [canonicalPhaseLowRealImagMatrix_quadratic,
      completedCanonicalPhaseLowRealImagFunctional_sum] at hassembly
    simp only [zero_dotProduct] at hassembly
    rw [hassembly] at hphysical
    simpa using hphysical
  have hall (z : CanonicalPhaseTailCompletion) :
      0 ≤ c ⬝ᵥ (canonicalPhaseLowMatrix 0 0 *ᵥ c) +
          2 * ∑ k, c k *
            completedCanonicalPhaseLowBasisTailRealFunctional
              k 0 0 (by norm_num) z +
          completedCanonicalPhaseTailBilinear 0 0 (by norm_num) z z := by
    refine UniformSpace.Completion.induction_on z
      (isClosed_le continuous_const (by fun_prop)) ?_
    intro x
    exact hcore x
  have hr := hall (-r)
  have hrepr : completedCanonicalPhaseTailBilinear 0 0 (by norm_num)
      r r = ∑ k, c k *
        completedCanonicalPhaseLowBasisTailRealFunctional
          k 0 0 (by norm_num) r := by
    simpa only [r] using
      completedCanonicalPhaseTailBilinear_realRieszCombination_apply
      c 0 0 (by norm_num) r
  have hnegFunctional :
      ∑ k, c k * completedCanonicalPhaseLowBasisTailRealFunctional
          k 0 0 (by norm_num) (-r) =
        -completedCanonicalPhaseTailBilinear 0 0 (by norm_num) r r := by
    simp only [map_neg, mul_neg,
      Finset.sum_neg_distrib, hrepr]
  have hnegBilinear : completedCanonicalPhaseTailBilinear 0 0 (by norm_num)
      (-r) (-r) = completedCanonicalPhaseTailBilinear 0 0 (by norm_num)
        r r := by
    simp
  rw [hnegFunctional, hnegBilinear] at hr
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalCleanSchurStructural
