import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointChannelRadius
import ArithmeticHodge.Analysis.YoshidaEndpointOddLowGramExpansion
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailBoundaryReductionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural

set_option autoImplicit false
set_option maxRecDepth 100000

open Complex Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailProductionClosureStructural

noncomputable section

open ArithmeticHodge.Analysis
open FormSpace
open MultiplicativeWeil
open UnitIntervalLogEnergyAffine
open YoshidaCoercivityNumerics
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointScaledCorrelation
open YoshidaEvenHomogeneousCoercivity
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
open YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyClosureStructural
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyStructural
open YoshidaFactorTwoPhaseCanonicalLowTailBoundaryReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseEndpointAdaptedTail
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddRealDecomposition
open YoshidaFactorTwoPhaseTailRealImagStructural
open YoshidaOddHomogeneousCoercivity
open YoshidaOddInfiniteSchur
open YoshidaParityRecombination
open YoshidaWeightedTailBounds

/-!
# Production closure of the canonical low--tail phase

This file transports a phase-uniform nonnegativity theorem on the canonical
`200 + 10 + tail` carrier to the two reflection-parity blocks used by the
production factor-two pencil.  It contains no new estimate: the only inputs
are the canonical physical phase hypothesis and the existing exact crop,
parity, Fourier low--tail, and numerical-radius equivalences.
-/

/-- Put a pair of algebraic real Fourier tails into the real coordinate of
the shared complex canonical tail carrier. -/
def canonicalPhaseTailCoreOfRealTails
    (e : YoshidaEvenOneNinetyNineTail) (o : YoshidaOddTenTail) :
    CanonicalPhaseTailCore :=
  WithLp.toLp 2
    ((FormSpace.of e : EvenPhaseTailFormSpace),
      (FormSpace.of o : OddPhaseTailFormSpace))

private theorem evenTailRealPart_eq_self_of_real
    (e : YoshidaEvenOneNinetyNineTail)
    (he : ∀ x : ℝ, (evenOneNinetyNineTailToClippedSmooth e x).im = 0) :
    evenTailRealPart e = e := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change evenOneNinetyNineTailToClippedSmooth (evenTailRealPart e) x =
    evenOneNinetyNineTailToClippedSmooth e x
  rw [evenTailRealPart_apply]
  apply Complex.ext
  · simp
  · change 0 = (evenOneNinetyNineTailToClippedSmooth e x).im
    exact (he x).symm

private theorem evenTailImagPart_eq_zero_of_real
    (e : YoshidaEvenOneNinetyNineTail)
    (he : ∀ x : ℝ, (evenOneNinetyNineTailToClippedSmooth e x).im = 0) :
    evenTailImagPart e = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change evenOneNinetyNineTailToClippedSmooth (evenTailImagPart e) x = 0
  rw [evenTailImagPart_apply]
  apply Complex.ext
  · change (evenOneNinetyNineTailToClippedSmooth e x).im = 0
    exact he x
  · simp

private theorem oddTailRealPart_eq_self_of_real
    (o : YoshidaOddTenTail)
    (ho : ∀ x : ℝ, (oddTenTailToClippedSmooth o x).im = 0) :
    oddTailRealPart o = o := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change oddTenTailToClippedSmooth (oddTailRealPart o) x =
    oddTenTailToClippedSmooth o x
  rw [oddTailRealPart_apply]
  apply Complex.ext
  · simp
  · change 0 = (oddTenTailToClippedSmooth o x).im
    exact (ho x).symm

private theorem oddTailImagPart_eq_zero_of_real
    (o : YoshidaOddTenTail)
    (ho : ∀ x : ℝ, (oddTenTailToClippedSmooth o x).im = 0) :
    oddTailImagPart o = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change oddTenTailToClippedSmooth (oddTailImagPart o) x = 0
  rw [oddTailImagPart_apply]
  apply Complex.ext
  · change (oddTenTailToClippedSmooth o x).im = 0
    exact ho x
  · simp

@[simp] private theorem boundaryCanonicalEvenTailProfile_zero :
    boundaryCanonicalEvenTailProfile (0 : YoshidaEvenOneNinetyNineTail) = 0 := by
  unfold boundaryCanonicalEvenTailProfile
  simpa only [canonicalEvenTailPointwise] using
    boundaryContinuousEvenProfile_zero

@[simp] private theorem canonicalOddTailProfile_zero :
    canonicalOddTailProfile (0 : YoshidaOddTenTail) = 0 := by
  funext x
  unfold canonicalOddTailProfile centeredRescale
  simp

theorem canonicalPhaseTailCoreOfRealTails_profiles
    (e : YoshidaEvenOneNinetyNineTail) (o : YoshidaOddTenTail)
    (he : ∀ x : ℝ, (evenOneNinetyNineTailToClippedSmooth e x).im = 0)
    (ho : ∀ x : ℝ, (oddTenTailToClippedSmooth o x).im = 0) :
    canonicalPhaseTailEvenRealProfile
        (canonicalPhaseTailCoreOfRealTails e o) =
          boundaryCanonicalEvenTailProfile e ∧
      canonicalPhaseTailOddRealProfile
        (canonicalPhaseTailCoreOfRealTails e o) =
          canonicalOddTailProfile o ∧
      canonicalPhaseTailEvenImagProfile
        (canonicalPhaseTailCoreOfRealTails e o) = 0 ∧
      canonicalPhaseTailOddImagProfile
        (canonicalPhaseTailCoreOfRealTails e o) = 0 := by
  change boundaryCanonicalEvenTailProfile (evenTailRealPart e) =
        boundaryCanonicalEvenTailProfile e ∧
      canonicalOddTailProfile (oddTailRealPart o) = canonicalOddTailProfile o ∧
      boundaryCanonicalEvenTailProfile (evenTailImagPart e) = 0 ∧
      canonicalOddTailProfile (oddTailImagPart o) = 0
  rw [show evenTailRealPart e = e from
      evenTailRealPart_eq_self_of_real e he,
    show oddTailRealPart o = o from oddTailRealPart_eq_self_of_real o ho,
    show evenTailImagPart e = 0 from
      evenTailImagPart_eq_zero_of_real e he,
    show oddTailImagPart o = 0 from oddTailImagPart_eq_zero_of_real o ho]
  simp

private theorem yoshidaEndpointOddCleanQuadratic_zero :
    yoshidaEndpointOddCleanQuadratic (0 : ℝ → ℝ) = 0 := by
  have h := yoshidaEndpointOddCleanQuadratic_const_mul (fun _ : ℝ ↦ 1) 0
  norm_num at h
  change yoshidaEndpointOddCleanQuadratic (fun _ : ℝ ↦ 0) = 0
  exact h

private theorem factorTwoCenteredSymmetricPerturbation_zero :
    factorTwoCenteredSymmetricPerturbation (0 : ℝ → ℝ) = 0 := by
  have h := factorTwoCenteredSymmetricPerturbation_smul
    0 (fun _ : ℝ ↦ 1)
  norm_num at h
  exact h

private theorem factorTwoEndpointChannelPhase_zero_zero (a b : ℝ) :
    factorTwoEndpointChannelPhase (0 : ℝ → ℝ) (0 : ℝ → ℝ) a b = 0 := by
  unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
  rw [yoshidaEndpointOddCleanQuadratic_zero,
    factorTwoCenteredSymmetricPerturbation_zero,
    factorTwoCenteredAlternatingCoupling_self]
  ring

@[simp] private theorem factorTwoBoundaryCanonicalEvenLowProfile_zero :
    factorTwoBoundaryCanonicalEvenLowProfile
      (0 : YoshidaEvenIndex → ℝ) = 0 := by
  unfold factorTwoBoundaryCanonicalEvenLowProfile
  have hzero : canonicalEvenRealLowPointwise
      (0 : YoshidaEvenIndex → ℝ) = 0 := by
    apply Subtype.ext
    change canonicalEvenRealLowPeriodicCore
      (0 : YoshidaEvenIndex → ℝ) = 0
    classical
    simp [canonicalEvenRealLowPeriodicCore]
  rw [hzero, boundaryContinuousEvenProfile_zero]

@[simp] private theorem factorTwoOddLowSynthesis_zero :
    factorTwoOddLowSynthesis (0 : YoshidaOddIndex → ℝ) = 0 := by
  funext x
  unfold factorTwoOddLowSynthesis factorTwoCenteredOddLowProfile
  simp

/-- Uniform nonnegativity of the assembled canonical physical phase closes
the phase form for every pointwise-real periodic even/odd source pair. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_canonicalPhysical
    (hcanonical : ∀
      (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
      (x : CanonicalPhaseTailCore) (a b : ℝ)
      (_hphase : a ^ 2 + b ^ 2 ≤ 1),
      CanonicalPhasePhysicalLowTailNonnegative cReal cImag x a b)
    (ge : YoshidaPeriodicEvenCore) (go : YoshidaPeriodicOddCore)
    (heReal : ∀ x : ℝ,
      ((((ge : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0)
    (heEndpoint :
      (((ge : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) yoshidaA = 0))
    (hoReal : ∀ x : ℝ,
      ((((go : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0) :
    ∀ a b : ℝ, a ^ 2 + b ^ 2 ≤ 1 →
      0 ≤ factorTwoEndpointChannelPhase
        (centeredRescale yoshidaA (fun x ↦
          (((ge : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) x).re))
        (centeredRescale yoshidaA (fun x ↦
          (((go : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) x).re)) a b := by
  intro a b hphase
  obtain ⟨ce, re, _heDecomp, hreReal, heProfiles⟩ :=
    exists_periodicEvenCore_real_boundaryContinuous_low_add_tail
      ge heReal heEndpoint
  obtain ⟨co, ro, hoDecomp, hroReal, _hroNeg, _hroPos⟩ :=
    exists_periodicOddCore_real_low_add_tail go hoReal
  let c : FactorTwoPhaseLowIndex → ℝ :=
    factorTwoPhaseLowCoefficients ce co
  let x : CanonicalPhaseTailCore :=
    canonicalPhaseTailCoreOfRealTails re ro
  have hprofiles := canonicalPhaseTailCoreOfRealTails_profiles
    re ro hreReal hroReal
  rcases hprofiles with ⟨hxER, hxOR, hxEI, hxOI⟩
  have hoProfiles := centeredOddProfile_eq_canonicalLow_add_tail
    go co ro hoDecomp
  have hnonneg := hcanonical c 0 x a b hphase
  unfold CanonicalPhasePhysicalLowTailNonnegative at hnonneg
  unfold canonicalPhasePhysicalLowTailValue at hnonneg
  have hcEven : canonicalPhaseLowEvenCoefficients c = ce := by rfl
  have hcOdd : canonicalPhaseLowOddCoefficients c = co := by rfl
  have hzeroEven : canonicalPhaseLowEvenCoefficients
      (0 : FactorTwoPhaseLowIndex → ℝ) = 0 := by rfl
  have hzeroOdd : canonicalPhaseLowOddCoefficients
      (0 : FactorTwoPhaseLowIndex → ℝ) = 0 := by rfl
  rw [hcEven, hcOdd, hzeroEven, hzeroOdd, hxER, hxOR, hxEI, hxOI,
    factorTwoBoundaryCanonicalEvenLowProfile_zero,
    factorTwoOddLowSynthesis_zero, zero_add,
    factorTwoEndpointChannelPhase_zero_zero,
    add_zero] at hnonneg
  rw [← heProfiles, hoProfiles]
  exact hnonneg

private theorem periodicCoreEvenPart_real_of_real
    (r : YoshidaClippedPeriodicCore yoshidaA)
    (hr : ∀ x : ℝ,
      (((r : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0)
    (x : ℝ) :
    (((periodicCoreEvenPart r : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) x).im = 0 := by
  simp only [periodicCoreEvenPart_toSmooth_apply]
  norm_num [Complex.mul_im, hr x, hr (-x)]

private theorem periodicCoreOddPart_real_of_real
    (r : YoshidaClippedPeriodicCore yoshidaA)
    (hr : ∀ x : ℝ,
      (((r : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0)
    (x : ℝ) :
    (((periodicCoreOddPart r : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) x).im = 0 := by
  simp only [periodicCoreOddPart_toSmooth_apply]
  norm_num [Complex.mul_im, hr x, hr (-x)]

private theorem periodicCoreEvenPart_endpoint_zero
    (r : YoshidaClippedPeriodicCore yoshidaA)
    (hneg : ((r : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hpos : ((r : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) yoshidaA = 0) :
    ((periodicCoreEvenPart r : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) yoshidaA = 0 := by
  simp only [periodicCoreEvenPart_toSmooth_apply]
  rw [hpos, hneg]
  simp

private theorem centeredRescale_periodicCoreEvenPart
    (r : YoshidaClippedPeriodicCore yoshidaA) :
    centeredRescale yoshidaA (fun x ↦
      ((((periodicCoreEvenPart r : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).re)) =
      factorTwoReflectionEvenPart
        (centeredRescale yoshidaA (fun x ↦
          (((r : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) x).re)) := by
  funext x
  unfold centeredRescale factorTwoReflectionEvenPart
  simp only [periodicCoreEvenPart_toSmooth_apply]
  rw [show yoshidaA * -x = -(yoshidaA * x) by ring]
  norm_num [Complex.mul_re]
  ring

private theorem centeredRescale_periodicCoreOddPart
    (r : YoshidaClippedPeriodicCore yoshidaA) :
    centeredRescale yoshidaA (fun x ↦
      ((((periodicCoreOddPart r : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).re)) =
      factorTwoReflectionOddPart
        (centeredRescale yoshidaA (fun x ↦
          (((r : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) x).re)) := by
  funext x
  unfold centeredRescale factorTwoReflectionOddPart
  simp only [periodicCoreOddPart_toSmooth_apply]
  rw [show yoshidaA * -x = -(yoshidaA * x) by ring]
  norm_num [Complex.mul_re]
  ring

private theorem centeredRescale_criticalPullbackCrop_eq
    (g : BombieriTest)
    (hsupport : YoshidaCriticalPullbackSupported yoshidaA g) :
    let crop : YoshidaClippedSmooth yoshidaA :=
      yoshidaCriticalPullbackCropLinear yoshidaA g
    let r : YoshidaClippedPeriodicCore yoshidaA :=
      ⟨crop, yoshidaCriticalPullbackCrop_mem_periodicCore_structural
        yoshidaA_pos g hsupport⟩
    centeredRescale yoshidaA (fun x ↦
      (((r : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).re) =
      factorTwoCenteredProfile g := by
  dsimp only
  have hcrop :=
    yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hsupport
  funext x
  unfold centeredRescale factorTwoCenteredProfile
  change (yoshidaCriticalPullbackCropLinear yoshidaA g
      (yoshidaA * x)).re =
    (g.logarithmicPullbackSchwartz (1 / 2) (yoshidaA * x)).re
  exact congrArg Complex.re (congrFun hcrop (yoshidaA * x))

/-- The canonical physical theorem transports exactly to the production
even--odd reflection channel of any two real supported pullbacks. -/
theorem factorTwoEndpointChannelPhase_reflectionEvenOdd_nonneg_of_canonicalPhysical
    (hcanonical : ∀
      (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
      (x : CanonicalPhaseTailCore) (a b : ℝ)
      (_hphase : a ^ 2 + b ^ 2 ≤ 1),
      CanonicalPhasePhysicalLowTailNonnegative cReal cImag x a b)
    (gu gv : BombieriTest)
    (huSupport : YoshidaCriticalPullbackSupported yoshidaA gu)
    (hvSupport : YoshidaCriticalPullbackSupported yoshidaA gv)
    (huReal : ∀ x : ℝ,
      (gu.logarithmicPullbackSchwartz (1 / 2) x).im = 0)
    (hvReal : ∀ x : ℝ,
      (gv.logarithmicPullbackSchwartz (1 / 2) x).im = 0) :
    ∀ a b : ℝ, a ^ 2 + b ^ 2 ≤ 1 →
      0 ≤ factorTwoEndpointChannelPhase
        (factorTwoReflectionEvenPart (factorTwoCenteredProfile gu))
        (factorTwoReflectionOddPart (factorTwoCenteredProfile gv)) a b := by
  let cropU : YoshidaClippedSmooth yoshidaA :=
    yoshidaCriticalPullbackCropLinear yoshidaA gu
  have hmemU : cropU ∈ yoshidaClippedPeriodicCoreSubmodule yoshidaA := by
    simpa only [cropU] using
      yoshidaCriticalPullbackCrop_mem_periodicCore_structural
        yoshidaA_pos gu huSupport
  let rU : YoshidaClippedPeriodicCore yoshidaA := ⟨cropU, hmemU⟩
  have hcropU : (cropU : ℝ → ℂ) =
      gu.logarithmicPullbackSchwartz (1 / 2) := by
    simpa only [cropU] using
      yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz huSupport
  have hrUReal : ∀ x : ℝ,
      (((rU : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    change (cropU x).im = 0
    rw [show cropU x = gu.logarithmicPullbackSchwartz (1 / 2) x by
      exact congrFun hcropU x]
    exact huReal x
  obtain ⟨huNeg, huPos⟩ :=
    criticalPullback_endpoints_zero_of_supported gu huSupport
  have hrUNeg : ((rU : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0 := by
    change cropU (-yoshidaA) = 0
    rw [show cropU (-yoshidaA) =
        gu.logarithmicPullbackSchwartz (1 / 2) (-yoshidaA) by
      exact congrFun hcropU (-yoshidaA), huNeg]
  have hrUPos : ((rU : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) yoshidaA = 0 := by
    change cropU yoshidaA = 0
    rw [show cropU yoshidaA =
        gu.logarithmicPullbackSchwartz (1 / 2) yoshidaA by
      exact congrFun hcropU yoshidaA, huPos]
  let cropV : YoshidaClippedSmooth yoshidaA :=
    yoshidaCriticalPullbackCropLinear yoshidaA gv
  have hmemV : cropV ∈ yoshidaClippedPeriodicCoreSubmodule yoshidaA := by
    simpa only [cropV] using
      yoshidaCriticalPullbackCrop_mem_periodicCore_structural
        yoshidaA_pos gv hvSupport
  let rV : YoshidaClippedPeriodicCore yoshidaA := ⟨cropV, hmemV⟩
  have hcropV : (cropV : ℝ → ℂ) =
      gv.logarithmicPullbackSchwartz (1 / 2) := by
    simpa only [cropV] using
      yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hvSupport
  have hrVReal : ∀ x : ℝ,
      (((rV : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    change (cropV x).im = 0
    rw [show cropV x = gv.logarithmicPullbackSchwartz (1 / 2) x by
      exact congrFun hcropV x]
    exact hvReal x
  let ge : YoshidaPeriodicEvenCore :=
    ⟨periodicCoreEvenPart rU, periodicCoreEvenPart_mem_evenCore rU⟩
  let go : YoshidaPeriodicOddCore :=
    ⟨periodicCoreOddPart rV, periodicCoreOddPart_mem_oddCore rV⟩
  have hgeReal : ∀ x : ℝ,
      ((((ge : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0 := by
    intro x
    exact periodicCoreEvenPart_real_of_real rU hrUReal x
  have hgoReal : ∀ x : ℝ,
      ((((go : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0 := by
    intro x
    exact periodicCoreOddPart_real_of_real rV hrVReal x
  have hgeEndpoint :
      (((ge : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) yoshidaA = 0) := by
    exact periodicCoreEvenPart_endpoint_zero rU hrUNeg hrUPos
  have hphase := factorTwoEndpointChannelPhase_nonneg_of_canonicalPhysical
    hcanonical ge go hgeReal hgeEndpoint hgoReal
  have hrawU : centeredRescale yoshidaA (fun x ↦
      (((rU : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).re) =
      factorTwoCenteredProfile gu := by
    simpa only [cropU, rU] using
      centeredRescale_criticalPullbackCrop_eq gu huSupport
  have hrawV : centeredRescale yoshidaA (fun x ↦
      (((rV : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).re) =
      factorTwoCenteredProfile gv := by
    simpa only [cropV, rV] using
      centeredRescale_criticalPullbackCrop_eq gv hvSupport
  have hprofileU : centeredRescale yoshidaA (fun x ↦
      (((ge : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).re) =
      factorTwoReflectionEvenPart (factorTwoCenteredProfile gu) := by
    rw [show centeredRescale yoshidaA (fun x ↦
        (((ge : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) x).re) =
        factorTwoReflectionEvenPart
          (centeredRescale yoshidaA (fun x ↦
            (((rU : YoshidaClippedPeriodicCore yoshidaA) :
              YoshidaClippedSmooth yoshidaA) x).re)) by
      simpa only [ge] using centeredRescale_periodicCoreEvenPart rU,
      hrawU]
  have hprofileV : centeredRescale yoshidaA (fun x ↦
      (((go : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).re) =
      factorTwoReflectionOddPart (factorTwoCenteredProfile gv) := by
    rw [show centeredRescale yoshidaA (fun x ↦
        (((go : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) x).re) =
        factorTwoReflectionOddPart
          (centeredRescale yoshidaA (fun x ↦
            (((rV : YoshidaClippedPeriodicCore yoshidaA) :
              YoshidaClippedSmooth yoshidaA) x).re)) by
      simpa only [go] using centeredRescale_periodicCoreOddPart rV,
      hrawV]
  simpa only [hprofileU, hprofileV] using hphase

/-- Both opposite-reflection-parity production blocks inherit nonnegativity
from the uniform canonical physical phase theorem.  The odd--even block is
the even--odd theorem for the swapped profiles and the reflected phase
coordinate `b ↦ -b`. -/
theorem factorTwoReflectionChannelPencils_nonneg_of_canonicalPhysical
    (hcanonical : ∀
      (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
      (x : CanonicalPhaseTailCore) (a b : ℝ)
      (_hphase : a ^ 2 + b ^ 2 ≤ 1),
      CanonicalPhasePhysicalLowTailNonnegative cReal cImag x a b)
    (gu gv : BombieriTest)
    (huSupport : YoshidaCriticalPullbackSupported yoshidaA gu)
    (hvSupport : YoshidaCriticalPullbackSupported yoshidaA gv)
    (huReal : ∀ x : ℝ,
      (gu.logarithmicPullbackSchwartz (1 / 2) x).im = 0)
    (hvReal : ∀ x : ℝ,
      (gv.logarithmicPullbackSchwartz (1 / 2) x).im = 0) :
    (∀ r s : ℝ, 0 ≤ factorTwoReflectionEvenOddChannelPencil
      (factorTwoCenteredProfile gu) (factorTwoCenteredProfile gv) r s) ∧
    (∀ r s : ℝ, 0 ≤ factorTwoReflectionOddEvenChannelPencil
      (factorTwoCenteredProfile gu) (factorTwoCenteredProfile gv) r s) := by
  let eu := factorTwoReflectionEvenPart (factorTwoCenteredProfile gu)
  let ou := factorTwoReflectionOddPart (factorTwoCenteredProfile gu)
  let ev := factorTwoReflectionEvenPart (factorTwoCenteredProfile gv)
  let ov := factorTwoReflectionOddPart (factorTwoCenteredProfile gv)
  have hEvenOddPhase : ∀ a b : ℝ, a ^ 2 + b ^ 2 ≤ 1 →
      0 ≤ factorTwoEndpointChannelPhase eu ov a b := by
    simpa only [eu, ov] using
      factorTwoEndpointChannelPhase_reflectionEvenOdd_nonneg_of_canonicalPhysical
        hcanonical gu gv huSupport hvSupport huReal hvReal
  have hEvenOddRadius :=
    (factorTwoEndpointChannel_phase_nonneg_iff_radius eu ov).mp
      hEvenOddPhase
  have hEvenOddPencil :=
    (factorTwoEndpointChannelPencil_nonneg_iff_radius eu ov).mpr
      hEvenOddRadius
  have hOddEvenPhase : ∀ a b : ℝ, a ^ 2 + b ^ 2 ≤ 1 →
      0 ≤ factorTwoEndpointChannelPhase ou ev a b := by
    intro a b hphase
    rw [factorTwoEndpointChannelPhase_swap]
    apply
      factorTwoEndpointChannelPhase_reflectionEvenOdd_nonneg_of_canonicalPhysical
        hcanonical gv gu hvSupport huSupport hvReal huReal a (-b)
    simpa only [neg_sq] using hphase
  have hOddEvenRadius :=
    (factorTwoEndpointChannel_phase_nonneg_iff_radius ou ev).mp
      hOddEvenPhase
  have hOddEvenPencil :=
    (factorTwoEndpointChannelPencil_nonneg_iff_radius ou ev).mpr
      hOddEvenRadius
  constructor
  · intro r s
    rw [factorTwoReflectionEvenOddChannelPencil_eq_oppositeParity]
    exact hEvenOddPencil r s
  · intro r s
    rw [factorTwoReflectionOddEvenChannelPencil_eq_oppositeParity]
    exact hOddEvenPencil r s

/-- For a centered ratio-two Bombieri seed, both production reflection
blocks are nonnegative once the canonical physical phase is uniformly
nonnegative on the closed disk. -/
theorem logCentered_reflectionChannelPencils_nonneg_of_canonicalPhysical
    (hcanonical : ∀
      (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
      (x : CanonicalPhaseTailCore) (phaseRe phaseIm : ℝ)
      (_hphase : phaseRe ^ 2 + phaseIm ^ 2 ≤ 1),
      CanonicalPhasePhysicalLowTailNonnegative
        cReal cImag x phaseRe phaseIm)
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    let gc := normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g
    let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
    let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
    (∀ r s : ℝ, 0 ≤ factorTwoReflectionEvenOddChannelPencil u v r s) ∧
      (∀ r s : ℝ,
        0 ≤ factorTwoReflectionOddEvenChannelPencil u v r s) := by
  let gc := normalizedDilation (logarithmicCenter a b)
    (logarithmicCenter_pos a b) g
  let gu := bombieriRealPartTest gc
  let gv := bombieriImagPartTest gc
  have hcritical : YoshidaCriticalPullbackSupported yoshidaA gc := by
    simpa only [gc] using
      logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaEndpointA
        g ha hab hsupport hratio
  have huSupport : YoshidaCriticalPullbackSupported yoshidaA gu :=
    bombieriRealPartTest_criticalPullbackSupported gc hcritical
  have hvSupport : YoshidaCriticalPullbackSupported yoshidaA gv :=
    bombieriImagPartTest_criticalPullbackSupported gc hcritical
  have huReal : ∀ x : ℝ,
      (gu.logarithmicPullbackSchwartz (1 / 2) x).im = 0 :=
    bombieriRealPartTest_criticalPullback_im_eq_zero gc
  have hvReal : ∀ x : ℝ,
      (gv.logarithmicPullbackSchwartz (1 / 2) x).im = 0 :=
    bombieriImagPartTest_criticalPullback_im_eq_zero gc
  simpa only [gc, gu, gv] using
    factorTwoReflectionChannelPencils_nonneg_of_canonicalPhysical
      hcanonical gu gv huSupport hvSupport huReal hvReal

/-- The two block certificates recombine into the full production
reflection-parity pencil. -/
theorem logCentered_reflectionParityPencil_nonneg_of_canonicalPhysical
    (hcanonical : ∀
      (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
      (x : CanonicalPhaseTailCore) (phaseRe phaseIm : ℝ)
      (_hphase : phaseRe ^ 2 + phaseIm ^ 2 ≤ 1),
      CanonicalPhasePhysicalLowTailNonnegative
        cReal cImag x phaseRe phaseIm)
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    let gc := normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g
    let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
    let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
    ∀ r s : ℝ, 0 ≤ factorTwoReflectionParityPencil u v r s := by
  dsimp only
  obtain ⟨hEvenOdd, hOddEven⟩ :=
    logCentered_reflectionChannelPencils_nonneg_of_canonicalPhysical
      hcanonical g ha hab hsupport hratio
  exact factorTwoReflectionParityPencil_nonneg_of_channels _ _
    hEvenOdd hOddEven

/-- Uniform canonical physical phase nonnegativity therefore proves every
same-seed production member `g + c D₂g` on a ratio-two support cell. -/
theorem bombieriFunctional_twoBump_nonneg_of_canonicalPhysical
    (hcanonical : ∀
      (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
      (x : CanonicalPhaseTailCore) (phaseRe phaseIm : ℝ)
      (_hphase : phaseRe ^ 2 + phaseIm ^ 2 ≤ 1),
      CanonicalPhasePhysicalLowTailNonnegative
        cReal cImag x phaseRe phaseIm)
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    ∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re := by
  apply
    (bombieriFunctional_twoBump_nonneg_iff_logCentered_reflectionParityPencil
      g ha hab hsupport hratio).mpr
  exact logCentered_reflectionParityPencil_nonneg_of_canonicalPhysical
    hcanonical g ha hab hsupport hratio

/-- A uniform reduced corrected-Gram certificate supplies the canonical
physical hypothesis required by the production closure. -/
theorem bombieriFunctional_twoBump_nonneg_of_realCorrectedGram_posSemidef
    (hgram : ∀ (phaseRe phaseIm : ℝ)
      (hphase : phaseRe ^ 2 + phaseIm ^ 2 ≤ 1),
      Matrix.PosSemidef
        (completedCanonicalPhaseLowTailRealCorrectedGram
          phaseRe phaseIm hphase))
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    ∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re := by
  apply bombieriFunctional_twoBump_nonneg_of_canonicalPhysical
    (g := g) (a := a) (b := b) _ ha hab hsupport hratio
  intro cReal cImag x phaseRe phaseIm hphase
  exact
    canonicalPhasePhysicalLowTailValue_nonneg_of_realCorrectedGram_posSemidef
      cReal cImag x phaseRe phaseIm hphase
        (hgram phaseRe phaseIm hphase)

/-- Consequently the remaining circle corrected-Gram theorem, together with
the compiled disk concavity reduction, is already sufficient for universal
same-seed factor-two positivity on every ratio-two support cell. -/
theorem bombieriFunctional_twoBump_nonneg_of_realCorrectedGram_circle
    (hcircle : ∀ (phaseRe phaseIm : ℝ)
      (hphase : phaseRe ^ 2 + phaseIm ^ 2 ≤ 1),
      phaseRe ^ 2 + phaseIm ^ 2 = 1 →
        Matrix.PosSemidef
          (completedCanonicalPhaseLowTailRealCorrectedGram
            phaseRe phaseIm hphase))
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    ∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re := by
  apply bombieriFunctional_twoBump_nonneg_of_realCorrectedGram_posSemidef
    (g := g) (a := a) (b := b) _ ha hab hsupport hratio
  intro phaseRe phaseIm hphase
  exact
    completedCanonicalPhaseLowTailRealCorrectedGram_disk_posSemidef_of_circle
      hcircle phaseRe phaseIm hphase

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailProductionClosureStructural
