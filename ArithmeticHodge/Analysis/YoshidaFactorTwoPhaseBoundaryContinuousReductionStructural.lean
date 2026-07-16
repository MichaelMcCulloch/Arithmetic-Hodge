import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousPhaseCongruenceStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowMatrix

set_option autoImplicit false
set_option maxRecDepth 100000

open Complex Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaEvenHomogeneousCoercivity
open YoshidaEvenInfiniteSchur
open YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseOddRealDecomposition
open YoshidaFactorTwoPhaseRadiusClosure
open YoshidaOddHomogeneousCoercivity
open YoshidaOddInfiniteSchur
open YoshidaParityRecombination
open YoshidaWeightedTailBounds

/-!
# Canonical boundary-continuous phase reduction

This is the production low--tail split on the original Fourier coordinates.
The even tail remains in the full cutoff-`199` carrier, including frequency
`200`; its continuous representative absorbs the endpoint trace without
changing the Fourier vector.  The result exposes the exact finite low phase,
twice the complete mixed block, and the structurally coercive tail phase.
-/

/-- Boundary-continuous profile of the standard real `Fin 200` low block. -/
def boundaryCanonicalEvenLowProfile
    (c : YoshidaEvenIndex → ℝ) : ℝ → ℝ :=
  boundaryContinuousEvenProfile (canonicalEvenRealLowPointwise c)

/-- Boundary-continuous profile of the standard cutoff-`199` even tail. -/
def boundaryCanonicalEvenTailProfile
    (f : YoshidaEvenOneNinetyNineTail) : ℝ → ℝ :=
  boundaryContinuousEvenProfile (canonicalEvenTailPointwise f)

/-- Raw centered profile of the standard cutoff-`10` odd tail. -/
def canonicalOddTailProfile (f : YoshidaOddTenTail) : ℝ → ℝ :=
  centeredRescale yoshidaA (fun x ↦
    (((f : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) x).re)

theorem continuous_boundaryCanonicalEvenLowProfile
    (c : YoshidaEvenIndex → ℝ) :
    Continuous (boundaryCanonicalEvenLowProfile c) := by
  exact continuous_boundaryContinuousEvenProfile
    (canonicalEvenRealLowPointwise c)

theorem continuous_boundaryCanonicalEvenTailProfile
    (f : YoshidaEvenOneNinetyNineTail) :
    Continuous (boundaryCanonicalEvenTailProfile f) := by
  exact continuous_boundaryContinuousEvenProfile
    (canonicalEvenTailPointwise f)

theorem continuous_canonicalOddTailProfile (f : YoshidaOddTenTail) :
    Continuous (canonicalOddTailProfile f) := by
  obtain ⟨hneg, hpos⟩ := oddTenTail_endpoints_zero f
  exact continuous_centeredRescale_re_of_endpoints_zero yoshidaA_pos
    (f : YoshidaClippedPeriodicCore yoshidaA) hneg hpos

/-- Centered rescaling transports the exact real odd Fourier decomposition
to the canonical low synthesis plus its actual odd tail profile. -/
theorem centeredOddProfile_eq_canonicalLow_add_tail
    (g : YoshidaPeriodicOddCore)
    (c : YoshidaOddIndex → ℝ)
    (f : YoshidaOddTenTail)
    (hdecomp :
      (((g : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)) =
        (∑ i, ((c i : ℝ) : ℂ) •
          yoshidaClippedOddLowMode yoshidaA i) +
          oddTenTailToClippedSmooth f) :
    centeredRescale yoshidaA (fun x ↦
        (((g : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) x).re) =
      factorTwoOddLowSynthesis c + canonicalOddTailProfile f := by
  funext x
  have hx := congrArg
    (fun h : YoshidaClippedSmooth yoshidaA ↦ h (yoshidaA * x))
    hdecomp
  have hxRe := congrArg Complex.re hx
  change
    ((((g : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) (yoshidaA * x)).re) =
      (((∑ i, ((c i : ℝ) : ℂ) •
          yoshidaClippedOddLowMode yoshidaA i) +
        oddTenTailToClippedSmooth f) (yoshidaA * x)).re at hxRe
  unfold factorTwoOddLowSynthesis factorTwoCenteredOddLowProfile
    canonicalOddTailProfile
  unfold centeredRescale
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hxRe]
  simp only [Submodule.coe_add, Pi.add_apply, Complex.add_re,
    Submodule.coe_sum, Finset.sum_apply, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change ((((c i : ℝ) : ℂ) *
      yoshidaClippedOddLowMode yoshidaA i (yoshidaA * x)).re) =
    c i * (yoshidaClippedOddLowMode yoshidaA i (yoshidaA * x)).re
  rw [Complex.mul_re, oddLowMode_im_zero]
  simp

/-- Every pointwise-real even/odd seed pair with the production endpoint
condition admits the original canonical `Fin 200 + Fin 10` split.  Its pure
tail phase retains a uniform clean reserve, and the full seed phase is exactly
the finite low phase plus twice the mixed block plus the tail phase. -/
theorem exists_real_canonical_boundary_low_tails_with_phase_decomposition
    (ge : YoshidaPeriodicEvenCore)
    (go : YoshidaPeriodicOddCore)
    (heReal : ∀ x : ℝ,
      ((((ge : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0)
    (heEndpoint :
      (((ge : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) yoshidaA = 0))
    (hoReal : ∀ x : ℝ,
      ((((go : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    ∃ ce : YoshidaEvenIndex → ℝ,
      ∃ co : YoshidaOddIndex → ℝ,
        ∃ re : YoshidaEvenOneNinetyNineTail,
          ∃ ro : YoshidaOddTenTail,
            let eFull := centeredRescale yoshidaA (fun x ↦
              (((ge : YoshidaClippedPeriodicCore yoshidaA) :
                YoshidaClippedSmooth yoshidaA) x).re)
            let oFull := centeredRescale yoshidaA (fun x ↦
              (((go : YoshidaClippedPeriodicCore yoshidaA) :
                YoshidaClippedSmooth yoshidaA) x).re)
            let eLow := boundaryCanonicalEvenLowProfile ce
            let eTail := boundaryCanonicalEvenTailProfile re
            let oLow := factorTwoOddLowSynthesis co
            let oTail := canonicalOddTailProfile ro
            eFull = eLow + eTail ∧
            oFull = oLow + oTail ∧
            (1 / 200 : ℝ) *
                (yoshidaEndpointOddCleanQuadratic eTail +
                  yoshidaEndpointOddCleanQuadratic oTail) ≤
              factorTwoEndpointChannelPhase eTail oTail a b ∧
            factorTwoEndpointChannelPhase eFull oFull a b =
              factorTwoEndpointChannelPhase eLow oLow a b +
                2 * factorTwoEndpointLowTailMixed
                  eLow eTail oLow oTail a b +
              factorTwoEndpointChannelPhase eTail oTail a b := by
  classical
  obtain ⟨ce, re, heDecomp, heTailReal, heProfiles⟩ :=
    exists_periodicEvenCore_real_boundaryContinuous_low_add_tail
      ge heReal heEndpoint
  obtain ⟨co, ro, hoDecomp, hoTailReal, hoNeg, hoPos⟩ :=
    exists_periodicOddCore_real_low_add_tail go hoReal
  let eFull := centeredRescale yoshidaA (fun x ↦
    (((ge : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) x).re)
  let oFull := centeredRescale yoshidaA (fun x ↦
    (((go : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) x).re)
  let eLow := boundaryCanonicalEvenLowProfile ce
  let eTail := boundaryCanonicalEvenTailProfile re
  let oLow := factorTwoOddLowSynthesis co
  let oTail := canonicalOddTailProfile ro
  have heFull : eFull = eLow + eTail := by
    simpa only [eFull, eLow, eTail,
      boundaryCanonicalEvenLowProfile,
      boundaryCanonicalEvenTailProfile] using heProfiles.symm
  have hoFull : oFull = oLow + oTail := by
    simpa only [oFull, oLow, oTail] using
      centeredOddProfile_eq_canonicalLow_add_tail go co ro hoDecomp
  have htail := boundaryContinuous_tail_phase_uniform_clean_reserve
    (re : YoshidaClippedPeriodicCore yoshidaA)
    (ro : YoshidaClippedPeriodicCore yoshidaA)
    re.property ro.property heTailReal hoTailReal a b hphase
  have htail' :
      (1 / 200 : ℝ) *
          (yoshidaEndpointOddCleanQuadratic eTail +
            yoshidaEndpointOddCleanQuadratic oTail) ≤
        factorTwoEndpointChannelPhase eTail oTail a b := by
    simpa only [eTail, oTail, boundaryCanonicalEvenTailProfile,
      canonicalEvenTailPointwise, canonicalOddTailProfile] using htail
  have hsplit := factorTwoEndpointChannelPhase_add_add_eq_low_mixed_tail
    eLow eTail oLow oTail
    (continuous_boundaryCanonicalEvenLowProfile ce)
    (continuous_boundaryCanonicalEvenTailProfile re)
    (continuous_factorTwoOddLowSynthesis co)
    (continuous_canonicalOddTailProfile ro) a b
  rw [← heFull, ← hoFull] at hsplit
  exact ⟨ce, co, re, ro, heFull, hoFull, htail', hsplit⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
