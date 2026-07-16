import ArithmeticHodge.Analysis.LinearFormCompletion
import ArithmeticHodge.Analysis.YoshidaEvenTailLowFunctional
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseAlternatingCoercivity
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointTailBilinearContinuityStructural
import ArithmeticHodge.Analysis.YoshidaOddTailLowFunctional

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural

noncomputable section

open ArithmeticHodge.Analysis
open FormSpace
open UnitIntervalLogEnergyAffine
open YoshidaClippedCircleBridge
open YoshidaClippedCircleFaithful
open YoshidaCoercivityNumerics
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaEndpointHyperbolicBound
open YoshidaEvenHomogeneousCoercivity
open YoshidaEvenTailLowFunctional
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseAlternatingCoercivity
open YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
open YoshidaFactorTwoPhaseBoundaryContinuousCleanPolarizationStructural
open YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousPhaseCongruenceStructural
open YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailMixedCauchyStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseCleanPolarizationCritical
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPhaseEndpointTailBilinearContinuityStructural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddRealDecomposition
open YoshidaFactorTwoPhaseTailCoercivity
open YoshidaFactorTwoPhaseTailRealImagLinearStructural
open YoshidaFactorTwoPhaseTailRealImagStructural
open YoshidaOddHomogeneousCoercivity
open YoshidaOddModeRegularity
open YoshidaOddSpectralMassBridge
open YoshidaOddTailLowFunctional
open YoshidaPointwiseParityCore
open YoshidaRegularKernelSchur
open YoshidaWeightedTailBounds

/-!
# Canonical finite-low functionals on the completed phase tail

Each standard basis vector of the canonical `Fin 200 ⊕ Fin 10` low block
defines a real linear mixed-phase functional on either the real or imaginary
tail coordinate.  This module normalizes those basis profiles, proves the
functionals bounded in the critical product norm, and extends them to the
completed coercive phase-tail space.
-/

/-- Select the even coordinates of one standard coupled low basis vector. -/
def canonicalLowEvenSelector :
    FactorTwoPhaseLowIndex → YoshidaEvenIndex → ℝ
  | Sum.inl i => Pi.single i 1
  | Sum.inr _ => 0

/-- Select the odd coordinates of one standard coupled low basis vector. -/
def canonicalLowOddSelector :
    FactorTwoPhaseLowIndex → YoshidaOddIndex → ℝ
  | Sum.inl _ => 0
  | Sum.inr j => Pi.single j 1

@[simp] theorem factorTwoPhaseLowCoefficients_selectors
    (k : FactorTwoPhaseLowIndex) :
    factorTwoPhaseLowCoefficients
        (canonicalLowEvenSelector k)
        (canonicalLowOddSelector k) =
      Pi.single k 1 := by
  ext q
  cases k with
  | inl i =>
      cases q with
      | inl j =>
          by_cases hij : i = j <;>
            simp [canonicalLowEvenSelector, canonicalLowOddSelector,
              factorTwoPhaseLowCoefficients, Pi.single_apply, hij]
      | inr j =>
          simp [canonicalLowEvenSelector, canonicalLowOddSelector,
            factorTwoPhaseLowCoefficients]
  | inr i =>
      cases q with
      | inl j =>
          simp [canonicalLowEvenSelector, canonicalLowOddSelector,
            factorTwoPhaseLowCoefficients]
      | inr j =>
          by_cases hij : i = j <;>
            simp [canonicalLowEvenSelector, canonicalLowOddSelector,
              factorTwoPhaseLowCoefficients, Pi.single_apply, hij]

/-- Even profile of one canonical coupled low basis vector. -/
def canonicalPhaseLowBasisEvenProfile :
    FactorTwoPhaseLowIndex → ℝ → ℝ
  | Sum.inl i => boundaryContinuousEvenProfile
      (canonicalEvenLowModePointwise i)
  | Sum.inr _ => 0

/-- Odd profile of one canonical coupled low basis vector. -/
def canonicalPhaseLowBasisOddProfile :
    FactorTwoPhaseLowIndex → ℝ → ℝ
  | Sum.inl _ => 0
  | Sum.inr j => factorTwoCenteredOddLowProfile j

@[simp] theorem continuous_canonicalPhaseLowBasisEvenProfile
    (k : FactorTwoPhaseLowIndex) :
    Continuous (canonicalPhaseLowBasisEvenProfile k) := by
  cases k with
  | inl i =>
      exact continuous_boundaryContinuousEvenProfile
        (canonicalEvenLowModePointwise i)
  | inr j => exact continuous_const

@[simp] theorem continuous_canonicalPhaseLowBasisOddProfile
    (k : FactorTwoPhaseLowIndex) :
    Continuous (canonicalPhaseLowBasisOddProfile k) := by
  cases k with
  | inl i => exact continuous_const
  | inr j => exact continuous_factorTwoCenteredOddLowProfile j

theorem canonicalPhaseLowBasisEvenProfile_even
    (k : FactorTwoPhaseLowIndex) :
    Function.Even (canonicalPhaseLowBasisEvenProfile k) := by
  cases k with
  | inl i =>
      exact boundaryContinuousEvenProfile_even
        (canonicalEvenLowModePointwise i)
  | inr j => exact fun _ ↦ rfl

theorem canonicalPhaseLowBasisOddProfile_odd
    (k : FactorTwoPhaseLowIndex) :
    Function.Odd (canonicalPhaseLowBasisOddProfile k) := by
  cases k with
  | inl i =>
      intro x
      simp [canonicalPhaseLowBasisOddProfile]
  | inr j =>
      intro x
      simp only [canonicalPhaseLowBasisOddProfile]
      unfold factorTwoCenteredOddLowProfile centeredRescale
      rw [show yoshidaA * -x = -(yoshidaA * x) by ring]
      change (yoshidaClippedOddMode yoshidaA (j.1 + 1)
          (-(yoshidaA * x))).re =
        -(yoshidaClippedOddMode yoshidaA (j.1 + 1)
          (yoshidaA * x)).re
      by_cases hx : yoshidaA * x ∈ Icc (-yoshidaA) yoshidaA
      · have hnx : -(yoshidaA * x) ∈ Icc (-yoshidaA) yoshidaA := by
          constructor <;> linarith [hx.1, hx.2]
        rw [yoshidaClippedOddMode_apply_all yoshidaA_pos (j.1 + 1)
            (-(yoshidaA * x)),
          yoshidaClippedOddMode_apply_all yoshidaA_pos (j.1 + 1)
            (yoshidaA * x),
          if_pos hnx, if_pos hx]
        norm_cast
        rw [show Real.pi * (((j.1 + 1 : ℕ) : ℝ)) * (-(yoshidaA * x)) /
              yoshidaA =
            -(Real.pi * (((j.1 + 1 : ℕ) : ℝ)) * (yoshidaA * x) /
              yoshidaA) by ring,
          Real.sin_neg]
        ring
      · have hnx : -(yoshidaA * x) ∉ Icc (-yoshidaA) yoshidaA := by
          intro h
          apply hx
          constructor <;> linarith [h.1, h.2]
        rw [yoshidaClippedOddMode_apply_all yoshidaA_pos (j.1 + 1)
            (-(yoshidaA * x)),
          yoshidaClippedOddMode_apply_all yoshidaA_pos (j.1 + 1)
            (yoshidaA * x),
          if_neg hnx, if_neg hx]
        simp

/-- The canonical odd low mode bundled in the clipped periodic core. -/
def canonicalOddLowModePeriodicCore (j : YoshidaOddIndex) :
    YoshidaClippedPeriodicCore yoshidaA :=
  ⟨yoshidaClippedOddLowMode yoshidaA j,
    yoshidaClippedOddLowMode_mem_periodicCore yoshidaA_pos j⟩

@[simp] theorem canonicalOddLowModePeriodicCore_toSmooth
    (j : YoshidaOddIndex) :
    ((canonicalOddLowModePeriodicCore j :
        YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) =
        yoshidaClippedOddLowMode yoshidaA j :=
  rfl

private theorem clippedIntervalEnergy_evenLowMode_eq_one
    (i : YoshidaEvenIndex) :
    clippedIntervalEnergy (yoshidaClippedEvenLowMode yoshidaA i) = 1 := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  calc
    clippedIntervalEnergy (yoshidaClippedEvenLowMode yoshidaA i) =
        lebesgueNormSq (T := 2 * yoshidaA)
          (yoshidaClippedCircleL2 yoshidaA_pos
            (yoshidaClippedEvenLowMode yoshidaA i)) := by
      simpa only [clippedIntervalEnergy] using
        (lebesgueNormSq_yoshidaClippedCircleL2 yoshidaA_pos
          (yoshidaClippedEvenLowMode yoshidaA i)).symm
    _ = lebesgueNormSq (T := 2 * yoshidaA)
        (yoshidaEvenLowMode (T := 2 * yoshidaA) i) := by
      rw [yoshidaClippedCircleL2_evenLowMode]
    _ = 1 := lebesgueNormSq_yoshidaEvenLowMode i

private theorem clippedIntervalEnergy_oddLowMode_eq_one
    (j : YoshidaOddIndex) :
    clippedIntervalEnergy (yoshidaClippedOddLowMode yoshidaA j) = 1 := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  calc
    clippedIntervalEnergy (yoshidaClippedOddLowMode yoshidaA j) =
        lebesgueNormSq (T := 2 * yoshidaA)
          (yoshidaClippedCircleL2 yoshidaA_pos
            (yoshidaClippedOddLowMode yoshidaA j)) := by
      simpa only [clippedIntervalEnergy] using
        (lebesgueNormSq_yoshidaClippedCircleL2 yoshidaA_pos
          (yoshidaClippedOddLowMode yoshidaA j)).symm
    _ = lebesgueNormSq (T := 2 * yoshidaA)
        (yoshidaOddLowMode (T := 2 * yoshidaA) j) := by
      rw [yoshidaClippedCircleL2_oddLowMode]
    _ = 1 := lebesgueNormSq_yoshidaOddLowMode j

/-- Every normalized canonical even low basis profile has exact centered
interval energy `1 / yoshidaA`. -/
theorem canonicalEvenLowBasis_energy_eq
    (i : YoshidaEvenIndex) :
    (∫ x : ℝ in -1..1,
      (boundaryContinuousEvenProfile
        (canonicalEvenLowModePointwise i) x) ^ 2) =
      1 / yoshidaA := by
  let r : YoshidaClippedPeriodicCore yoshidaA :=
    canonicalEvenLowModePeriodicCore i
  let raw : ℝ → ℝ := centeredRescale yoshidaA (fun y ↦
    ((r : YoshidaClippedSmooth yoshidaA) y).re)
  have hreal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    dsimp only [r]
    exact evenLowMode_im_zero i x
  have henergy := centeredRescale_energy_eq r hreal
  have hclip : clippedIntervalEnergy
      (r : YoshidaClippedSmooth yoshidaA) = 1 := by
    simpa only [r, canonicalEvenLowModePeriodicCore_toSmooth] using
      clippedIntervalEnergy_evenLowMode_eq_one i
  have hprofiles : ∀ x ∈ Icc (-1 : ℝ) 1,
      boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i) x =
        raw x := by
    intro x hx
    simpa only [raw, r, canonicalEvenLowModePointwise] using
      boundaryContinuousEvenProfile_eq_centeredRescale
        (canonicalEvenLowModePointwise i) hreal hx
  have hintegral :
      (∫ x : ℝ in -1..1,
          (boundaryContinuousEvenProfile
            (canonicalEvenLowModePointwise i) x) ^ 2) =
        ∫ x : ℝ in -1..1, raw x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    change boundaryContinuousEvenProfile
        (canonicalEvenLowModePointwise i) x ^ 2 = raw x ^ 2
    rw [hprofiles x hx]
  have hmul : yoshidaA * (∫ x : ℝ in -1..1, raw x ^ 2) = 1 := by
    calc
      yoshidaA * (∫ x : ℝ in -1..1, raw x ^ 2) =
          clippedIntervalEnergy (r : YoshidaClippedSmooth yoshidaA) := by
        simpa only [raw, YoshidaEndpointHyperbolicBound.yoshidaEndpointA,
          YoshidaWeightedTailBounds.yoshidaA] using henergy.symm
      _ = 1 := hclip
  rw [hintegral]
  apply (eq_div_iff yoshidaA_pos.ne').2
  simpa only [mul_comm] using hmul

/-- Every normalized canonical odd low basis profile has exact centered
interval energy `1 / yoshidaA`. -/
theorem canonicalOddLowBasis_energy_eq
    (j : YoshidaOddIndex) :
    (∫ x : ℝ in -1..1,
      factorTwoCenteredOddLowProfile j x ^ 2) =
      1 / yoshidaA := by
  let r : YoshidaClippedPeriodicCore yoshidaA :=
    canonicalOddLowModePeriodicCore j
  have hreal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    dsimp only [r, canonicalOddLowModePeriodicCore]
    exact oddLowMode_im_zero j x
  have henergy := centeredRescale_energy_eq r hreal
  have hclip : clippedIntervalEnergy
      (r : YoshidaClippedSmooth yoshidaA) = 1 := by
    simpa only [r, canonicalOddLowModePeriodicCore_toSmooth] using
      clippedIntervalEnergy_oddLowMode_eq_one j
  change (∫ x : ℝ in -1..1,
      centeredRescale yoshidaA (fun y ↦
        ((r : YoshidaClippedSmooth yoshidaA) y).re) x ^ 2) = _
  have hmul : yoshidaA *
      (∫ x : ℝ in -1..1,
        centeredRescale yoshidaA (fun y ↦
          ((r : YoshidaClippedSmooth yoshidaA) y).re) x ^ 2) = 1 := by
    calc
      yoshidaA *
          (∫ x : ℝ in -1..1,
            centeredRescale yoshidaA (fun y ↦
              ((r : YoshidaClippedSmooth yoshidaA) y).re) x ^ 2) =
          clippedIntervalEnergy (r : YoshidaClippedSmooth yoshidaA) := by
        simpa only [YoshidaEndpointHyperbolicBound.yoshidaEndpointA,
          YoshidaWeightedTailBounds.yoshidaA] using henergy.symm
      _ = 1 := hclip
  apply (eq_div_iff yoshidaA_pos.ne').2
  simpa only [mul_comm] using hmul

/-- Mixed phase functional of a canonical low basis vector against the real
tail coordinate. -/
def canonicalPhaseLowBasisTailRealMixedValue
    (k : FactorTwoPhaseLowIndex) (x : CanonicalPhaseTailCore)
    (a b : ℝ) : ℝ :=
  factorTwoEndpointLowTailMixed
    (canonicalPhaseLowBasisEvenProfile k)
    (canonicalPhaseTailEvenRealProfile x)
    (canonicalPhaseLowBasisOddProfile k)
    (canonicalPhaseTailOddRealProfile x) a b

/-- Mixed phase functional of a canonical low basis vector against the
imaginary tail coordinate. -/
def canonicalPhaseLowBasisTailImagMixedValue
    (k : FactorTwoPhaseLowIndex) (x : CanonicalPhaseTailCore)
    (a b : ℝ) : ℝ :=
  factorTwoEndpointLowTailMixed
    (canonicalPhaseLowBasisEvenProfile k)
    (canonicalPhaseTailEvenImagProfile x)
    (canonicalPhaseLowBasisOddProfile k)
    (canonicalPhaseTailOddImagProfile x) a b

private theorem canonicalPhaseLowBasisMixed_add_right
    (k : FactorTwoPhaseLowIndex)
    (e₁ e₂ : YoshidaEvenOneNinetyNineTail)
    (o₁ o₂ : YoshidaOddTenTail)
    (heReal₁ : ∀ t : ℝ,
      (evenOneNinetyNineTailToClippedSmooth e₁ t).im = 0)
    (heReal₂ : ∀ t : ℝ,
      (evenOneNinetyNineTailToClippedSmooth e₂ t).im = 0)
    (hoReal₁ : ∀ t : ℝ,
      (oddTenTailToClippedSmooth o₁ t).im = 0)
    (hoReal₂ : ∀ t : ℝ,
      (oddTenTailToClippedSmooth o₂ t).im = 0)
    (a b : ℝ) :
    factorTwoEndpointLowTailMixed
        (canonicalPhaseLowBasisEvenProfile k)
        (boundaryCanonicalEvenTailProfile e₁ +
          boundaryCanonicalEvenTailProfile e₂)
        (canonicalPhaseLowBasisOddProfile k)
        (canonicalOddTailProfile o₁ + canonicalOddTailProfile o₂) a b =
      factorTwoEndpointLowTailMixed
          (canonicalPhaseLowBasisEvenProfile k)
          (boundaryCanonicalEvenTailProfile e₁)
          (canonicalPhaseLowBasisOddProfile k)
          (canonicalOddTailProfile o₁) a b +
        factorTwoEndpointLowTailMixed
          (canonicalPhaseLowBasisEvenProfile k)
          (boundaryCanonicalEvenTailProfile e₂)
          (canonicalPhaseLowBasisOddProfile k)
          (canonicalOddTailProfile o₂) a b := by
  obtain ⟨hoNeg₁, hoPos₁⟩ := oddTenTail_endpoints_zero o₁
  obtain ⟨hoNeg₂, hoPos₂⟩ := oddTenTail_endpoints_zero o₂
  cases k with
  | inl i =>
      have h := factorTwoEndpointLowTailMixed_boundaryContinuous_add_right
        (canonicalEvenLowModePointwise i)
        (canonicalEvenTailPointwise e₁)
        (canonicalEvenTailPointwise e₂)
        (0 : YoshidaClippedPeriodicCore yoshidaA)
        (o₁ : YoshidaClippedPeriodicCore yoshidaA)
        (o₂ : YoshidaClippedPeriodicCore yoshidaA)
        (by
          intro t
          simpa only [canonicalEvenLowModePointwise,
            canonicalEvenLowModePeriodicCore_toSmooth] using
              evenLowMode_im_zero i t)
        heReal₁ heReal₂
        (by intro t; simp) hoReal₁ hoReal₂
        (by simp) (by simp) hoNeg₁ hoPos₁ hoNeg₂ hoPos₂ a b
      change factorTwoEndpointLowTailMixed
          (canonicalPhaseLowBasisEvenProfile (Sum.inl i))
          (boundaryCanonicalEvenTailProfile e₁ +
            boundaryCanonicalEvenTailProfile e₂)
          (canonicalPhaseLowBasisOddProfile (Sum.inl i))
          (canonicalOddTailProfile o₁ + canonicalOddTailProfile o₂) a b =
        factorTwoEndpointLowTailMixed
            (canonicalPhaseLowBasisEvenProfile (Sum.inl i))
            (boundaryCanonicalEvenTailProfile e₁)
            (canonicalPhaseLowBasisOddProfile (Sum.inl i))
            (canonicalOddTailProfile o₁) a b +
          factorTwoEndpointLowTailMixed
            (canonicalPhaseLowBasisEvenProfile (Sum.inl i))
            (boundaryCanonicalEvenTailProfile e₂)
            (canonicalPhaseLowBasisOddProfile (Sum.inl i))
            (canonicalOddTailProfile o₂) a b at h
      exact h
  | inr j =>
      have hlowNeg :
          ((canonicalOddLowModePeriodicCore j :
            YoshidaClippedSmooth yoshidaA) (-yoshidaA)) = 0 := by
        change yoshidaClippedOddMode yoshidaA (j.1 + 1) (-yoshidaA) = 0
        exact yoshidaClippedOddMode_left_endpoint yoshidaA_pos (j.1 + 1)
      have hlowPos :
          ((canonicalOddLowModePeriodicCore j :
            YoshidaClippedSmooth yoshidaA) yoshidaA) = 0 := by
        change yoshidaClippedOddMode yoshidaA (j.1 + 1) yoshidaA = 0
        exact yoshidaClippedOddMode_right_endpoint yoshidaA_pos (j.1 + 1)
      have h := factorTwoEndpointLowTailMixed_boundaryContinuous_add_right
        (0 : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA)
        (canonicalEvenTailPointwise e₁)
        (canonicalEvenTailPointwise e₂)
        (canonicalOddLowModePeriodicCore j)
        (o₁ : YoshidaClippedPeriodicCore yoshidaA)
        (o₂ : YoshidaClippedPeriodicCore yoshidaA)
        (by intro t; simp) heReal₁ heReal₂
        (by
          intro t
          simpa only [canonicalOddLowModePeriodicCore_toSmooth] using
            oddLowMode_im_zero j t)
        hoReal₁ hoReal₂ hlowNeg hlowPos hoNeg₁ hoPos₁ hoNeg₂ hoPos₂ a b
      simp only [boundaryContinuousEvenProfile_zero] at h
      change factorTwoEndpointLowTailMixed
          (canonicalPhaseLowBasisEvenProfile (Sum.inr j))
          (boundaryCanonicalEvenTailProfile e₁ +
            boundaryCanonicalEvenTailProfile e₂)
          (canonicalPhaseLowBasisOddProfile (Sum.inr j))
          (canonicalOddTailProfile o₁ + canonicalOddTailProfile o₂) a b =
        factorTwoEndpointLowTailMixed
            (canonicalPhaseLowBasisEvenProfile (Sum.inr j))
            (boundaryCanonicalEvenTailProfile e₁)
            (canonicalPhaseLowBasisOddProfile (Sum.inr j))
            (canonicalOddTailProfile o₁) a b +
          factorTwoEndpointLowTailMixed
            (canonicalPhaseLowBasisEvenProfile (Sum.inr j))
            (boundaryCanonicalEvenTailProfile e₂)
            (canonicalPhaseLowBasisOddProfile (Sum.inr j))
            (canonicalOddTailProfile o₂) a b at h
      exact h

theorem canonicalPhaseLowBasisMixed_smul_right
    (k : FactorTwoPhaseLowIndex)
    (e : YoshidaEvenOneNinetyNineTail) (o : YoshidaOddTenTail)
    (heReal : ∀ t : ℝ,
      (evenOneNinetyNineTailToClippedSmooth e t).im = 0)
    (hoReal : ∀ t : ℝ,
      (oddTenTailToClippedSmooth o t).im = 0)
    (r a b : ℝ) :
    factorTwoEndpointLowTailMixed
        (canonicalPhaseLowBasisEvenProfile k)
        (r • boundaryCanonicalEvenTailProfile e)
        (canonicalPhaseLowBasisOddProfile k)
        (r • canonicalOddTailProfile o) a b =
      r * factorTwoEndpointLowTailMixed
        (canonicalPhaseLowBasisEvenProfile k)
        (boundaryCanonicalEvenTailProfile e)
        (canonicalPhaseLowBasisOddProfile k)
        (canonicalOddTailProfile o) a b := by
  obtain ⟨hoNeg, hoPos⟩ := oddTenTail_endpoints_zero o
  cases k with
  | inl i =>
      have h := factorTwoEndpointLowTailMixed_boundaryContinuous_smul_smul
        (canonicalEvenLowModePointwise i)
        (canonicalEvenTailPointwise e)
        (0 : YoshidaClippedPeriodicCore yoshidaA)
        (o : YoshidaClippedPeriodicCore yoshidaA)
        (by
          intro t
          simpa only [canonicalEvenLowModePointwise,
            canonicalEvenLowModePeriodicCore_toSmooth] using
              evenLowMode_im_zero i t)
        heReal (by intro t; simp) hoReal
        (by simp) (by simp) hoNeg hoPos 1 r a b
      simp only [one_smul, one_mul] at h
      change factorTwoEndpointLowTailMixed
          (canonicalPhaseLowBasisEvenProfile (Sum.inl i))
          (r • boundaryCanonicalEvenTailProfile e)
          (canonicalPhaseLowBasisOddProfile (Sum.inl i))
          (r • canonicalOddTailProfile o) a b =
        r * factorTwoEndpointLowTailMixed
          (canonicalPhaseLowBasisEvenProfile (Sum.inl i))
          (boundaryCanonicalEvenTailProfile e)
          (canonicalPhaseLowBasisOddProfile (Sum.inl i))
          (canonicalOddTailProfile o) a b at h
      exact h
  | inr j =>
      have hlowNeg :
          ((canonicalOddLowModePeriodicCore j :
            YoshidaClippedSmooth yoshidaA) (-yoshidaA)) = 0 := by
        change yoshidaClippedOddMode yoshidaA (j.1 + 1) (-yoshidaA) = 0
        exact yoshidaClippedOddMode_left_endpoint yoshidaA_pos (j.1 + 1)
      have hlowPos :
          ((canonicalOddLowModePeriodicCore j :
            YoshidaClippedSmooth yoshidaA) yoshidaA) = 0 := by
        change yoshidaClippedOddMode yoshidaA (j.1 + 1) yoshidaA = 0
        exact yoshidaClippedOddMode_right_endpoint yoshidaA_pos (j.1 + 1)
      have h := factorTwoEndpointLowTailMixed_boundaryContinuous_smul_smul
        (0 : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA)
        (canonicalEvenTailPointwise e)
        (canonicalOddLowModePeriodicCore j)
        (o : YoshidaClippedPeriodicCore yoshidaA)
        (by intro t; simp) heReal
        (by
          intro t
          simpa only [canonicalOddLowModePeriodicCore_toSmooth] using
            oddLowMode_im_zero j t)
        hoReal hlowNeg hlowPos hoNeg hoPos 1 r a b
      simp only [one_smul, one_mul, boundaryContinuousEvenProfile_zero] at h
      change factorTwoEndpointLowTailMixed
          (canonicalPhaseLowBasisEvenProfile (Sum.inr j))
          (r • boundaryCanonicalEvenTailProfile e)
          (canonicalPhaseLowBasisOddProfile (Sum.inr j))
          (r • canonicalOddTailProfile o) a b =
        r * factorTwoEndpointLowTailMixed
          (canonicalPhaseLowBasisEvenProfile (Sum.inr j))
          (boundaryCanonicalEvenTailProfile e)
          (canonicalPhaseLowBasisOddProfile (Sum.inr j))
          (canonicalOddTailProfile o) a b at h
      exact h

theorem canonicalPhaseLowBasisTailRealMixedValue_add
    (k : FactorTwoPhaseLowIndex) (x y : CanonicalPhaseTailCore)
    (a b : ℝ) :
    canonicalPhaseLowBasisTailRealMixedValue k (x + y) a b =
      canonicalPhaseLowBasisTailRealMixedValue k x a b +
        canonicalPhaseLowBasisTailRealMixedValue k y a b := by
  unfold canonicalPhaseLowBasisTailRealMixedValue
  rw [canonicalPhaseTailEvenRealProfile_add,
    canonicalPhaseTailOddRealProfile_add]
  exact canonicalPhaseLowBasisMixed_add_right k
    (evenTailRealPart x.fst.toV) (evenTailRealPart y.fst.toV)
    (oddTailRealPart x.snd.toV) (oddTailRealPart y.snd.toV)
    (by intro t; change (((((evenOneNinetyNineTailToClippedSmooth
      x.fst.toV t).re : ℝ) : ℂ)).im) = 0; simp)
    (by intro t; change (((((evenOneNinetyNineTailToClippedSmooth
      y.fst.toV t).re : ℝ) : ℂ)).im) = 0; simp)
    (by intro t; change (((((oddTenTailToClippedSmooth
      x.snd.toV t).re : ℝ) : ℂ)).im) = 0; simp)
    (by intro t; change (((((oddTenTailToClippedSmooth
      y.snd.toV t).re : ℝ) : ℂ)).im) = 0; simp) a b

theorem canonicalPhaseLowBasisTailImagMixedValue_add
    (k : FactorTwoPhaseLowIndex) (x y : CanonicalPhaseTailCore)
    (a b : ℝ) :
    canonicalPhaseLowBasisTailImagMixedValue k (x + y) a b =
      canonicalPhaseLowBasisTailImagMixedValue k x a b +
        canonicalPhaseLowBasisTailImagMixedValue k y a b := by
  unfold canonicalPhaseLowBasisTailImagMixedValue
  rw [canonicalPhaseTailEvenImagProfile_add,
    canonicalPhaseTailOddImagProfile_add]
  exact canonicalPhaseLowBasisMixed_add_right k
    (evenTailImagPart x.fst.toV) (evenTailImagPart y.fst.toV)
    (oddTailImagPart x.snd.toV) (oddTailImagPart y.snd.toV)
    (by intro t; change (((((evenOneNinetyNineTailToClippedSmooth
      x.fst.toV t).im : ℝ) : ℂ)).im) = 0; simp)
    (by intro t; change (((((evenOneNinetyNineTailToClippedSmooth
      y.fst.toV t).im : ℝ) : ℂ)).im) = 0; simp)
    (by intro t; change (((((oddTenTailToClippedSmooth
      x.snd.toV t).im : ℝ) : ℂ)).im) = 0; simp)
    (by intro t; change (((((oddTenTailToClippedSmooth
      y.snd.toV t).im : ℝ) : ℂ)).im) = 0; simp) a b

theorem canonicalPhaseLowBasisTailRealMixedValue_smul
    (k : FactorTwoPhaseLowIndex) (r : ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseLowBasisTailRealMixedValue k (r • x) a b =
      r * canonicalPhaseLowBasisTailRealMixedValue k x a b := by
  unfold canonicalPhaseLowBasisTailRealMixedValue
  rw [canonicalPhaseTailEvenRealProfile_smul,
    canonicalPhaseTailOddRealProfile_smul]
  exact canonicalPhaseLowBasisMixed_smul_right k
    (evenTailRealPart x.fst.toV) (oddTailRealPart x.snd.toV)
    (by intro t; change (((((evenOneNinetyNineTailToClippedSmooth
      x.fst.toV t).re : ℝ) : ℂ)).im) = 0; simp)
    (by intro t; change (((((oddTenTailToClippedSmooth
      x.snd.toV t).re : ℝ) : ℂ)).im) = 0; simp) r a b

theorem canonicalPhaseLowBasisTailImagMixedValue_smul
    (k : FactorTwoPhaseLowIndex) (r : ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseLowBasisTailImagMixedValue k (r • x) a b =
      r * canonicalPhaseLowBasisTailImagMixedValue k x a b := by
  unfold canonicalPhaseLowBasisTailImagMixedValue
  rw [canonicalPhaseTailEvenImagProfile_smul,
    canonicalPhaseTailOddImagProfile_smul]
  exact canonicalPhaseLowBasisMixed_smul_right k
    (evenTailImagPart x.fst.toV) (oddTailImagPart x.snd.toV)
    (by intro t; change (((((evenOneNinetyNineTailToClippedSmooth
      x.fst.toV t).im : ℝ) : ℂ)).im) = 0; simp)
    (by intro t; change (((((oddTenTailToClippedSmooth
      x.snd.toV t).im : ℝ) : ℂ)).im) = 0; simp) r a b

private theorem norm_evenTailRealPart_le_core
    (x : CanonicalPhaseTailCore) :
    ‖(FormSpace.of (evenTailRealPart x.fst.toV) :
      EvenPhaseTailFormSpace)‖ ≤ ‖x‖ := by
  have hsplit := evenFormSpace_norm_sq_eq_real_add_imag x.fst
  have hsq :
      ‖(FormSpace.of (evenTailRealPart x.fst.toV) :
        EvenPhaseTailFormSpace)‖ ^ 2 ≤ ‖x.fst‖ ^ 2 := by
    nlinarith [sq_nonneg
      ‖(FormSpace.of (evenTailImagPart x.fst.toV) :
        EvenPhaseTailFormSpace)‖]
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq).trans
    (WithLp.norm_fst_le EvenPhaseTailFormSpace x)

private theorem norm_evenTailImagPart_le_core
    (x : CanonicalPhaseTailCore) :
    ‖(FormSpace.of (evenTailImagPart x.fst.toV) :
      EvenPhaseTailFormSpace)‖ ≤ ‖x‖ := by
  have hsplit := evenFormSpace_norm_sq_eq_real_add_imag x.fst
  have hsq :
      ‖(FormSpace.of (evenTailImagPart x.fst.toV) :
        EvenPhaseTailFormSpace)‖ ^ 2 ≤ ‖x.fst‖ ^ 2 := by
    nlinarith [sq_nonneg
      ‖(FormSpace.of (evenTailRealPart x.fst.toV) :
        EvenPhaseTailFormSpace)‖]
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq).trans
    (WithLp.norm_fst_le EvenPhaseTailFormSpace x)

private theorem norm_oddTailRealPart_le_core
    (x : CanonicalPhaseTailCore) :
    ‖(FormSpace.of (oddTailRealPart x.snd.toV) :
      OddPhaseTailFormSpace)‖ ≤ ‖x‖ := by
  have hsplit := oddFormSpace_norm_sq_eq_real_add_imag x.snd
  have hsq :
      ‖(FormSpace.of (oddTailRealPart x.snd.toV) :
        OddPhaseTailFormSpace)‖ ^ 2 ≤ ‖x.snd‖ ^ 2 := by
    nlinarith [sq_nonneg
      ‖(FormSpace.of (oddTailImagPart x.snd.toV) :
        OddPhaseTailFormSpace)‖]
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq).trans
    (WithLp.norm_snd_le EvenPhaseTailFormSpace x)

private theorem norm_oddTailImagPart_le_core
    (x : CanonicalPhaseTailCore) :
    ‖(FormSpace.of (oddTailImagPart x.snd.toV) :
      OddPhaseTailFormSpace)‖ ≤ ‖x‖ := by
  have hsplit := oddFormSpace_norm_sq_eq_real_add_imag x.snd
  have hsq :
      ‖(FormSpace.of (oddTailImagPart x.snd.toV) :
        OddPhaseTailFormSpace)‖ ^ 2 ≤ ‖x.snd‖ ^ 2 := by
    nlinarith [sq_nonneg
      ‖(FormSpace.of (oddTailRealPart x.snd.toV) :
        OddPhaseTailFormSpace)‖]
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq).trans
    (WithLp.norm_snd_le EvenPhaseTailFormSpace x)

private theorem evenBoundaryTail_energy_le_formNorm
    (e : YoshidaEvenOneNinetyNineTail)
    (hreal : ∀ t : ℝ,
      (evenOneNinetyNineTailToClippedSmooth e t).im = 0) :
    (∫ t : ℝ in -1..1,
      boundaryCanonicalEvenTailProfile e t ^ 2) ≤
      (25 / (102 * yoshidaA) : ℝ) *
        ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2 := by
  have hcoercive := evenTail_boundaryContinuous_clean_coercive
    (e : YoshidaClippedPeriodicCore yoshidaA) e.property hreal
  have hnorm := evenRealTailFormSpace_norm_sq_eq_clean e hreal
  change (102 / 25 : ℝ) *
      (∫ t : ℝ in -1..1,
        boundaryCanonicalEvenTailProfile e t ^ 2) ≤
    yoshidaEndpointOddCleanQuadratic
      (boundaryCanonicalEvenTailProfile e) at hcoercive
  have hscaled := mul_le_mul_of_nonneg_left hcoercive yoshidaA_pos.le
  have hraw :
      (102 / 25 : ℝ) * yoshidaA *
          (∫ t : ℝ in -1..1,
            boundaryCanonicalEvenTailProfile e t ^ 2) ≤
        ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2 := by
    rw [hnorm]
    nlinarith
  calc
    (∫ t : ℝ in -1..1,
        boundaryCanonicalEvenTailProfile e t ^ 2) =
        (25 / (102 * yoshidaA) : ℝ) *
          ((102 / 25 : ℝ) * yoshidaA *
            (∫ t : ℝ in -1..1,
              boundaryCanonicalEvenTailProfile e t ^ 2)) := by
      field_simp [yoshidaA_pos.ne']
    _ ≤ (25 / (102 * yoshidaA) : ℝ) *
        ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hraw
        (div_nonneg (by norm_num)
          (mul_nonneg (by norm_num) yoshidaA_pos.le))

private theorem oddTail_energy_le_formNorm
    (o : YoshidaOddTenTail)
    (hreal : ∀ t : ℝ, (oddTenTailToClippedSmooth o t).im = 0) :
    (∫ t : ℝ in -1..1, canonicalOddTailProfile o t ^ 2) ≤
      (25 / (38 * yoshidaA) : ℝ) *
        ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ ^ 2 := by
  obtain ⟨hoNeg, hoPos⟩ := oddTenTail_endpoints_zero o
  have hcoercive := oddTail_endpoint_clean_coercive
    (o : YoshidaClippedPeriodicCore yoshidaA) o.property hreal hoNeg hoPos
  have hnorm := oddRealTailFormSpace_norm_sq_eq_clean o hreal
  change (38 / 25 : ℝ) *
      (∫ t : ℝ in -1..1, canonicalOddTailProfile o t ^ 2) ≤
    yoshidaEndpointOddCleanQuadratic (canonicalOddTailProfile o) at hcoercive
  have hscaled := mul_le_mul_of_nonneg_left hcoercive yoshidaA_pos.le
  have hraw :
      (38 / 25 : ℝ) * yoshidaA *
          (∫ t : ℝ in -1..1, canonicalOddTailProfile o t ^ 2) ≤
        ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ ^ 2 := by
    rw [hnorm]
    nlinarith
  calc
    (∫ t : ℝ in -1..1, canonicalOddTailProfile o t ^ 2) =
        (25 / (38 * yoshidaA) : ℝ) *
          ((38 / 25 : ℝ) * yoshidaA *
            (∫ t : ℝ in -1..1,
              canonicalOddTailProfile o t ^ 2)) := by
      field_simp [yoshidaA_pos.ne']
    _ ≤ (25 / (38 * yoshidaA) : ℝ) *
        ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hraw
        (div_nonneg (by norm_num)
          (mul_nonneg (by norm_num) yoshidaA_pos.le))

private theorem abs_evenLow_clean_le_formNorm
    (i : YoshidaEvenIndex) (e : YoshidaEvenOneNinetyNineTail)
    (hreal : ∀ t : ℝ,
      (evenOneNinetyNineTailToClippedSmooth e t).im = 0) :
    |factorTwoCenteredCleanPolarization
        (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
        (boundaryCanonicalEvenTailProfile e)| ≤
      (1 / yoshidaA) *
        ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ := by
  have hlowReal : ∀ t : ℝ,
      ((((canonicalEvenLowModePointwise i).1 :
        YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) t).im = 0 := by
    intro t
    simpa only [canonicalEvenLowModePointwise,
      canonicalEvenLowModePeriodicCore_toSmooth] using
        evenLowMode_im_zero i t
  have hbridge :=
    factorTwoCenteredCleanPolarization_boundaryContinuous_eq_clippedCriticalForm_re_div
      (canonicalEvenLowModePointwise i)
      (canonicalEvenTailPointwise e) hlowReal hreal
  let z : ℂ := yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
    (yoshidaClippedEvenLowMode yoshidaA i)
    (evenOneNinetyNineTailToClippedSmooth e)
  have htail := evenTailLowFunctional_sq_le_formNorm
    (FormSpace.of e : EvenPhaseTailFormSpace) i
  have hconj := yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos
    (evenOneNinetyNineTailToClippedSmooth e)
    (yoshidaClippedEvenLowMode yoshidaA i)
  have hnormEq : ‖z‖ =
      ‖yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth e)
        (yoshidaClippedEvenLowMode yoshidaA i)‖ := by
    dsimp only [z]
    rw [← hconj]
    simp
  have hsq : ‖z‖ ^ 2 ≤
      ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2 := by
    rw [hnormEq]
    nlinarith [sq_nonneg
      ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖]
  have hnorm : ‖z‖ ≤
      ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  change factorTwoCenteredCleanPolarization
      (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
      (boundaryCanonicalEvenTailProfile e) = z.re / yoshidaA at hbridge
  rw [hbridge, abs_div, abs_of_pos yoshidaA_pos]
  calc
    |z.re| / yoshidaA ≤ ‖z‖ / yoshidaA :=
      div_le_div_of_nonneg_right (Complex.abs_re_le_norm z) yoshidaA_pos.le
    _ ≤ ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ / yoshidaA :=
      div_le_div_of_nonneg_right hnorm yoshidaA_pos.le
    _ = (1 / yoshidaA) *
        ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ := by ring

private theorem abs_oddLow_clean_le_formNorm
    (j : YoshidaOddIndex) (o : YoshidaOddTenTail)
    (hreal : ∀ t : ℝ, (oddTenTailToClippedSmooth o t).im = 0) :
    |factorTwoCenteredCleanPolarization
        (factorTwoCenteredOddLowProfile j)
        (canonicalOddTailProfile o)| ≤
      (1 / yoshidaA) *
        ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ := by
  obtain ⟨hoNeg, hoPos⟩ := oddTenTail_endpoints_zero o
  have hlowReal : ∀ t : ℝ,
      ((canonicalOddLowModePeriodicCore j :
        YoshidaClippedSmooth yoshidaA) t).im = 0 := by
    intro t
    simpa only [canonicalOddLowModePeriodicCore_toSmooth] using
      oddLowMode_im_zero j t
  have hlowNeg :
      ((canonicalOddLowModePeriodicCore j :
        YoshidaClippedSmooth yoshidaA) (-yoshidaA)) = 0 := by
    change yoshidaClippedOddMode yoshidaA (j.1 + 1) (-yoshidaA) = 0
    exact yoshidaClippedOddMode_left_endpoint yoshidaA_pos (j.1 + 1)
  have hlowPos :
      ((canonicalOddLowModePeriodicCore j :
        YoshidaClippedSmooth yoshidaA) yoshidaA) = 0 := by
    change yoshidaClippedOddMode yoshidaA (j.1 + 1) yoshidaA = 0
    exact yoshidaClippedOddMode_right_endpoint yoshidaA_pos (j.1 + 1)
  have hbridge :=
    factorTwoCenteredCleanPolarization_eq_clippedCriticalForm_re_div
      (canonicalOddLowModePeriodicCore j)
      (o : YoshidaClippedPeriodicCore yoshidaA)
      hlowReal hreal hlowNeg hlowPos hoNeg hoPos
  let z : ℂ := yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
    (yoshidaClippedOddLowMode yoshidaA j)
    (oddTenTailToClippedSmooth o)
  have htail := oddTailLowFunctional_sq_le_formNorm
    (FormSpace.of o : OddPhaseTailFormSpace) j
  have hconj := yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos
    (oddTenTailToClippedSmooth o)
    (yoshidaClippedOddLowMode yoshidaA j)
  have hnormEq : ‖z‖ =
      ‖yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (oddTenTailToClippedSmooth o)
        (yoshidaClippedOddLowMode yoshidaA j)‖ := by
    dsimp only [z]
    rw [← hconj]
    simp
  have hsq : ‖z‖ ^ 2 ≤
      ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ ^ 2 := by
    rw [hnormEq]
    nlinarith [sq_nonneg
      ‖(FormSpace.of o : OddPhaseTailFormSpace)‖]
  have hnorm : ‖z‖ ≤
      ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  change factorTwoCenteredCleanPolarization
      (factorTwoCenteredOddLowProfile j) (canonicalOddTailProfile o) =
    z.re / yoshidaA at hbridge
  rw [hbridge, abs_div, abs_of_pos yoshidaA_pos]
  calc
    |z.re| / yoshidaA ≤ ‖z‖ / yoshidaA :=
      div_le_div_of_nonneg_right (Complex.abs_re_le_norm z) yoshidaA_pos.le
    _ ≤ ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ / yoshidaA :=
      div_le_div_of_nonneg_right hnorm yoshidaA_pos.le
    _ = (1 / yoshidaA) *
        ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ := by ring

private theorem canonicalOddTailProfile_odd
    (o : YoshidaOddTenTail) : Function.Odd (canonicalOddTailProfile o) := by
  intro x
  unfold canonicalOddTailProfile centeredRescale
  rw [show yoshidaA * -x = -(yoshidaA * x) by ring,
    show (fun y ↦ ((o : YoshidaClippedSmooth yoshidaA) y).re)
        (-(yoshidaA * x)) =
      ((o : YoshidaClippedSmooth yoshidaA) (-(yoshidaA * x))).re by rfl]
  rw [oddTail_pointwise_odd yoshidaA_pos 10
    (o : YoshidaClippedPeriodicCore yoshidaA) o.property (yoshidaA * x)]
  rfl

private theorem abs_evenLow_symmetric_le_formNorm
    (i : YoshidaEvenIndex) (e : YoshidaEvenOneNinetyNineTail)
    (hreal : ∀ t : ℝ,
      (evenOneNinetyNineTailToClippedSmooth e t).im = 0) :
    |factorTwoCenteredSymmetricPerturbationBilinear
        (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
        (boundaryCanonicalEvenTailProfile e)| ≤
      (3 / yoshidaA) *
        ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ := by
  have hsq :=
    factorTwoCenteredSymmetricPerturbationBilinear_sq_le_even_energy_mul
      (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
      (boundaryCanonicalEvenTailProfile e)
      (continuous_boundaryContinuousEvenProfile
        (canonicalEvenLowModePointwise i))
      (continuous_boundaryCanonicalEvenTailProfile e)
      (boundaryContinuousEvenProfile_even
        (canonicalEvenLowModePointwise i))
      (boundaryContinuousEvenProfile_even (canonicalEvenTailPointwise e))
  rw [canonicalEvenLowBasis_energy_eq] at hsq
  have henergy := evenBoundaryTail_energy_le_formNorm e hreal
  have hleft : 0 ≤ (9 : ℝ) * (1 / yoshidaA) := by
    exact mul_nonneg (by norm_num) (div_nonneg (by norm_num) yoshidaA_pos.le)
  have hsq' :
      factorTwoCenteredSymmetricPerturbationBilinear
          (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
          (boundaryCanonicalEvenTailProfile e) ^ 2 ≤
        (3 / yoshidaA *
          ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖) ^ 2 := by
    calc
      _ ≤ 9 * (1 / yoshidaA) *
          (∫ t : ℝ in -1..1,
            boundaryCanonicalEvenTailProfile e t ^ 2) := hsq
      _ ≤ 9 * (1 / yoshidaA) *
          ((25 / (102 * yoshidaA) : ℝ) *
            ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left henergy hleft
      _ = (9 * (1 / yoshidaA) *
            (25 / (102 * yoshidaA) : ℝ)) *
          ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2 := by ring
      _ ≤ (3 / yoshidaA) ^ 2 *
          ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        field_simp [yoshidaA_pos.ne']
        exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg yoshidaA)
      _ = (3 / yoshidaA *
          ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖) ^ 2 := by ring
  exact abs_le_of_sq_le_sq hsq'
    (mul_nonneg (div_nonneg (by norm_num) yoshidaA_pos.le)
      (norm_nonneg _))

private theorem abs_oddLow_symmetric_le_formNorm
    (j : YoshidaOddIndex) (o : YoshidaOddTenTail)
    (hreal : ∀ t : ℝ, (oddTenTailToClippedSmooth o t).im = 0) :
    |factorTwoCenteredSymmetricPerturbationBilinear
        (factorTwoCenteredOddLowProfile j) (canonicalOddTailProfile o)| ≤
      (3 / yoshidaA) *
        ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ := by
  have hsq :=
    factorTwoCenteredSymmetricPerturbationBilinear_sq_le_odd_energy_mul
      (factorTwoCenteredOddLowProfile j) (canonicalOddTailProfile o)
      (continuous_factorTwoCenteredOddLowProfile j)
      (continuous_canonicalOddTailProfile o)
      (canonicalPhaseLowBasisOddProfile_odd (Sum.inr j))
      (canonicalOddTailProfile_odd o)
  rw [canonicalOddLowBasis_energy_eq] at hsq
  have henergy := oddTail_energy_le_formNorm o hreal
  have hleft : 0 ≤ (9 / 4 : ℝ) * (1 / yoshidaA) := by
    exact mul_nonneg (by norm_num) (div_nonneg (by norm_num) yoshidaA_pos.le)
  have hsq' :
      factorTwoCenteredSymmetricPerturbationBilinear
          (factorTwoCenteredOddLowProfile j) (canonicalOddTailProfile o) ^ 2 ≤
        (3 / yoshidaA *
          ‖(FormSpace.of o : OddPhaseTailFormSpace)‖) ^ 2 := by
    calc
      _ ≤ (9 / 4 : ℝ) * (1 / yoshidaA) *
          (∫ t : ℝ in -1..1, canonicalOddTailProfile o t ^ 2) := hsq
      _ ≤ (9 / 4 : ℝ) * (1 / yoshidaA) *
          ((25 / (38 * yoshidaA) : ℝ) *
            ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left henergy hleft
      _ = ((9 / 4 : ℝ) * (1 / yoshidaA) *
            (25 / (38 * yoshidaA) : ℝ)) *
          ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ ^ 2 := by ring
      _ ≤ (3 / yoshidaA) ^ 2 *
          ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        field_simp [yoshidaA_pos.ne']
        exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg yoshidaA)
      _ = (3 / yoshidaA *
          ‖(FormSpace.of o : OddPhaseTailFormSpace)‖) ^ 2 := by ring
  exact abs_le_of_sq_le_sq hsq'
    (mul_nonneg (div_nonneg (by norm_num) yoshidaA_pos.le)
      (norm_nonneg _))

private theorem abs_evenLow_oddTail_alternating_le_formNorm
    (i : YoshidaEvenIndex) (o : YoshidaOddTenTail)
    (hreal : ∀ t : ℝ, (oddTenTailToClippedSmooth o t).im = 0) :
    |factorTwoCenteredAlternatingCoupling
        (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
        (canonicalOddTailProfile o)| ≤
      (4 / yoshidaA) *
        ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ := by
  have hsq := factorTwoCenteredAlternatingCoupling_sq_le_energy_mul
    (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
    (canonicalOddTailProfile o)
    (continuous_boundaryContinuousEvenProfile
      (canonicalEvenLowModePointwise i))
    (continuous_canonicalOddTailProfile o)
    (boundaryContinuousEvenProfile_even (canonicalEvenLowModePointwise i))
    (canonicalOddTailProfile_odd o)
  rw [canonicalEvenLowBasis_energy_eq] at hsq
  have henergy := oddTail_energy_le_formNorm o hreal
  have hleft : 0 ≤ (625 / 64 : ℝ) * (1 / yoshidaA) := by
    exact mul_nonneg (by norm_num) (div_nonneg (by norm_num) yoshidaA_pos.le)
  have hsq' : factorTwoCenteredAlternatingCoupling
        (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
        (canonicalOddTailProfile o) ^ 2 ≤
      (4 / yoshidaA *
        ‖(FormSpace.of o : OddPhaseTailFormSpace)‖) ^ 2 := by
    calc
      _ ≤ (625 / 64 : ℝ) * ((1 / yoshidaA) *
          (∫ t : ℝ in -1..1, canonicalOddTailProfile o t ^ 2)) := hsq
      _ = (625 / 64 : ℝ) * (1 / yoshidaA) *
          (∫ t : ℝ in -1..1, canonicalOddTailProfile o t ^ 2) := by ring
      _ ≤ (625 / 64 : ℝ) * (1 / yoshidaA) *
          ((25 / (38 * yoshidaA) : ℝ) *
            ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left henergy hleft
      _ = ((625 / 64 : ℝ) * (1 / yoshidaA) *
            (25 / (38 * yoshidaA) : ℝ)) *
          ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ ^ 2 := by ring
      _ ≤ (4 / yoshidaA) ^ 2 *
          ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        field_simp [yoshidaA_pos.ne']
        exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg yoshidaA)
      _ = (4 / yoshidaA *
          ‖(FormSpace.of o : OddPhaseTailFormSpace)‖) ^ 2 := by ring
  exact abs_le_of_sq_le_sq hsq'
    (mul_nonneg (div_nonneg (by norm_num) yoshidaA_pos.le)
      (norm_nonneg _))

private theorem abs_evenTail_oddLow_alternating_le_formNorm
    (e : YoshidaEvenOneNinetyNineTail) (j : YoshidaOddIndex)
    (hreal : ∀ t : ℝ,
      (evenOneNinetyNineTailToClippedSmooth e t).im = 0) :
    |factorTwoCenteredAlternatingCoupling
        (boundaryCanonicalEvenTailProfile e)
        (factorTwoCenteredOddLowProfile j)| ≤
      (4 / yoshidaA) *
        ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ := by
  have hsq := factorTwoCenteredAlternatingCoupling_sq_le_energy_mul
    (boundaryCanonicalEvenTailProfile e) (factorTwoCenteredOddLowProfile j)
    (continuous_boundaryCanonicalEvenTailProfile e)
    (continuous_factorTwoCenteredOddLowProfile j)
    (boundaryContinuousEvenProfile_even (canonicalEvenTailPointwise e))
    (canonicalPhaseLowBasisOddProfile_odd (Sum.inr j))
  rw [canonicalOddLowBasis_energy_eq] at hsq
  have henergy := evenBoundaryTail_energy_le_formNorm e hreal
  have hright : 0 ≤ (625 / 64 : ℝ) * (1 / yoshidaA) := by
    exact mul_nonneg (by norm_num) (div_nonneg (by norm_num) yoshidaA_pos.le)
  have hsq' : factorTwoCenteredAlternatingCoupling
        (boundaryCanonicalEvenTailProfile e)
        (factorTwoCenteredOddLowProfile j) ^ 2 ≤
      (4 / yoshidaA *
        ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖) ^ 2 := by
    calc
      _ ≤ (625 / 64 : ℝ) *
          ((∫ t : ℝ in -1..1,
              boundaryCanonicalEvenTailProfile e t ^ 2) *
            (1 / yoshidaA)) := hsq
      _ = (625 / 64 : ℝ) * (1 / yoshidaA) *
          (∫ t : ℝ in -1..1,
            boundaryCanonicalEvenTailProfile e t ^ 2) := by ring
      _ ≤ (625 / 64 : ℝ) * (1 / yoshidaA) *
          ((25 / (102 * yoshidaA) : ℝ) *
            ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left henergy hright
      _ = ((625 / 64 : ℝ) * (1 / yoshidaA) *
            (25 / (102 * yoshidaA) : ℝ)) *
          ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2 := by ring
      _ ≤ (4 / yoshidaA) ^ 2 *
          ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        field_simp [yoshidaA_pos.ne']
        exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg yoshidaA)
      _ = (4 / yoshidaA *
          ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖) ^ 2 := by ring
  exact abs_le_of_sq_le_sq hsq'
    (mul_nonneg (div_nonneg (by norm_num) yoshidaA_pos.le)
      (norm_nonneg _))

@[simp] private theorem yoshidaEndpointOddCleanQuadratic_zero :
    yoshidaEndpointOddCleanQuadratic (0 : ℝ → ℝ) = 0 := by
  unfold yoshidaEndpointOddCleanQuadratic centeredRawLogEnergy
    yoshidaEndpointRegularQuadratic yoshidaEndpointHyperbolicQuadratic
  simp

@[simp] private theorem factorTwoCenteredCleanPolarization_zero_left
    (u : ℝ → ℝ) : factorTwoCenteredCleanPolarization 0 u = 0 := by
  unfold factorTwoCenteredCleanPolarization
  rw [zero_add, yoshidaEndpointOddCleanQuadratic_zero]
  ring

@[simp] private theorem factorTwoCenteredCleanPolarization_zero_right
    (u : ℝ → ℝ) : factorTwoCenteredCleanPolarization u 0 = 0 := by
  unfold factorTwoCenteredCleanPolarization
  rw [add_zero, yoshidaEndpointOddCleanQuadratic_zero]
  ring

@[simp] private theorem
    factorTwoCenteredSymmetricPerturbationBilinear_zero_left
    (u : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear 0 u = 0 := by
  have h := factorTwoCenteredSymmetricPerturbationBilinear_smul_smul
    0 1 u u
  simpa only [zero_smul, one_smul, zero_mul] using h

@[simp] private theorem
    factorTwoCenteredSymmetricPerturbationBilinear_zero_right
    (u : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear u 0 = 0 := by
  have h := factorTwoCenteredSymmetricPerturbationBilinear_smul_smul
    1 0 u u
  simpa only [zero_smul, one_smul, mul_zero, zero_mul] using h

@[simp] private theorem factorTwoCenteredAlternatingCoupling_zero_left
    (u : ℝ → ℝ) : factorTwoCenteredAlternatingCoupling 0 u = 0 := by
  have h := factorTwoCenteredAlternatingCoupling_smul_left 0 u u
  simpa only [zero_smul, zero_mul] using h

@[simp] private theorem factorTwoCenteredAlternatingCoupling_zero_right
    (u : ℝ → ℝ) : factorTwoCenteredAlternatingCoupling u 0 = 0 := by
  have h := factorTwoCenteredAlternatingCoupling_smul_right 0 u u
  simpa only [zero_smul, zero_mul] using h

private theorem abs_phase_coordinate_le_one
    {a b : ℝ} (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    |a| ≤ 1 ∧ |b| ≤ 1 := by
  have haSq : a ^ 2 ≤ (1 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg b]
  have hbSq : b ^ 2 ≤ (1 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg a]
  constructor
  · simpa only [abs_one] using (sq_le_sq.mp haSq)
  · simpa only [abs_one] using (sq_le_sq.mp hbSq)

private theorem abs_canonicalPhaseLowBasisMixed_le
    (k : FactorTwoPhaseLowIndex)
    (e : YoshidaEvenOneNinetyNineTail) (o : YoshidaOddTenTail)
    (heReal : ∀ t : ℝ,
      (evenOneNinetyNineTailToClippedSmooth e t).im = 0)
    (hoReal : ∀ t : ℝ, (oddTenTailToClippedSmooth o t).im = 0)
    (N : ℝ)
    (heN : ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ≤ N)
    (hoN : ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ ≤ N)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    |factorTwoEndpointLowTailMixed
        (canonicalPhaseLowBasisEvenProfile k)
        (boundaryCanonicalEvenTailProfile e)
        (canonicalPhaseLowBasisOddProfile k)
        (canonicalOddTailProfile o) a b| ≤
      (6 / yoshidaA) * N := by
  obtain ⟨ha, hb⟩ := abs_phase_coordinate_le_one hphase
  have hN : 0 ≤ N := (norm_nonneg _).trans heN
  cases k with
  | inl i =>
      let C := factorTwoCenteredCleanPolarization
        (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
        (boundaryCanonicalEvenTailProfile e)
      let P := factorTwoCenteredSymmetricPerturbationBilinear
        (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
        (boundaryCanonicalEvenTailProfile e)
      let J := factorTwoCenteredAlternatingCoupling
        (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
        (canonicalOddTailProfile o)
      have hform : factorTwoEndpointLowTailMixed
          (canonicalPhaseLowBasisEvenProfile (Sum.inl i))
          (boundaryCanonicalEvenTailProfile e)
          (canonicalPhaseLowBasisOddProfile (Sum.inl i))
          (canonicalOddTailProfile o) a b =
        C + a * P + (b / 2) * J := by
        unfold canonicalPhaseLowBasisEvenProfile
          canonicalPhaseLowBasisOddProfile factorTwoEndpointLowTailMixed
          C P J
        simp
      have hC := abs_evenLow_clean_le_formNorm i e heReal
      have hP := abs_evenLow_symmetric_le_formNorm i e heReal
      have hJ := abs_evenLow_oddTail_alternating_le_formNorm i o hoReal
      have hC' : |C| ≤ (1 / yoshidaA) * N := by
        exact hC.trans (mul_le_mul_of_nonneg_left heN
          (div_nonneg (by norm_num) yoshidaA_pos.le))
      have hAP : |a * P| ≤ (3 / yoshidaA) * N := by
        rw [abs_mul]
        calc
          |a| * |P| ≤ |a| * ((3 / yoshidaA) *
              ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖) :=
            mul_le_mul_of_nonneg_left hP (abs_nonneg a)
          _ ≤ 1 * ((3 / yoshidaA) *
              ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖) :=
            mul_le_mul_of_nonneg_right ha
              (mul_nonneg (div_nonneg (by norm_num) yoshidaA_pos.le)
                (norm_nonneg _))
          _ ≤ (3 / yoshidaA) * N := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_left heN
              (div_nonneg (by norm_num) yoshidaA_pos.le)
      have hBJ : |(b / 2) * J| ≤ (2 / yoshidaA) * N := by
        rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        calc
          (|b| / 2) * |J| ≤ (|b| / 2) * ((4 / yoshidaA) *
              ‖(FormSpace.of o : OddPhaseTailFormSpace)‖) :=
            mul_le_mul_of_nonneg_left hJ (div_nonneg (abs_nonneg b) (by norm_num))
          _ ≤ (1 / 2 : ℝ) * ((4 / yoshidaA) *
              ‖(FormSpace.of o : OddPhaseTailFormSpace)‖) := by
            apply mul_le_mul_of_nonneg_right
            · exact div_le_div_of_nonneg_right hb (by norm_num)
            · exact mul_nonneg (div_nonneg (by norm_num) yoshidaA_pos.le)
                (norm_nonneg _)
          _ = (2 / yoshidaA) *
              ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ := by ring
          _ ≤ (2 / yoshidaA) * N :=
            mul_le_mul_of_nonneg_left hoN
              (div_nonneg (by norm_num) yoshidaA_pos.le)
      rw [hform]
      calc
        |C + a * P + (b / 2) * J| ≤
            |C| + |a * P| + |(b / 2) * J| := by
          exact (abs_add_le (C + a * P) ((b / 2) * J)).trans
            (add_le_add (abs_add_le C (a * P)) le_rfl)
        _ ≤ (1 / yoshidaA) * N + (3 / yoshidaA) * N +
            (2 / yoshidaA) * N := add_le_add (add_le_add hC' hAP) hBJ
        _ = (6 / yoshidaA) * N := by ring
  | inr j =>
      let C := factorTwoCenteredCleanPolarization
        (factorTwoCenteredOddLowProfile j) (canonicalOddTailProfile o)
      let P := factorTwoCenteredSymmetricPerturbationBilinear
        (factorTwoCenteredOddLowProfile j) (canonicalOddTailProfile o)
      let J := factorTwoCenteredAlternatingCoupling
        (boundaryCanonicalEvenTailProfile e)
        (factorTwoCenteredOddLowProfile j)
      have hform : factorTwoEndpointLowTailMixed
          (canonicalPhaseLowBasisEvenProfile (Sum.inr j))
          (boundaryCanonicalEvenTailProfile e)
          (canonicalPhaseLowBasisOddProfile (Sum.inr j))
          (canonicalOddTailProfile o) a b =
        C + a * P + (b / 2) * J := by
        unfold canonicalPhaseLowBasisEvenProfile
          canonicalPhaseLowBasisOddProfile factorTwoEndpointLowTailMixed
          C P J
        simp
      have hC := abs_oddLow_clean_le_formNorm j o hoReal
      have hP := abs_oddLow_symmetric_le_formNorm j o hoReal
      have hJ := abs_evenTail_oddLow_alternating_le_formNorm e j heReal
      have hC' : |C| ≤ (1 / yoshidaA) * N := by
        exact hC.trans (mul_le_mul_of_nonneg_left hoN
          (div_nonneg (by norm_num) yoshidaA_pos.le))
      have hAP : |a * P| ≤ (3 / yoshidaA) * N := by
        rw [abs_mul]
        calc
          |a| * |P| ≤ |a| * ((3 / yoshidaA) *
              ‖(FormSpace.of o : OddPhaseTailFormSpace)‖) :=
            mul_le_mul_of_nonneg_left hP (abs_nonneg a)
          _ ≤ 1 * ((3 / yoshidaA) *
              ‖(FormSpace.of o : OddPhaseTailFormSpace)‖) :=
            mul_le_mul_of_nonneg_right ha
              (mul_nonneg (div_nonneg (by norm_num) yoshidaA_pos.le)
                (norm_nonneg _))
          _ ≤ (3 / yoshidaA) * N := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_left hoN
              (div_nonneg (by norm_num) yoshidaA_pos.le)
      have hBJ : |(b / 2) * J| ≤ (2 / yoshidaA) * N := by
        rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        calc
          (|b| / 2) * |J| ≤ (|b| / 2) * ((4 / yoshidaA) *
              ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖) :=
            mul_le_mul_of_nonneg_left hJ (div_nonneg (abs_nonneg b) (by norm_num))
          _ ≤ (1 / 2 : ℝ) * ((4 / yoshidaA) *
              ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖) := by
            apply mul_le_mul_of_nonneg_right
            · exact div_le_div_of_nonneg_right hb (by norm_num)
            · exact mul_nonneg (div_nonneg (by norm_num) yoshidaA_pos.le)
                (norm_nonneg _)
          _ = (2 / yoshidaA) *
              ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ := by ring
          _ ≤ (2 / yoshidaA) * N :=
            mul_le_mul_of_nonneg_left heN
              (div_nonneg (by norm_num) yoshidaA_pos.le)
      rw [hform]
      calc
        |C + a * P + (b / 2) * J| ≤
            |C| + |a * P| + |(b / 2) * J| := by
          exact (abs_add_le (C + a * P) ((b / 2) * J)).trans
            (add_le_add (abs_add_le C (a * P)) le_rfl)
        _ ≤ (1 / yoshidaA) * N + (3 / yoshidaA) * N +
            (2 / yoshidaA) * N := add_le_add (add_le_add hC' hAP) hBJ
        _ = (6 / yoshidaA) * N := by ring

/-- Uniform continuity bound for every real-coordinate canonical low-tail
functional. -/
theorem abs_canonicalPhaseLowBasisTailRealMixedValue_le
    (k : FactorTwoPhaseLowIndex) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    |canonicalPhaseLowBasisTailRealMixedValue k x a b| ≤
      (6 / yoshidaA) * ‖x‖ := by
  exact abs_canonicalPhaseLowBasisMixed_le k
    (evenTailRealPart x.fst.toV) (oddTailRealPart x.snd.toV)
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).re :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth x.snd.toV t).re : ℝ) :
        ℂ)).im) = 0
      simp)
    ‖x‖ (norm_evenTailRealPart_le_core x)
    (norm_oddTailRealPart_le_core x) a b hphase

/-- Uniform continuity bound for every imaginary-coordinate canonical
low-tail functional. -/
theorem abs_canonicalPhaseLowBasisTailImagMixedValue_le
    (k : FactorTwoPhaseLowIndex) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    |canonicalPhaseLowBasisTailImagMixedValue k x a b| ≤
      (6 / yoshidaA) * ‖x‖ := by
  exact abs_canonicalPhaseLowBasisMixed_le k
    (evenTailImagPart x.fst.toV) (oddTailImagPart x.snd.toV)
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).im :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth x.snd.toV t).im : ℝ) :
        ℂ)).im) = 0
      simp)
    ‖x‖ (norm_evenTailImagPart_le_core x)
    (norm_oddTailImagPart_le_core x) a b hphase

/-- Algebraic real-coordinate low-tail functional. -/
def canonicalPhaseLowBasisTailRealLinear
    (k : FactorTwoPhaseLowIndex) (a b : ℝ) :
    CanonicalPhaseTailCore →ₗ[ℝ] ℝ where
  toFun x := canonicalPhaseLowBasisTailRealMixedValue k x a b
  map_add' x y := canonicalPhaseLowBasisTailRealMixedValue_add k x y a b
  map_smul' r x := by
    simpa only [smul_eq_mul] using
      canonicalPhaseLowBasisTailRealMixedValue_smul k r x a b

/-- Algebraic imaginary-coordinate low-tail functional. -/
def canonicalPhaseLowBasisTailImagLinear
    (k : FactorTwoPhaseLowIndex) (a b : ℝ) :
    CanonicalPhaseTailCore →ₗ[ℝ] ℝ where
  toFun x := canonicalPhaseLowBasisTailImagMixedValue k x a b
  map_add' x y := canonicalPhaseLowBasisTailImagMixedValue_add k x y a b
  map_smul' r x := by
    simpa only [smul_eq_mul] using
      canonicalPhaseLowBasisTailImagMixedValue_smul k r x a b

@[simp] theorem canonicalPhaseLowBasisTailRealLinear_apply
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseLowBasisTailRealLinear k a b x =
      canonicalPhaseLowBasisTailRealMixedValue k x a b :=
  rfl

@[simp] theorem canonicalPhaseLowBasisTailImagLinear_apply
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseLowBasisTailImagLinear k a b x =
      canonicalPhaseLowBasisTailImagMixedValue k x a b :=
  rfl

/-- Bounded real-coordinate low-tail functional on the algebraic core. -/
def canonicalPhaseLowBasisTailRealContinuous
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    CanonicalPhaseTailCore →L[ℝ] ℝ :=
  (canonicalPhaseLowBasisTailRealLinear k a b).mkContinuous
    (6 / yoshidaA) (fun x ↦ by
      simpa only [canonicalPhaseLowBasisTailRealLinear_apply,
        Real.norm_eq_abs] using
        abs_canonicalPhaseLowBasisTailRealMixedValue_le k x a b hphase)

/-- Bounded imaginary-coordinate low-tail functional on the algebraic core. -/
def canonicalPhaseLowBasisTailImagContinuous
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    CanonicalPhaseTailCore →L[ℝ] ℝ :=
  (canonicalPhaseLowBasisTailImagLinear k a b).mkContinuous
    (6 / yoshidaA) (fun x ↦ by
      simpa only [canonicalPhaseLowBasisTailImagLinear_apply,
        Real.norm_eq_abs] using
        abs_canonicalPhaseLowBasisTailImagMixedValue_le k x a b hphase)

@[simp] theorem canonicalPhaseLowBasisTailRealContinuous_apply
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) (x : CanonicalPhaseTailCore) :
    canonicalPhaseLowBasisTailRealContinuous k a b hphase x =
      canonicalPhaseLowBasisTailRealMixedValue k x a b :=
  rfl

@[simp] theorem canonicalPhaseLowBasisTailImagContinuous_apply
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) (x : CanonicalPhaseTailCore) :
    canonicalPhaseLowBasisTailImagContinuous k a b hphase x =
      canonicalPhaseLowBasisTailImagMixedValue k x a b :=
  rfl

/-- Completed real-coordinate low-tail functional. -/
def completedCanonicalPhaseLowBasisTailRealFunctional
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    CanonicalPhaseTailCompletion →L[ℝ] ℝ :=
  completionLinearExtension
    (canonicalPhaseLowBasisTailRealContinuous k a b hphase)

/-- Completed imaginary-coordinate low-tail functional. -/
def completedCanonicalPhaseLowBasisTailImagFunctional
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    CanonicalPhaseTailCompletion →L[ℝ] ℝ :=
  completionLinearExtension
    (canonicalPhaseLowBasisTailImagContinuous k a b hphase)

@[simp] theorem completedCanonicalPhaseLowBasisTailRealFunctional_coe
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) (x : CanonicalPhaseTailCore) :
    completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase
        (x : CanonicalPhaseTailCompletion) =
      canonicalPhaseLowBasisTailRealMixedValue k x a b := by
  rw [completedCanonicalPhaseLowBasisTailRealFunctional,
    completionLinearExtension_coe,
    canonicalPhaseLowBasisTailRealContinuous_apply]

@[simp] theorem completedCanonicalPhaseLowBasisTailImagFunctional_coe
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) (x : CanonicalPhaseTailCore) :
    completedCanonicalPhaseLowBasisTailImagFunctional k a b hphase
        (x : CanonicalPhaseTailCompletion) =
      canonicalPhaseLowBasisTailImagMixedValue k x a b := by
  rw [completedCanonicalPhaseLowBasisTailImagFunctional,
    completionLinearExtension_coe,
    canonicalPhaseLowBasisTailImagContinuous_apply]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
