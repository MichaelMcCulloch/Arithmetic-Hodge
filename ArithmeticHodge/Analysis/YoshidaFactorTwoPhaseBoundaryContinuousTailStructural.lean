import ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryProductionBridgeFinal
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedTailCoerciveStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousTailStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaEndpointEvenBoundaryProductionBridge
open YoshidaEndpointEvenBoundaryResidual
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseAlternatingCoercivity
open YoshidaFactorTwoPhaseEndpointAdaptedTail
open YoshidaFactorTwoPhaseEndpointAdaptedTailCoerciveStructural
open YoshidaFactorTwoPhaseEvenSchurClosure
open YoshidaFactorTwoPhaseEvenSymmetricBound
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseOddSymmetricBound
open YoshidaFactorTwoPhaseRadiusClosure
open YoshidaFactorTwoPhaseTailCoercivity
open YoshidaEvenHomogeneousCoercivity
open YoshidaOddSpectralMassBridge
open YoshidaOddHomogeneousCoercivity
open YoshidaPointwiseParityCore
open YoshidaSectionSixAnalytic
open YoshidaWeightedTailBounds

/-!
# Boundary-continuous representatives of real even tails

An even periodic Fourier tail need not vanish at the endpoints, so its clipped
representative can jump there.  Subtracting its endpoint constant produces a
zero-trace residual.  Adding the same real constant back after centered
rescaling gives a globally continuous representative which agrees with the
original centered profile throughout `[-1,1]`.

This keeps the underlying tail in the standard cutoff-`199` Hilbert space;
unlike frequency-`200` endpoint adaptation, it does not change the Fourier
carrier on which the existing clean Riesz theory is built.
-/

/-- Continuous centered representative of a real even periodic profile,
formed from its endpoint constant and zero-trace boundary residual. -/
def boundaryContinuousEvenProfile
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA) : ℝ → ℝ :=
  let c := ((((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
    YoshidaClippedSmooth yoshidaA) yoshidaA).re)
  let r := evenBoundaryResidual f
  fun x ↦ c + centeredRescale yoshidaA (fun y ↦
    ((r : YoshidaClippedSmooth yoshidaA) y).re) x

/-- On the centered endpoint interval, the boundary-continuous representative
is exactly the raw centered rescaling of the original clipped profile. -/
theorem boundaryContinuousEvenProfile_eq_centeredRescale
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA)
    (hfReal : ∀ x : ℝ,
      ((((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0))
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    boundaryContinuousEvenProfile f x =
      centeredRescale yoshidaA (fun y ↦
        (((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) y).re) x := by
  have hax : yoshidaA * x ∈ Icc (-yoshidaA) yoshidaA := by
    constructor
    · have h := mul_le_mul_of_nonneg_left hx.1 yoshidaA_pos.le
      simpa only [mul_neg, mul_one] using h
    · have h := mul_le_mul_of_nonneg_left hx.2 yoshidaA_pos.le
      simpa only [mul_one] using h
  have hfa :
      (((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) yoshidaA) =
        (((((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) yoshidaA).re : ℝ) : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hfReal yoshidaA
  unfold boundaryContinuousEvenProfile centeredRescale
  change _ +
      (((evenBoundaryResidual f : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) (yoshidaA * x)).re = _
  unfold evenBoundaryResidual evenBoundaryConstantPart
  simp only [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [periodicCoreOne_apply_of_mem hax, hfa]
  simp only [Complex.sub_re, ofReal_re]
  simp only [mul_one, Complex.ofReal_re]
  ring

/-- The boundary-continuous representative is genuinely continuous on the
whole real line. -/
theorem continuous_boundaryContinuousEvenProfile
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA) :
    Continuous (boundaryContinuousEvenProfile f) := by
  obtain ⟨hneg, hpos⟩ :=
    evenBoundaryResidual_endpoints_zero yoshidaA_pos f
  have hr := continuous_centeredRescale_re_of_endpoints_zero
    yoshidaA_pos (evenBoundaryResidual f) hneg hpos
  exact continuous_const.add (by
    simpa only [boundaryContinuousEvenProfile] using hr)

/-- The boundary-continuous representative preserves even parity. -/
theorem boundaryContinuousEvenProfile_even
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA) :
    Function.Even (boundaryContinuousEvenProfile f) := by
  intro x
  unfold boundaryContinuousEvenProfile centeredRescale
  rw [show yoshidaA * -x = -(yoshidaA * x) by ring]
  change _ +
      (((evenBoundaryResidual f : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) (-(yoshidaA * x))).re =
    _ +
      (((evenBoundaryResidual f : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) (yoshidaA * x)).re
  rw [show
      (((evenBoundaryResidual f : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) (-(yoshidaA * x))).re =
      (((evenBoundaryResidual f : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) (yoshidaA * x)).re by
    exact congrArg Complex.re
      (evenBoundaryResidual_pointwise_even f (yoshidaA * x))]

/-- The standard cutoff-`199` clean coercivity controls the continuous
boundary representative without any endpoint-zero hypothesis on the even
tail itself. -/
theorem evenTail_boundaryContinuous_clean_coercive
    (r : YoshidaClippedPeriodicCore yoshidaA)
    (htail : r ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)
    (hreal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaA) x).im = 0) :
    let f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
      ⟨r, evenTail_pointwise_even yoshidaA_pos 199 r htail⟩
    (102 / 25 : ℝ) * (∫ x : ℝ in -1..1,
        boundaryContinuousEvenProfile f x ^ 2) ≤
      yoshidaEndpointOddCleanQuadratic
        (boundaryContinuousEvenProfile f) := by
  dsimp only
  let f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
    ⟨r, evenTail_pointwise_even yoshidaA_pos 199 r htail⟩
  let raw : ℝ → ℝ := centeredRescale yoshidaA (fun y ↦
    ((r : YoshidaClippedSmooth yoshidaA) y).re)
  let u : ℝ → ℝ := boundaryContinuousEvenProfile f
  have hcoercive := evenOneNinetyNineTail_clipped_form_value_coercive r htail
  change (102 / 25 : ℝ) * clippedIntervalEnergy
      (r : YoshidaClippedSmooth yoshidaA) ≤
    clippedCriticalFormValue yoshidaA yoshidaA_pos
      (r : YoshidaClippedSmooth yoshidaA) at hcoercive
  have henergy := centeredRescale_energy_eq r hreal
  have hprofiles : ∀ x ∈ Icc (-1 : ℝ) 1, u x = raw x := by
    intro x hx
    simpa only [u, raw, f] using
      boundaryContinuousEvenProfile_eq_centeredRescale f hreal hx
  have hintegral :
      (∫ x : ℝ in -1..1, raw x ^ 2) =
        ∫ x : ℝ in -1..1, u x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    change raw x ^ 2 = u x ^ 2
    rw [hprofiles x hx]
  have hbridge := clippedCriticalFormValue_even_eq_clean_add_boundary
    f (by simpa only [f] using hreal)
  change clippedCriticalFormValue yoshidaA yoshidaA_pos
      (r : YoshidaClippedSmooth yoshidaA) =
        yoshidaA * yoshidaEndpointOddCleanQuadratic u at hbridge
  change clippedIntervalEnergy (r : YoshidaClippedSmooth yoshidaA) =
      yoshidaA * ∫ x : ℝ in -1..1, raw x ^ 2 at henergy
  rw [henergy, hintegral, hbridge] at hcoercive
  nlinarith [yoshidaA_pos]

/-- Uniform phase coercivity for the standard, non-endpoint-adapted Fourier
tails.  The even coordinate uses its boundary-continuous representative, so
the carrier remains the full cutoff-`199` tail containing frequency `200`. -/
theorem boundaryContinuous_tail_phase_uniform_clean_reserve
    (re ro : YoshidaClippedPeriodicCore yoshidaA)
    (heTail : re ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)
    (hoTail : ro ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)
    (heReal : ∀ x : ℝ,
      ((re : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal : ∀ x : ℝ,
      ((ro : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let fe : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
      ⟨re, evenTail_pointwise_even yoshidaA_pos 199 re heTail⟩
    let e := boundaryContinuousEvenProfile fe
    let o := centeredRescale yoshidaA (fun x ↦
      ((ro : YoshidaClippedSmooth yoshidaA) x).re)
    (1 / 200 : ℝ) * (yoshidaEndpointOddCleanQuadratic e +
        yoshidaEndpointOddCleanQuadratic o) ≤
      factorTwoEndpointChannelPhase e o a b := by
  dsimp only
  let fe : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
    ⟨re, evenTail_pointwise_even yoshidaA_pos 199 re heTail⟩
  let e : ℝ → ℝ := boundaryContinuousEvenProfile fe
  let o : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((ro : YoshidaClippedSmooth yoshidaA) x).re)
  let Ee : ℝ := ∫ x : ℝ in -1..1, e x ^ 2
  let Eo : ℝ := ∫ x : ℝ in -1..1, o x ^ 2
  have hec : Continuous e := by
    simpa only [e] using continuous_boundaryContinuousEvenProfile fe
  obtain ⟨hoNeg, hoPos⟩ := oddTail_endpoints_zero ro hoTail
  have hoc : Continuous o := by
    simpa only [o] using continuous_centeredRescale_re_of_endpoints_zero
      yoshidaA_pos ro hoNeg hoPos
  have heven : Function.Even e := by
    simpa only [e] using boundaryContinuousEvenProfile_even fe
  have hood : Function.Odd o := by
    intro x
    dsimp only [o, centeredRescale]
    rw [show yoshidaA * -x = -(yoshidaA * x) by ring,
      oddTail_pointwise_odd yoshidaA_pos 10 ro hoTail (yoshidaA * x)]
    rfl
  have hEe : 0 ≤ Ee := by
    dsimp only [Ee]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ ↦ sq_nonneg (e x))
  have hEo : 0 ≤ Eo := by
    dsimp only [Eo]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ ↦ sq_nonneg (o x))
  have hQe : (102 / 25 : ℝ) * Ee ≤
      yoshidaEndpointOddCleanQuadratic e := by
    simpa only [e, Ee, fe] using
      evenTail_boundaryContinuous_clean_coercive re heTail heReal
  have hQo : (38 / 25 : ℝ) * Eo ≤
      yoshidaEndpointOddCleanQuadratic o := by
    simpa only [o, Eo] using oddTail_endpoint_clean_coercive
      ro hoTail hoReal hoNeg hoPos
  have hPeLower : -(3 : ℝ) * Ee ≤
      factorTwoCenteredSymmetricPerturbation e := by
    simpa only [Ee] using
      neg_three_energy_le_even_symmetricPerturbation e hec heven
  have hPeUpper : factorTwoCenteredSymmetricPerturbation e ≤ Ee := by
    simpa only [Ee] using even_symmetricPerturbation_le_energy e hec heven
  have hPoLower : -Eo ≤ factorTwoCenteredSymmetricPerturbation o := by
    simpa only [Eo] using neg_energy_le_odd_symmetricPerturbation o hoc hood
  have hPoUpper : factorTwoCenteredSymmetricPerturbation o ≤
      (3 / 2 : ℝ) * Eo := by
    simpa only [Eo] using
      odd_symmetricPerturbation_le_three_halves_energy o hoc hood
  have hJ : factorTwoCenteredAlternatingCoupling e o ^ 2 ≤
      (625 / 64 : ℝ) * Ee * Eo := by
    simpa only [Ee, Eo, mul_assoc] using
      factorTwoCenteredAlternatingCoupling_sq_le_energy_mul
        e o hec hoc heven hood
  have h := phase_uniform_of_directional_tail_bounds_clean_reserve
    Ee Eo
    (yoshidaEndpointOddCleanQuadratic e)
    (yoshidaEndpointOddCleanQuadratic o)
    (factorTwoCenteredSymmetricPerturbation e)
    (factorTwoCenteredSymmetricPerturbation o)
    (factorTwoCenteredAlternatingCoupling e o)
    a b hEe hEo hQe hQo hPeLower hPeUpper hPoLower hPoUpper hJ hphase
  simpa only [factorTwoEndpointChannelPhase,
    factorTwoEndpointChannelCleanSum, factorTwoEndpointChannelSymmetricSum]
    using h

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
