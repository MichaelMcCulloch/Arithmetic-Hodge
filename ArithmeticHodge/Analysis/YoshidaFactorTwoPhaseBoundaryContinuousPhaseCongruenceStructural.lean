import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEnvelope
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseFullProfile

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousPhaseCongruenceStructural

noncomputable section

open ArithmeticHodge.Analysis
open UnitIntervalLogEnergyAffine
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseFullProfile
open YoshidaRegularKernelBound
open YoshidaRegularKernelSchur

/-!
# Locality of the complete factor-two phase

Every profile evaluation in the centered factor-two channel occurs in
`[-1,1]`.  The lemmas below expose that locality structurally: replacing any
profile by another representative with the same restriction to `[-1,1]`
preserves the clean, symmetric, alternating, and complete phase forms.
-/

/-- Ordered centered correlation depends only on the restrictions of both
profiles to the closed endpoint interval. -/
theorem factorTwoCenteredCrossCorrelation_congr_Icc
    {u u' v v' : ℝ → ℝ}
    (hu : ∀ x ∈ Icc (-1 : ℝ) 1, u x = u' x)
    (hv : ∀ x ∈ Icc (-1 : ℝ) 1, v x = v' x)
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    factorTwoCenteredCrossCorrelation u v t =
      factorTwoCenteredCrossCorrelation u' v' t := by
  unfold factorTwoCenteredCrossCorrelation
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by linarith : (-1 : ℝ) ≤ 1 - t)] at hx
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have htxIcc : t + x ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  change u (t + x) * v x = u' (t + x) * v' x
  rw [hu (t + x) htxIcc, hv x hxIcc]

/-- The symmetric correlation polarization is local to `[-1,1]` in both
entries. -/
theorem factorTwoCenteredCorrelationBilinear_congr_Icc
    {u u' v v' : ℝ → ℝ}
    (hu : ∀ x ∈ Icc (-1 : ℝ) 1, u x = u' x)
    (hv : ∀ x ∈ Icc (-1 : ℝ) 1, v x = v' x)
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    factorTwoCenteredCorrelationBilinear u v t =
      factorTwoCenteredCorrelationBilinear u' v' t := by
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_congr_Icc hu hv ht0 ht2,
    factorTwoCenteredCrossCorrelation_congr_Icc hv hu ht0 ht2]

/-- The complete symmetric perturbation bilinear form, including both retained
prime atoms, depends only on the endpoint-interval restrictions. -/
theorem factorTwoCenteredSymmetricPerturbationBilinear_congr_Icc
    {u u' v v' : ℝ → ℝ}
    (hu : ∀ x ∈ Icc (-1 : ℝ) 1, u x = u' x)
    (hv : ∀ x ∈ Icc (-1 : ℝ) 1, v x = v' x) :
    factorTwoCenteredSymmetricPerturbationBilinear u v =
      factorTwoCenteredSymmetricPerturbationBilinear u' v' := by
  have hint :
      (∫ t : ℝ in 0..2,
          factorTwoSymmetricWeight (yoshidaEndpointA * t) *
            factorTwoCenteredCorrelationBilinear u v t) =
        ∫ t : ℝ in 0..2,
          factorTwoSymmetricWeight (yoshidaEndpointA * t) *
            factorTwoCenteredCorrelationBilinear u' v' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    change factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        factorTwoCenteredCorrelationBilinear u v t =
      factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        factorTwoCenteredCorrelationBilinear u' v' t
    rw [factorTwoCenteredCorrelationBilinear_congr_Icc hu hv ht.1 ht.2]
  have htau := factorTwoPrimeShift_div_endpointA_mem_one_two
  have htau0 : 0 ≤ factorTwoPrimeShift / yoshidaEndpointA :=
    le_trans (by norm_num) htau.1
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  rw [hint,
    factorTwoCenteredCorrelationBilinear_congr_Icc hu hv
      (by norm_num) (by norm_num),
    factorTwoCenteredCorrelationBilinear_congr_Icc hu hv htau0 htau.2]

/-- The symmetric perturbation quadratic is local to `[-1,1]`. -/
theorem factorTwoCenteredSymmetricPerturbation_congr_Icc
    {u u' : ℝ → ℝ}
    (hu : ∀ x ∈ Icc (-1 : ℝ) 1, u x = u' x) :
    factorTwoCenteredSymmetricPerturbation u =
      factorTwoCenteredSymmetricPerturbation u' := by
  calc
    factorTwoCenteredSymmetricPerturbation u =
        factorTwoCenteredSymmetricPerturbationBilinear u u :=
      (factorTwoCenteredSymmetricPerturbationBilinear_self u).symm
    _ = factorTwoCenteredSymmetricPerturbationBilinear u' u' :=
      factorTwoCenteredSymmetricPerturbationBilinear_congr_Icc hu hu
    _ = factorTwoCenteredSymmetricPerturbation u' :=
      factorTwoCenteredSymmetricPerturbationBilinear_self u'

/-- The complete alternating coupling is local to `[-1,1]` in both entries. -/
theorem factorTwoCenteredAlternatingCoupling_congr_Icc
    {u u' v v' : ℝ → ℝ}
    (hu : ∀ x ∈ Icc (-1 : ℝ) 1, u x = u' x)
    (hv : ∀ x ∈ Icc (-1 : ℝ) 1, v x = v' x) :
    factorTwoCenteredAlternatingCoupling u v =
      factorTwoCenteredAlternatingCoupling u' v' := by
  have hint :
      (∫ t : ℝ in 0..2,
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            (factorTwoCenteredCrossCorrelation v u t -
              factorTwoCenteredCrossCorrelation u v t)) =
        ∫ t : ℝ in 0..2,
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            (factorTwoCenteredCrossCorrelation v' u' t -
              factorTwoCenteredCrossCorrelation u' v' t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    change factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation v u t -
          factorTwoCenteredCrossCorrelation u v t) =
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation v' u' t -
          factorTwoCenteredCrossCorrelation u' v' t)
    rw [factorTwoCenteredCrossCorrelation_congr_Icc hv hu ht.1 ht.2,
      factorTwoCenteredCrossCorrelation_congr_Icc hu hv ht.1 ht.2]
  have htau := factorTwoPrimeShift_div_endpointA_mem_one_two
  have htau0 : 0 ≤ factorTwoPrimeShift / yoshidaEndpointA :=
    le_trans (by norm_num) htau.1
  unfold factorTwoCenteredAlternatingCoupling
  rw [hint,
    factorTwoCenteredCrossCorrelation_congr_Icc hv hu htau0 htau.2,
    factorTwoCenteredCrossCorrelation_congr_Icc hu hv htau0 htau.2]

/-- The raw logarithmic energy only sees the endpoint interval. -/
theorem centeredRawLogEnergy_congr_Icc
    {u u' : ℝ → ℝ}
    (hu : ∀ x ∈ Icc (-1 : ℝ) 1, u x = u' x) :
    centeredRawLogEnergy u = centeredRawLogEnergy u' := by
  unfold centeredRawLogEnergy
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hy
  change (u x - u y) ^ 2 / |x - y| =
    (u' x - u' y) ^ 2 / |x - y|
  rw [hu x hx, hu y hy]

/-- The regular-kernel quadratic is unchanged by replacing its argument
outside `[-1,1]`. -/
theorem yoshidaEndpointRegularQuadratic_congr_Icc
    {f g : ℝ → ℂ}
    (hfg : ∀ x ∈ Icc (-1 : ℝ) 1, f x = g x) :
    yoshidaEndpointRegularQuadratic f =
      yoshidaEndpointRegularQuadratic g := by
  let I : Set ℝ := Icc (-1) 1
  let μ : Measure ℝ := volume.restrict I
  change (∫ p : ℝ × ℝ,
      (yoshidaRegularKernel ((Real.log 2 / 2) * |p.1 - p.2|) : ℂ) *
        f p.2 * star (f p.1) ∂μ.prod μ) =
    ∫ p : ℝ × ℝ,
      (yoshidaRegularKernel ((Real.log 2 / 2) * |p.1 - p.2|) : ℂ) *
        g p.2 * star (g p.1) ∂μ.prod μ
  apply integral_congr_ae
  have hpMem : ∀ᵐ p ∂μ.prod μ, p ∈ I ×ˢ I := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  filter_upwards [hpMem] with p hp
  rw [hfg p.2 hp.2, hfg p.1 hp.1]

/-- The hyperbolic rank-two quadratic is local to `[-1,1]`. -/
theorem yoshidaEndpointHyperbolicQuadratic_congr_Icc
    {f g : ℝ → ℂ}
    (hfg : ∀ x ∈ Icc (-1 : ℝ) 1, f x = g x) :
    yoshidaEndpointHyperbolicQuadratic f =
      yoshidaEndpointHyperbolicQuadratic g := by
  have hcosh :
      (∫ x : ℝ in -1..1,
          (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * f x) =
        ∫ x : ℝ in -1..1,
          (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    change (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * f x =
      (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * g x
    rw [hfg x hx]
  have hsinh :
      (∫ x : ℝ in -1..1,
          (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * f x) =
        ∫ x : ℝ in -1..1,
          (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    change (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * f x =
      (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * g x
    rw [hfg x hx]
  unfold yoshidaEndpointHyperbolicQuadratic
  rw [hcosh, hsinh]

/-- The endpoint clean quadratic is local to `[-1,1]`. -/
theorem yoshidaEndpointOddCleanQuadratic_congr_Icc
    {u u' : ℝ → ℝ}
    (hu : ∀ x ∈ Icc (-1 : ℝ) 1, u x = u' x) :
    yoshidaEndpointOddCleanQuadratic u =
      yoshidaEndpointOddCleanQuadratic u' := by
  have hpotential :
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x ^ 2) =
        ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u' x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    change yoshidaEndpointPotential x * u x ^ 2 =
      yoshidaEndpointPotential x * u' x ^ 2
    rw [hu x hx]
  have hmass :
      (∫ x : ℝ in -1..1, u x ^ 2) =
        ∫ x : ℝ in -1..1, u' x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    change u x ^ 2 = u' x ^ 2
    rw [hu x hx]
  have hcomplex : ∀ x ∈ Icc (-1 : ℝ) 1,
      (u x : ℂ) = (u' x : ℂ) := by
    intro x hx
    exact congrArg (fun r : ℝ ↦ (r : ℂ)) (hu x hx)
  let f : ℝ → ℂ := fun x ↦ u x
  let f' : ℝ → ℂ := fun x ↦ u' x
  have hregular : yoshidaEndpointRegularQuadratic f =
      yoshidaEndpointRegularQuadratic f' := by
    apply yoshidaEndpointRegularQuadratic_congr_Icc
    simpa only [f, f'] using hcomplex
  have hhyperbolic : yoshidaEndpointHyperbolicQuadratic f =
      yoshidaEndpointHyperbolicQuadratic f' := by
    apply yoshidaEndpointHyperbolicQuadratic_congr_Icc
    simpa only [f, f'] using hcomplex
  change centeredRawLogEnergy u / 4 +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x ^ 2) -
        yoshidaEndpointScalarMassLoss * (∫ x : ℝ in -1..1, u x ^ 2) -
        yoshidaEndpointA * (yoshidaEndpointRegularQuadratic f).re +
        yoshidaEndpointHyperbolicQuadratic f =
      centeredRawLogEnergy u' / 4 +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u' x ^ 2) -
        yoshidaEndpointScalarMassLoss * (∫ x : ℝ in -1..1, u' x ^ 2) -
        yoshidaEndpointA * (yoshidaEndpointRegularQuadratic f').re +
        yoshidaEndpointHyperbolicQuadratic f'
  rw [centeredRawLogEnergy_congr_Icc hu, hpotential, hmass,
    hregular, hhyperbolic]

/-- The clean polarization is local to `[-1,1]` in both entries. -/
theorem factorTwoCenteredCleanPolarization_congr_Icc
    {u u' v v' : ℝ → ℝ}
    (hu : ∀ x ∈ Icc (-1 : ℝ) 1, u x = u' x)
    (hv : ∀ x ∈ Icc (-1 : ℝ) 1, v x = v' x) :
    factorTwoCenteredCleanPolarization u v =
      factorTwoCenteredCleanPolarization u' v' := by
  have huv : ∀ x ∈ Icc (-1 : ℝ) 1,
      (u + v) x = (u' + v') x := by
    intro x hx
    simp only [Pi.add_apply]
    rw [hu x hx, hv x hx]
  unfold factorTwoCenteredCleanPolarization
  rw [yoshidaEndpointOddCleanQuadratic_congr_Icc huv,
    yoshidaEndpointOddCleanQuadratic_congr_Icc hu,
    yoshidaEndpointOddCleanQuadratic_congr_Icc hv]

/-- The complete low--tail polarization depends only on the endpoint-interval
restrictions of all four profiles. -/
theorem factorTwoEndpointLowTailMixed_congr_Icc
    {uLow uLow' uTail uTail' vLow vLow' vTail vTail' : ℝ → ℝ}
    (huLow : ∀ x ∈ Icc (-1 : ℝ) 1, uLow x = uLow' x)
    (huTail : ∀ x ∈ Icc (-1 : ℝ) 1, uTail x = uTail' x)
    (hvLow : ∀ x ∈ Icc (-1 : ℝ) 1, vLow x = vLow' x)
    (hvTail : ∀ x ∈ Icc (-1 : ℝ) 1, vTail x = vTail' x)
    (a b : ℝ) :
    factorTwoEndpointLowTailMixed uLow uTail vLow vTail a b =
      factorTwoEndpointLowTailMixed uLow' uTail' vLow' vTail' a b := by
  unfold factorTwoEndpointLowTailMixed
  rw [factorTwoCenteredCleanPolarization_congr_Icc huLow huTail,
    factorTwoCenteredCleanPolarization_congr_Icc hvLow hvTail,
    factorTwoCenteredSymmetricPerturbationBilinear_congr_Icc huLow huTail,
    factorTwoCenteredSymmetricPerturbationBilinear_congr_Icc hvLow hvTail,
    factorTwoCenteredAlternatingCoupling_congr_Icc huLow hvTail,
    factorTwoCenteredAlternatingCoupling_congr_Icc huTail hvLow]

/-- The complete one-channel phase only depends on the restrictions of its two
profiles to `[-1,1]`.  This is the representative-change theorem used by the
boundary-continuous low--tail assembly. -/
theorem factorTwoEndpointChannelPhase_congr_Icc
    {u u' v v' : ℝ → ℝ}
    (hu : ∀ x ∈ Icc (-1 : ℝ) 1, u x = u' x)
    (hv : ∀ x ∈ Icc (-1 : ℝ) 1, v x = v' x)
    (a b : ℝ) :
    factorTwoEndpointChannelPhase u v a b =
      factorTwoEndpointChannelPhase u' v' a b := by
  unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
  rw [yoshidaEndpointOddCleanQuadratic_congr_Icc hu,
    yoshidaEndpointOddCleanQuadratic_congr_Icc hv,
    factorTwoCenteredSymmetricPerturbation_congr_Icc hu,
    factorTwoCenteredSymmetricPerturbation_congr_Icc hv,
    factorTwoCenteredAlternatingCoupling_congr_Icc hu hv]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousPhaseCongruenceStructural
