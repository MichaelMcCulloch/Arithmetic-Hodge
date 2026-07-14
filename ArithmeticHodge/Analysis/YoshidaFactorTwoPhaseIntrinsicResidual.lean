import ArithmeticHodge.Analysis.CenteredOddOneThreeEnergy
import ArithmeticHodge.Analysis.UnitIntervalLogEnergyLipschitz
import ArithmeticHodge.Analysis.YoshidaEndpointEvenMeanZeroPositive
import ArithmeticHodge.Analysis.YoshidaEndpointPullbackLipschitz
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseFullProfile
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSingularSquare

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicResidual

open CenteredOddOneThreeEnergy
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaEndpointPullbackLipschitz
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseSingularSquare
open YoshidaRegularKernelSchur

noncomputable section

/-!
# Intrinsic residual reserve for the factor-two phase

This file keeps the reflected Cauchy pole inside its exact two-vector square.
For profiles orthogonal to the intrinsic `P₀/P₂` and `P₁/P₃` blocks, the
infinite shifted-Legendre spectrum then leaves an explicit coercive reserve.
All other signed regular and prime terms are retained in one exact remainder;
no Fourier cutoff or finite enumeration is used.
-/

/-- The centered `L²` energy, named locally to keep the signed formulas legible. -/
def factorTwoIntrinsicEnergy (w : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in -1..1, w x ^ 2

/-- The endpoint potential part of the clean quadratic. -/
def factorTwoIntrinsicPotentialEnergy (w : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2

theorem factorTwoIntrinsicEnergy_nonneg (w : ℝ → ℝ) :
    0 ≤ factorTwoIntrinsicEnergy w := by
  unfold factorTwoIntrinsicEnergy
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x _hx
  positivity

theorem factorTwoIntrinsicPotentialEnergy_nonneg (w : ℝ → ℝ) :
    0 ≤ factorTwoIntrinsicPotentialEnergy w := by
  unfold factorTwoIntrinsicPotentialEnergy
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  exact mul_nonneg (yoshidaEndpointPotential_nonneg_on_Icc hx) (sq_nonneg _)

/-- The raw/potential block together with the signed reflected Cauchy pole. -/
def factorTwoIntrinsicProtectedBlock
    (u v : ℝ → ℝ) (a b : ℝ) : ℝ :=
  centeredRawLogEnergy u / 4 + factorTwoIntrinsicPotentialEnergy u +
    centeredRawLogEnergy v / 4 + factorTwoIntrinsicPotentialEnergy v -
    (1 / 2 : ℝ) *
      (∫ t : ℝ in 0..2,
        factorTwoCenteredPhaseCorrelation u v a (-b) t / (2 - t))

/-- Every term of the phase form not protected by the reflected singular
square.  The forward and reflected regular branches and both prime atoms
remain signed. -/
def factorTwoIntrinsicSignedRemainder
    (u v : ℝ → ℝ) (a b : ℝ) : ℝ :=
  yoshidaEndpointA *
      (∫ t : ℝ in 0..2,
        factorTwoCenteredForwardPhaseKernel u v a b t) +
    (∫ t : ℝ in 0..2,
      factorTwoCenteredReflectedDesingularizedPhaseKernel u v a b t) -
    (Real.log 2 / Real.sqrt 2) * a *
      (factorTwoIntrinsicEnergy u + factorTwoIntrinsicEnergy v) -
    (Real.log 3 / Real.sqrt 3) *
      factorTwoCenteredPhaseCorrelation u v a b
        (factorTwoPrimeShift / yoshidaEndpointA) -
    yoshidaEndpointScalarMassLoss *
      (factorTwoIntrinsicEnergy u + factorTwoIntrinsicEnergy v) -
    yoshidaEndpointA *
      ((yoshidaEndpointRegularQuadratic (fun x ↦ (u x : ℂ))).re +
        (yoshidaEndpointRegularQuadratic (fun x ↦ (v x : ℂ))).re) +
    yoshidaEndpointHyperbolicQuadratic (fun x ↦ (u x : ℂ)) +
    yoshidaEndpointHyperbolicQuadratic (fun x ↦ (v x : ℂ))

/-- Exact phase decomposition into the singular-square protected block and
the remaining signed regular/prime operator. -/
theorem factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) :
    factorTwoEndpointChannelPhase u v a b =
      factorTwoIntrinsicProtectedBlock u v a b +
        factorTwoIntrinsicSignedRemainder u v a b := by
  have hphase :=
    phase_symmetric_add_alternating_eq_regular_sub_pole_sub_primes
      u v hu hv a b
  unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
  calc
    _ = yoshidaEndpointOddCleanQuadratic u +
          yoshidaEndpointOddCleanQuadratic v +
        (a * (factorTwoCenteredSymmetricPerturbation u +
            factorTwoCenteredSymmetricPerturbation v) +
          b * factorTwoCenteredAlternatingCoupling u v) := by ring
    _ = _ := by
      rw [hphase]
      unfold yoshidaEndpointOddCleanQuadratic
        factorTwoIntrinsicProtectedBlock factorTwoIntrinsicSignedRemainder
        factorTwoIntrinsicEnergy factorTwoIntrinsicPotentialEnergy
      ring

/-- The exact endpoint square retains all of the raw logarithmic energy and
half of the potential, losing only half of the elementary `log 2` mass.  This
is stronger than discarding the singular square after proving it nonnegative. -/
theorem raw_add_half_potential_sub_half_logMass_le_protected
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hlocalu : LocallyLipschitzOn (Icc (-1) 1) u)
    (hlocalv : LocallyLipschitzOn (Icc (-1) 1) v)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    centeredRawLogEnergy u / 4 + centeredRawLogEnergy v / 4 +
        (1 / 2 : ℝ) *
          (factorTwoIntrinsicPotentialEnergy u +
            factorTwoIntrinsicPotentialEnergy v) -
        (Real.log 2 / 2) *
          (factorTwoIntrinsicEnergy u + factorTwoIntrinsicEnergy v) ≤
      factorTwoIntrinsicProtectedBlock u v a b := by
  have hphase :=
    centeredEnergy_add_potential_add_logMass_sub_half_phasePole_eq_square
      u v hu hv hlocalu hlocalv a b
  have hzero :=
    centeredEnergy_add_potential_add_logMass_sub_half_phasePole_eq_square
      u v hu hv hlocalu hlocalv 0 0
  have hretain := half_integral_singularSquare_zero_add_quarter_raw_le
    u v hu hv hlocalu hlocalv a b hab
  have hzero' :
      (centeredRawLogEnergy u / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x ^ 2) +
          Real.log 2 * (∫ x : ℝ in -1..1, u x ^ 2)) +
        (centeredRawLogEnergy v / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * v x ^ 2) +
          Real.log 2 * (∫ x : ℝ in -1..1, v x ^ 2)) =
        (1 / 2 : ℝ) *
          (∫ r : ℝ in 0..2,
            factorTwoPhaseSingularSquareNumerator u v 0 0 r / r) := by
    simpa [factorTwoCenteredPhaseCorrelation] using hzero
  unfold factorTwoIntrinsicProtectedBlock factorTwoIntrinsicPotentialEnergy
    factorTwoIntrinsicEnergy
  linarith [hzero']

/-- Local Lipschitz regularity supplies the even form domain, so annihilating
`P₀/P₂` exposes the full degree-four-and-higher spectral gap. -/
theorem even_intrinsic_residual_raw_reserve
    (e : ℝ → ℝ) (hec : Continuous e) (he : Function.Even e)
    (he0 : centeredEvenP0Coefficient e = 0)
    (he2 : centeredEvenP2Coefficient e = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e) :
    (25 / 12 : ℝ) * factorTwoIntrinsicEnergy e ≤
      centeredRawLogEnergy e / 4 := by
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback e helocal
  let f : unitInterval → ℝ := fun t ↦ centeredPullback e (t : ℝ)
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hfmem : MemLp f 2 :=
    hfcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hspectral := centered_even_zero_two_tail_energy_le e hec
    (by simpa only [f] using hfmem) (by simpa only [f] using henergy) he
  have hresidual : centeredEvenZeroTwoResidual e = e := by
    funext x
    unfold centeredEvenZeroTwoResidual
    rw [he0, he2]
    ring
  rw [hresidual, he2] at hspectral
  unfold factorTwoIntrinsicEnergy
  norm_num at hspectral ⊢
  exact hspectral

/-- The odd intrinsic residual starts at shifted-Legendre degree five. -/
theorem odd_intrinsic_residual_raw_reserve
    (o : ℝ → ℝ) (hoc : Continuous o) (ho : Function.Odd o)
    (ho1 : centeredOddP1Coefficient o = 0)
    (ho3 : centeredOddP3Coefficient o = 0)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o) :
    (137 / 60 : ℝ) * factorTwoIntrinsicEnergy o ≤
      centeredRawLogEnergy o / 4 := by
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback o holocal
  let f : unitInterval → ℝ := fun t ↦ centeredPullback o (t : ℝ)
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hfmem : MemLp f 2 :=
    hfcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hspectral := centered_odd_one_three_tail_energy_le o hoc
    (by simpa only [f] using hfmem) (by simpa only [f] using henergy) ho
  have hresidual : centeredOddOneThreeResidual o = o := by
    funext x
    unfold centeredOddOneThreeResidual
    rw [ho1, ho3]
    ring
  rw [hresidual, ho1, ho3] at hspectral
  unfold factorTwoIntrinsicEnergy
  norm_num at hspectral ⊢
  exact hspectral

/-- Combining the exact singular-square retention with the two infinite
spectral gaps gives the intrinsic residual reserve.  Notice that no absolute
value has yet been put on the regular or prime remainder. -/
theorem intrinsic_residual_spectral_reserve_le_protected
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (he2 : centeredEvenP2Coefficient e = 0)
    (ho1 : centeredOddP1Coefficient o = 0)
    (ho3 : centeredOddP3Coefficient o = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (25 / 12 - Real.log 2 / 2) * factorTwoIntrinsicEnergy e +
        (137 / 60 - Real.log 2 / 2) * factorTwoIntrinsicEnergy o +
        (1 / 2 : ℝ) *
          (factorTwoIntrinsicPotentialEnergy e +
            factorTwoIntrinsicPotentialEnergy o) ≤
      factorTwoIntrinsicProtectedBlock e o a b := by
  have heRaw := even_intrinsic_residual_raw_reserve
    e hec he he0 he2 helocal
  have hoRaw := odd_intrinsic_residual_raw_reserve
    o hoc ho ho1 ho3 holocal
  have hsquare := raw_add_half_potential_sub_half_logMass_le_protected
    e o hec hoc helocal holocal a b hab
  linarith

/-- The explicit reserve left by the singular square and the intrinsic
spectral gaps is itself nonnegative. -/
theorem intrinsic_residual_spectral_reserve_nonneg
    (e o : ℝ → ℝ) :
    0 ≤ (25 / 12 - Real.log 2 / 2) * factorTwoIntrinsicEnergy e +
        (137 / 60 - Real.log 2 / 2) * factorTwoIntrinsicEnergy o +
        (1 / 2 : ℝ) *
          (factorTwoIntrinsicPotentialEnergy e +
            factorTwoIntrinsicPotentialEnergy o) := by
  have hlog : Real.log 2 < 7 / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hecoeff : 0 ≤ 25 / 12 - Real.log 2 / 2 := by linarith
  have hocoeff : 0 ≤ 137 / 60 - Real.log 2 / 2 := by linarith
  have heEnergy := factorTwoIntrinsicEnergy_nonneg e
  have hoEnergy := factorTwoIntrinsicEnergy_nonneg o
  have hePotential := factorTwoIntrinsicPotentialEnergy_nonneg e
  have hoPotential := factorTwoIntrinsicPotentialEnergy_nonneg o
  positivity

/-- Consequently the square-protected block alone is positive on the
intrinsic residual subspace. -/
theorem factorTwoIntrinsicProtectedBlock_nonneg_of_intrinsic_residual
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (he2 : centeredEvenP2Coefficient e = 0)
    (ho1 : centeredOddP1Coefficient o = 0)
    (ho3 : centeredOddP3Coefficient o = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoIntrinsicProtectedBlock e o a b := by
  exact (intrinsic_residual_spectral_reserve_nonneg e o).trans
    (intrinsic_residual_spectral_reserve_le_protected
      e o hec hoc he ho he0 he2 ho1 ho3 helocal holocal a b hab)

/-- The complete phase is bounded below by the intrinsic spectral reserve
plus the exact signed regular/prime remainder. -/
theorem intrinsic_residual_reserve_add_signedRemainder_le_phase
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (he2 : centeredEvenP2Coefficient e = 0)
    (ho1 : centeredOddP1Coefficient o = 0)
    (ho3 : centeredOddP3Coefficient o = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (25 / 12 - Real.log 2 / 2) * factorTwoIntrinsicEnergy e +
        (137 / 60 - Real.log 2 / 2) * factorTwoIntrinsicEnergy o +
        (1 / 2 : ℝ) *
          (factorTwoIntrinsicPotentialEnergy e +
            factorTwoIntrinsicPotentialEnergy o) +
        factorTwoIntrinsicSignedRemainder e o a b ≤
      factorTwoEndpointChannelPhase e o a b := by
  have hreserve := intrinsic_residual_spectral_reserve_le_protected
    e o hec hoc he ho he0 he2 ho1 ho3 helocal holocal a b hab
  rw [factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
    e o hec hoc a b]
  linarith

/-- Sharp square-protected sufficient condition for the complete intrinsic
residual phase.  This theorem isolates the sole remaining analytic task: the
signed regular/prime operator may spend, but not exceed, the displayed raw
spectral reserve. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_intrinsic_signedRemainder
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (he2 : centeredEvenP2Coefficient e = 0)
    (ho1 : centeredOddP1Coefficient o = 0)
    (ho3 : centeredOddP3Coefficient o = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hrem :
      -factorTwoIntrinsicSignedRemainder e o a b ≤
        (25 / 12 - Real.log 2 / 2) * factorTwoIntrinsicEnergy e +
          (137 / 60 - Real.log 2 / 2) * factorTwoIntrinsicEnergy o +
          (1 / 2 : ℝ) *
            (factorTwoIntrinsicPotentialEnergy e +
              factorTwoIntrinsicPotentialEnergy o)) :
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  have hphase := intrinsic_residual_reserve_add_signedRemainder_le_phase
    e o hec hoc he ho he0 he2 ho1 ho3 helocal holocal a b hab
  linarith

/-!
## Exact obstruction to the coarse `L²` Schur route

The next facts concern only the currently available scalar bounds.  They are
not a counterexample to phase positivity.  They prove that combining the
mass reserves `41/60`, `53/60` with the generic alternating constant `25/8`
cannot establish the needed Schur determinant.
-/

theorem intrinsic_coarse_mass_schur_exact_deficit :
    (25 / 8 : ℝ) ^ 2 -
        4 * (41 / 60 : ℝ) * (53 / 60 : ℝ) =
      105857 / 14400 := by
  norm_num

theorem intrinsic_coarse_mass_schur_does_not_close :
    4 * (41 / 60 : ℝ) * (53 / 60 : ℝ) < (25 / 8 : ℝ) ^ 2 := by
  norm_num

/-- An abstract saturating model witnesses the logical gap in the coarse
mass-only inequalities.  It deliberately makes no assertion that profiles
saturating all three estimates exist. -/
theorem exists_coarse_mass_bounds_without_schur_determinant :
    ∃ Ee Eo Qe Qo J : ℝ,
      0 ≤ Ee ∧ 0 ≤ Eo ∧
      (41 / 60 : ℝ) * Ee ≤ Qe ∧
      (53 / 60 : ℝ) * Eo ≤ Qo ∧
      J ^ 2 ≤ (625 / 64 : ℝ) * Ee * Eo ∧
      4 * Qe * Qo < J ^ 2 := by
  refine ⟨1, 1, 41 / 60, 53 / 60, 25 / 8, ?_⟩
  norm_num

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicResidual
