import ArithmeticHodge.Analysis.YoshidaEndpointOddOneThreeRawPolarization
import ArithmeticHodge.Analysis.YoshidaEndpointOddResidualRegularity
import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseFullProfile

set_option autoImplicit false

open Complex MeasureTheory Polynomial Real Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaEndpointOddFullPolarization

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredLowModeThreeL2
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open ShiftedLegendreLogEigen
open ShiftedLegendreLogKernel
open ShiftedLegendreOrthogonality
open ShiftedLogKernelCrossEnergy
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseFullProfile

/-!
# Exact full polarization of the intrinsic odd low block

The centered odd profile is split into its two structural Legendre modes
`P₁,P₃` and an infinite-dimensional residual orthogonal to both.  The
singular raw-log cross is eliminated by the shifted-Legendre eigenidentity,
not by a cutoff or an estimate.  The resulting clean-form polarization keeps
the potential, regular-kernel, and hyperbolic cross terms exactly.
-/

private theorem centeredPullback_centeredP1_eq_neg_shiftedLegendre
    (t : ℝ) :
    centeredPullback centeredP1 t =
      -(shiftedLegendreReal 1).eval t := by
  unfold centeredPullback centeredP1
  calc
    2 * t - 1 =
        -(centeredShiftedLegendreReal 1).eval (2 * t - 1) := by
      rw [eval_centeredShiftedLegendreReal_one]
      ring
    _ = -(shiftedLegendreReal 1).eval (((2 * t - 1) + 1) / 2) := by
      rw [eval_centeredShiftedLegendreReal]
    _ = -(shiftedLegendreReal 1).eval t := by
      congr 2
      ring

private theorem centeredPullback_centeredP3_eq_neg_shiftedLegendre
    (t : ℝ) :
    centeredPullback centeredP3 t =
      -(shiftedLegendreReal 3).eval t := by
  unfold centeredPullback centeredP3
  calc
    (5 * (2 * t - 1) ^ 3 - 3 * (2 * t - 1)) / 2 =
        -(centeredShiftedLegendreReal 3).eval (2 * t - 1) := by
      rw [eval_centeredShiftedLegendreReal_three]
      ring
    _ = -(shiftedLegendreReal 3).eval (((2 * t - 1) + 1) / 2) := by
      rw [eval_centeredShiftedLegendreReal]
    _ = -(shiftedLegendreReal 3).eval t := by
      congr 2
      ring

private theorem integral_centeredPullback_mul_shiftedLegendre_eq_neg_half
    (n : ℕ) (q r : ℝ → ℝ)
    (hmode : ∀ t : ℝ, centeredPullback q t =
      -(shiftedLegendreReal n).eval t) :
    (∫ t : unitInterval,
      centeredPullback r (t : ℝ) * (shiftedLegendreReal n).eval (t : ℝ)) =
      -(1 / 2 : ℝ) * ∫ x : ℝ in -1..1, r x * q x := by
  calc
    (∫ t : unitInterval,
        centeredPullback r (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ)) =
        ∫ t : ℝ in 0..1,
          centeredPullback r t * (shiftedLegendreReal n).eval t := by
      change (∫ t : unitInterval,
        (fun s : ℝ ↦ centeredPullback r s *
          (shiftedLegendreReal n).eval s) (t : ℝ)) = _
      simpa only using integral_unitInterval_eq_intervalIntegral
        (fun s : ℝ ↦ centeredPullback r s *
          (shiftedLegendreReal n).eval s)
    _ = ∫ t : ℝ in 0..1,
        -((fun x : ℝ ↦ r x * q x) (2 * t - 1)) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      have hm := hmode t
      unfold centeredPullback at hm ⊢
      have hp : (shiftedLegendreReal n).eval t =
          -q (2 * t - 1) := by
        linarith
      change r (2 * t - 1) * (shiftedLegendreReal n).eval t =
        -(r (2 * t - 1) * q (2 * t - 1))
      rw [hp]
      ring
    _ = -(∫ t : ℝ in 0..1,
        (fun x : ℝ ↦ r x * q x) (2 * t - 1)) := by
      rw [intervalIntegral.integral_neg]
    _ = -((1 / 2 : ℝ) * ∫ x : ℝ in -1..1, r x * q x) := by
      rw [integral_comp_two_mul_sub_one (fun x : ℝ ↦ r x * q x)]
    _ = _ := by ring

/-- The complete raw-log cross between the intrinsic `P₁/P₃` low
profile and a continuous residual orthogonal to both modes is exactly zero.
The proof treats the two modes as one polynomial eigen-expansion before
integrating the singular kernel. -/
theorem centeredRawLogBilinear_fixedOddLowProfile_tail_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (c d : ℝ) :
    centeredRawLogBilinear (factorTwoOddStructuralLowProfile c d) r = 0 := by
  let p : ℝ[X] :=
    -(c • shiftedLegendreReal 1 + d • shiftedLegendreReal 3)
  let q : ℝ → ℝ := factorTwoOddStructuralLowProfile c d
  let f : unitInterval → ℝ := fun t ↦ centeredPullback r (t : ℝ)
  let U : unitInterval × unitInterval → ℝ := fun z ↦
    (f z.1 - f z.2) * unitIntervalRawPolynomialLogKernel p z
  have hmode (t : ℝ) : centeredPullback q t = p.eval t := by
    have h1 := centeredPullback_centeredP1_eq_neg_shiftedLegendre t
    have h3 := centeredPullback_centeredP3_eq_neg_shiftedLegendre t
    dsimp only [q, p, factorTwoOddStructuralLowProfile]
    simp only [Polynomial.eval_neg, Polynomial.eval_add,
      Polynomial.eval_smul]
    unfold centeredPullback at h1 h3 ⊢
    unfold factorTwoOddStructuralLowProfile
    rw [h1, h3]
    simp only [smul_eq_mul]
    ring
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    exact hr.comp (by fun_prop)
  have hf : Integrable f :=
    hfcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hUInt : Integrable U := by
    simpa only [U] using
      integrable_sub_mul_unitIntervalRawPolynomialLogKernel f hf p
  have hpairOne : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 1).eval (t : ℝ)) = 0 := by
    rw [integral_centeredPullback_mul_shiftedLegendre_eq_neg_half
      1 centeredP1 r centeredPullback_centeredP1_eq_neg_shiftedLegendre,
      integral_mul_centeredP1_eq, hone]
    ring
  have hpairThree : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 3).eval (t : ℝ)) = 0 := by
    rw [integral_centeredPullback_mul_shiftedLegendre_eq_neg_half
      3 centeredP3 r centeredPullback_centeredP3_eq_neg_shiftedLegendre,
      integral_mul_centeredP3_eq, hthree]
    ring
  have hpLog : shiftedLogKernel p =
      -(c • (Polynomial.C 2 * shiftedLegendreReal 1) +
        d • (Polynomial.C (11 / 3 : ℝ) * shiftedLegendreReal 3)) := by
    dsimp only [p]
    rw [map_neg, map_add, map_smul, map_smul,
      shiftedLogKernel_shiftedLegendreReal,
      shiftedLogKernel_shiftedLegendreReal]
    norm_num [harmonic]
  have hIntOne : Integrable (fun t : unitInterval ↦
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 1).eval (t : ℝ)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hfcont.mul
        ((shiftedLegendreReal 1).continuous.comp continuous_subtype_val)
    · exact HasCompactSupport.of_compactSpace _
  have hIntThree : Integrable (fun t : unitInterval ↦
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 3).eval (t : ℝ)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hfcont.mul
        ((shiftedLegendreReal 3).continuous.comp continuous_subtype_val)
    · exact HasCompactSupport.of_compactSpace _
  have hpair : (∫ t : unitInterval,
      f t * (shiftedLogKernel p).eval (t : ℝ)) = 0 := by
    rw [hpLog]
    simp only [Polynomial.eval_neg, Polynomial.eval_add,
      Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_C,
      smul_eq_mul]
    rw [show (fun t : unitInterval ↦
        f t *
          -(c * (2 * (shiftedLegendreReal 1).eval (t : ℝ)) +
            d * ((11 / 3 : ℝ) *
              (shiftedLegendreReal 3).eval (t : ℝ)))) =
        fun t : unitInterval ↦ (-2 * c) *
            (centeredPullback r (t : ℝ) *
              (shiftedLegendreReal 1).eval (t : ℝ)) +
          (-(11 / 3 : ℝ) * d) *
            (centeredPullback r (t : ℝ) *
              (shiftedLegendreReal 3).eval (t : ℝ)) by
      funext t
      dsimp only [f]
      ring,
      integral_add (hIntOne.const_mul (-2 * c))
        (hIntThree.const_mul (-(11 / 3 : ℝ) * d)),
      integral_const_mul, integral_const_mul, hpairOne, hpairThree]
    ring
  have hcross :=
    integral_sub_mul_unitIntervalRawPolynomialLogKernel_eq f hf p
  rw [hpair] at hcross
  norm_num at hcross
  have hUzero : (∫ z, U z) = 0 := by
    simpa only [U] using hcross
  have hiter : (∫ z, U z) =
      ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
        (centeredPullback r s - centeredPullback r t) *
          ((p.eval s - p.eval t) / |s - t|) := by
    calc
      (∫ z, U z) = ∫ s : unitInterval, ∫ t : unitInterval, U (s, t) :=
        MeasureTheory.integral_prod _ hUInt
      _ = ∫ s : unitInterval, ∫ t : ℝ in 0..1,
          (centeredPullback r (s : ℝ) - centeredPullback r t) *
            ((p.eval (s : ℝ) - p.eval t) / |(s : ℝ) - t|) := by
        apply integral_congr_ae
        filter_upwards [] with s
        rw [← integral_unitInterval_eq_intervalIntegral]
        apply integral_congr_ae
        filter_upwards [] with t
        rfl
      _ = _ := by
        rw [← integral_unitInterval_eq_intervalIntegral]
  have hpoint (s t : ℝ) :
      (centeredPullback r s - centeredPullback r t) *
          ((p.eval s - p.eval t) / |s - t|) =
        2 * (((q (2 * s - 1) - q (2 * t - 1)) *
          (r (2 * s - 1) - r (2 * t - 1))) /
            |(2 * s - 1) - (2 * t - 1)|) := by
    rw [← hmode s, ← hmode t,
      show centeredPullback r s = r (2 * s - 1) by rfl,
      show centeredPullback r t = r (2 * t - 1) by rfl,
      show centeredPullback q s = q (2 * s - 1) by rfl,
      show centeredPullback q t = q (2 * t - 1) by rfl,
      show (2 * s - 1) - (2 * t - 1) = 2 * (s - t) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    by_cases hst : |s - t| = 0
    · simp [hst]
    · field_simp [hst]
  have hscaled :
      (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
        (centeredPullback r s - centeredPullback r t) *
          ((p.eval s - p.eval t) / |s - t|)) =
        (1 / 2 : ℝ) * centeredRawLogBilinear q r := by
    let H : ℝ → ℝ → ℝ := fun x y ↦
      ((q x - q y) * (r x - r y)) / |x - y|
    calc
      _ = ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          2 * H (2 * s - 1) (2 * t - 1) := by
        apply intervalIntegral.integral_congr
        intro s _hs
        apply intervalIntegral.integral_congr
        intro t _ht
        exact hpoint s t
      _ = 2 * (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          H (2 * s - 1) (2 * t - 1)) := by
        rw [show (fun s : ℝ ↦ ∫ t : ℝ in 0..1,
            2 * H (2 * s - 1) (2 * t - 1)) =
            fun s ↦ 2 * ∫ t : ℝ in 0..1,
              H (2 * s - 1) (2 * t - 1) by
          funext s
          rw [intervalIntegral.integral_const_mul],
          intervalIntegral.integral_const_mul]
      _ = 2 * ((1 / 4 : ℝ) *
          ∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1, H x y) := by
        rw [integral_integral_comp_two_mul_sub_one H]
      _ = _ := by
        unfold centeredRawLogBilinear
        dsimp only [H]
        ring
  rw [hiter, hscaled] at hUzero
  linarith

/-- The ordinary `L²` cross between the intrinsic odd low block and a
continuous residual with zero `P₁/P₃` coefficients vanishes exactly. -/
theorem integral_fixedOddLowProfile_mul_tail_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (c d : ℝ) :
    (∫ x : ℝ in -1..1,
      factorTwoOddStructuralLowProfile c d x * r x) = 0 := by
  have h1 : IntervalIntegrable
      (fun x : ℝ ↦ r x * centeredP1 x) volume (-1) 1 :=
    (hr.mul (by unfold centeredP1; fun_prop)).intervalIntegrable (-1) 1
  have h3 : IntervalIntegrable
      (fun x : ℝ ↦ r x * centeredP3 x) volume (-1) 1 :=
    (hr.mul (by unfold centeredP3; fun_prop)).intervalIntegrable (-1) 1
  rw [show (fun x : ℝ ↦
      factorTwoOddStructuralLowProfile c d x * r x) =
      fun x ↦ c * (r x * centeredP1 x) +
        d * (r x * centeredP3 x) by
    funext x
    unfold factorTwoOddStructuralLowProfile
    ring,
    intervalIntegral.integral_add (h1.const_mul c) (h3.const_mul d),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_mul_centeredP1_eq, integral_mul_centeredP3_eq,
    hone, hthree]
  ring

/-- Exact clean-form polarization of the intrinsic odd low block against its
residual.  The raw logarithmic energy is split by the all-degree eigenidentity;
all remaining cross terms are retained in the genuine clean bilinear form. -/
theorem yoshidaEndpointOddCleanQuadratic_oddStructuralLow_tail_eq_bilinear
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (c d : ℝ) :
    yoshidaEndpointOddCleanQuadratic
        (factorTwoOddStructuralLowProfile c d + r) =
      yoshidaEndpointOddCleanQuadratic
          (factorTwoOddStructuralLowProfile c d) +
        2 * yoshidaEndpointEvenCleanBilinear
          (factorTwoOddStructuralLowProfile c d) r +
        yoshidaEndpointOddCleanQuadratic r := by
  let p : ℝ → ℝ := factorTwoOddStructuralLowProfile c d
  have hp : Continuous p :=
    continuous_factorTwoOddStructuralLowProfile c d
  have hrawSplit := centeredRawLogEnergy_one_three_add_tail
    r hlocal hone hthree c d
  have hraw : centeredRawLogEnergy (fun x ↦ p x + r x) =
      centeredRawLogEnergy p + centeredRawLogEnergy r := by
    simpa only [p, factorTwoOddStructuralLowProfile]
      using hrawSplit
  have hrawCross : centeredRawLogBilinear p r = 0 :=
    centeredRawLogBilinear_fixedOddLowProfile_tail_eq_zero
      r hr hone hthree c d
  have hpotential := integral_endpointPotential_add_sq p r hp hr
  have hmass := integral_add_sq p r hp hr
  have hregular := yoshidaEndpointRegularQuadratic_add_ofReal p r hp hr
  have hhyper := yoshidaEndpointHyperbolicQuadratic_add_ofReal p r hp hr
  change yoshidaEndpointOddCleanQuadratic (fun x ↦ p x + r x) =
    yoshidaEndpointOddCleanQuadratic p +
      2 * yoshidaEndpointEvenCleanBilinear p r +
      yoshidaEndpointOddCleanQuadratic r
  unfold yoshidaEndpointOddCleanQuadratic
    yoshidaEndpointEvenCleanBilinear
  dsimp only
  rw [hraw, hrawCross, hpotential, hmass, hregular, hhyper]
  simp only [zero_div, add_re]
  ring

/-- On the structural odd low/tail split, the generic clean polarization is
the concrete clean bilinear form.  This identification inherits the exact
raw-energy split from the preceding theorem. -/
theorem factorTwoCenteredCleanPolarization_oddStructuralLow_tail_eq_bilinear
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (c d : ℝ) :
    factorTwoCenteredCleanPolarization
        (factorTwoOddStructuralLowProfile c d) r =
      yoshidaEndpointEvenCleanBilinear
        (factorTwoOddStructuralLowProfile c d) r := by
  have h :=
    yoshidaEndpointOddCleanQuadratic_oddStructuralLow_tail_eq_bilinear
      r hr hlocal hone hthree c d
  unfold factorTwoCenteredCleanPolarization
  rw [h]
  ring

/-- Exact clean quadratic polarization stated with the generic clean
polarization API used by the full factor-two phase decomposition. -/
theorem yoshidaEndpointOddCleanQuadratic_oddStructuralLow_tail_eq_polarization
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (c d : ℝ) :
    yoshidaEndpointOddCleanQuadratic
        (factorTwoOddStructuralLowProfile c d + r) =
      yoshidaEndpointOddCleanQuadratic
          (factorTwoOddStructuralLowProfile c d) +
        2 * factorTwoCenteredCleanPolarization
          (factorTwoOddStructuralLowProfile c d) r +
        yoshidaEndpointOddCleanQuadratic r := by
  rw [factorTwoCenteredCleanPolarization_oddStructuralLow_tail_eq_bilinear
    r hr hlocal hone hthree c d]
  exact yoshidaEndpointOddCleanQuadratic_oddStructuralLow_tail_eq_bilinear
    r hr hlocal hone hthree c d

/-! ## Intrinsic odd low Gram data -/

/-- The `P₁,P₁` entry of the exact clean odd low Gram matrix. -/
def yoshidaEndpointOddLowGram11 : ℝ :=
  yoshidaEndpointOddCleanQuadratic centeredP1

/-- The `P₁,P₃` entry of the exact clean odd low Gram matrix. -/
def yoshidaEndpointOddLowGram13 : ℝ :=
  factorTwoCenteredCleanPolarization centeredP1 centeredP3

/-- The `P₃,P₃` entry of the exact clean odd low Gram matrix. -/
def yoshidaEndpointOddLowGram33 : ℝ :=
  yoshidaEndpointOddCleanQuadratic centeredP3

end

end ArithmeticHodge.Analysis.YoshidaEndpointOddFullPolarization
