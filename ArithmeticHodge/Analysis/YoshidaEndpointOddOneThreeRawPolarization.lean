import ArithmeticHodge.Analysis.CenteredOddOneThreeEnergy
import ArithmeticHodge.Analysis.YoshidaEndpointEvenTailRepresenter
import ArithmeticHodge.Analysis.YoshidaEndpointOddResidualRegularity

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaEndpointOddOneThreeRawPolarization

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredLowModeL2
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
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOcticTwoModeSchurData
open YoshidaEndpointPullbackLipschitz

noncomputable section

/-!
# Structural raw-log polarization of the centered odd low modes

The logarithmic difference operator diagonalizes on every shifted-Legendre
degree.  Transporting that all-degree identity through `t ↦ 2t - 1`
shows that a residual orthogonal to the centered degree-one and degree-three
modes has exactly zero raw-log cross pairing with those modes.  No finite
mode truncation is used.
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

/-- A centered mode whose pullback is the negative shifted-Legendre mode of
degree `n` has zero raw-log pairing with every continuous residual that is
`L²`-orthogonal to that mode.  The proof uses the exact all-degree
shifted-Legendre eigenidentity. -/
private theorem centeredRawLogBilinear_mode_tail_eq_zero
    (n : ℕ) (q r : ℝ → ℝ) (hr : Continuous r)
    (hmode : ∀ t : ℝ, centeredPullback q t =
      -(shiftedLegendreReal n).eval t)
    (hortho : (∫ x : ℝ in -1..1, r x * q x) = 0) :
    centeredRawLogBilinear q r = 0 := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback r (t : ℝ)
  let p : ℝ[X] := shiftedLegendreReal n
  let U : unitInterval × unitInterval → ℝ := fun z ↦
    (f z.1 - f z.2) * unitIntervalRawPolynomialLogKernel p z
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    exact hr.comp (by fun_prop)
  have hf : Integrable f :=
    hfcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hUInt : Integrable U := by
    simpa only [U] using
      integrable_sub_mul_unitIntervalRawPolynomialLogKernel f hf p
  have hcross :=
    integral_sub_mul_unitIntervalRawPolynomialLogKernel_eq f hf p
  have hpull : (∫ t : unitInterval, f t * p.eval (t : ℝ)) =
      -(1 / 2 : ℝ) * ∫ x : ℝ in -1..1, r x * q x := by
    simpa only [f, p] using
      integral_centeredPullback_mul_shiftedLegendre_eq_neg_half
        n q r hmode
  have hpair : (∫ t : unitInterval,
      f t * (shiftedLogKernel p).eval (t : ℝ)) = 0 := by
    rw [show shiftedLogKernel p =
        Polynomial.C (2 * (harmonic n : ℝ)) * p by
      dsimp only [p]
      exact shiftedLogKernel_shiftedLegendreReal n]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [show (∫ t : unitInterval,
        f t * ((2 * (harmonic n : ℝ)) * p.eval (t : ℝ))) =
        (2 * (harmonic n : ℝ)) *
          ∫ t : unitInterval, f t * p.eval (t : ℝ) by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring,
      hpull, hortho]
    ring
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
  rw [hiter] at hUzero
  have hpoint (s t : ℝ) :
      (centeredPullback r s - centeredPullback r t) *
          ((p.eval s - p.eval t) / |s - t|) =
        -2 * (((q (2 * s - 1) - q (2 * t - 1)) *
          (r (2 * s - 1) - r (2 * t - 1))) /
            |(2 * s - 1) - (2 * t - 1)|) := by
    have hms := hmode s
    have hmt := hmode t
    unfold centeredPullback at hms hmt ⊢
    have hps : p.eval s = -q (2 * s - 1) := by
      dsimp only [p]
      linarith
    have hpt : p.eval t = -q (2 * t - 1) := by
      dsimp only [p]
      linarith
    rw [hps, hpt,
      show (2 * s - 1) - (2 * t - 1) = 2 * (s - t) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    by_cases hst : |s - t| = 0
    · simp [hst]
    · field_simp [hst]
      ring
  have hscaled :
      (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
        (centeredPullback r s - centeredPullback r t) *
          ((p.eval s - p.eval t) / |s - t|)) =
        -(1 / 2 : ℝ) * centeredRawLogBilinear q r := by
    let H : ℝ → ℝ → ℝ := fun x y ↦
      ((q x - q y) * (r x - r y)) / |x - y|
    calc
      _ = ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          -2 * H (2 * s - 1) (2 * t - 1) := by
        apply intervalIntegral.integral_congr
        intro s _hs
        apply intervalIntegral.integral_congr
        intro t _ht
        exact hpoint s t
      _ = -2 * (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          H (2 * s - 1) (2 * t - 1)) := by
        rw [show (fun s : ℝ ↦ ∫ t : ℝ in 0..1,
            -2 * H (2 * s - 1) (2 * t - 1)) =
            fun s ↦ -2 * ∫ t : ℝ in 0..1,
              H (2 * s - 1) (2 * t - 1) by
          funext s
          rw [intervalIntegral.integral_const_mul],
          intervalIntegral.integral_const_mul]
      _ = -2 * ((1 / 4 : ℝ) *
          ∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1, H x y) := by
        rw [integral_integral_comp_two_mul_sub_one H]
      _ = _ := by
        unfold centeredRawLogBilinear
        dsimp only [H]
        ring
  rw [hscaled] at hUzero
  linarith

/-- Raw-log orthogonality of the centered degree-one mode and a continuous
residual with vanishing degree-one coefficient. -/
theorem centeredRawLogBilinear_centeredP1_tail_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r)
    (hone : centeredOddP1Coefficient r = 0) :
    centeredRawLogBilinear centeredP1 r = 0 := by
  apply centeredRawLogBilinear_mode_tail_eq_zero 1 centeredP1 r hr
    centeredPullback_centeredP1_eq_neg_shiftedLegendre
  rw [integral_mul_centeredP1_eq, hone]
  ring

/-- Raw-log orthogonality of the centered degree-three mode and a continuous
residual with vanishing degree-three coefficient. -/
theorem centeredRawLogBilinear_centeredP3_tail_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r)
    (hthree : centeredOddP3Coefficient r = 0) :
    centeredRawLogBilinear centeredP3 r = 0 := by
  apply centeredRawLogBilinear_mode_tail_eq_zero 3 centeredP3 r hr
    centeredPullback_centeredP3_eq_neg_shiftedLegendre
  rw [integral_mul_centeredP3_eq, hthree]
  ring

/-- Exact raw-energy splitting between a centered polynomial profile and a
locally Lipschitz residual whose pairing with the logarithmic image of that
polynomial vanishes. -/
private theorem centeredRawLogEnergy_add_polynomial_tail
    (p : ℝ[X]) (q r : ℝ → ℝ)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (hmode : ∀ t : unitInterval,
      centeredPullback q (t : ℝ) = p.eval (t : ℝ))
    (hpair : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLogKernel p).eval (t : ℝ)) = 0) :
    centeredRawLogEnergy (fun x ↦ q x + r x) =
      centeredRawLogEnergy q + centeredRawLogEnergy r := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback r (t : ℝ)
  let pfun : unitInterval → ℝ := fun t ↦ p.eval (t : ℝ)
  let g : unitInterval → ℝ := fun t ↦
    centeredPullback (fun x ↦ q x + r x) (t : ℝ)
  let U : unitInterval × unitInterval → ℝ := fun z ↦
    (f z.1 - f z.2) * unitIntervalRawPolynomialLogKernel p z
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback r hlocal
  have hfEnergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hfcont : Continuous f := by
    simpa only [f] using hLip.continuous
  have hf : Integrable f :=
    hfcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpEq : pfun = fun t : unitInterval ↦ p.eval (t : ℝ) := rfl
  have hpEnergy : Integrable (unitIntervalRawLogEnergyIntegrand pfun) := by
    rw [hpEq]
    exact integrable_unitIntervalRawLogEnergyIntegrand_polynomial p
  have hUInt : Integrable U := by
    simpa only [U] using
      integrable_sub_mul_unitIntervalRawPolynomialLogKernel f hf p
  have hcrossEq :=
    integral_sub_mul_unitIntervalRawPolynomialLogKernel_eq f hf p
  have hUzero : (∫ z, U z) = 0 := by
    rw [hpair] at hcrossEq
    norm_num at hcrossEq
    simpa only [U, f] using hcrossEq
  have hgPoint (t : unitInterval) : g t = pfun t + f t := by
    dsimp only [g, pfun, f, centeredPullback]
    have hm := hmode t
    unfold centeredPullback at hm
    rw [hm]
  have hpoint (z : unitInterval × unitInterval) :
      unitIntervalRawLogEnergyIntegrand g z =
        unitIntervalRawLogEnergyIntegrand pfun z +
          unitIntervalRawLogEnergyIntegrand f z + 2 * U z := by
    unfold unitIntervalRawLogEnergyIntegrand U
      unitIntervalRawPolynomialLogKernel
    rw [hgPoint z.1, hgPoint z.2]
    dsimp only [pfun]
    ring
  have hcombo : Integrable (fun z : unitInterval × unitInterval ↦
      unitIntervalRawLogEnergyIntegrand pfun z +
        unitIntervalRawLogEnergyIntegrand f z + 2 * U z) :=
    (hpEnergy.add hfEnergy).add (hUInt.const_mul 2)
  have hgEnergy : Integrable (unitIntervalRawLogEnergyIntegrand g) := by
    apply hcombo.congr
    filter_upwards [] with z
    exact (hpoint z).symm
  have hIntegralExpand :
      (∫ z, unitIntervalRawLogEnergyIntegrand pfun z +
          unitIntervalRawLogEnergyIntegrand f z + 2 * U z) =
        (∫ z, unitIntervalRawLogEnergyIntegrand pfun z) +
          (∫ z, unitIntervalRawLogEnergyIntegrand f z) +
            2 * (∫ z, U z) := by
    calc
      _ = (∫ z, unitIntervalRawLogEnergyIntegrand pfun z +
            unitIntervalRawLogEnergyIntegrand f z) + ∫ z, 2 * U z := by
        exact integral_add (hpEnergy.add hfEnergy) (hUInt.const_mul 2)
      _ = ((∫ z, unitIntervalRawLogEnergyIntegrand pfun z) +
            ∫ z, unitIntervalRawLogEnergyIntegrand f z) +
          ∫ z, 2 * U z := by
        rw [integral_add hpEnergy hfEnergy]
      _ = _ := by rw [integral_const_mul]
  have hunitExpand : unitIntervalLogEnergy g =
      unitIntervalLogEnergy pfun + unitIntervalLogEnergy f := by
    unfold unitIntervalLogEnergy
    rw [show (∫ z, unitIntervalRawLogEnergyIntegrand g z) =
        ∫ z, unitIntervalRawLogEnergyIntegrand pfun z +
          unitIntervalRawLogEnergyIntegrand f z + 2 * U z by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hpoint z,
      hIntegralExpand, hUzero]
    ring
  have hbridgeG : unitIntervalLogEnergy g =
      (1 / 4 : ℝ) *
        centeredRawLogEnergy (fun x ↦ q x + r x) := by
    simpa only [g] using unitIntervalLogEnergy_centeredPullback
      (fun x ↦ q x + r x) hgEnergy
  have hbridgeQ : unitIntervalLogEnergy pfun =
      (1 / 4 : ℝ) * centeredRawLogEnergy q := by
    have hpEnergy' : Integrable (unitIntervalRawLogEnergyIntegrand
        (fun t : unitInterval ↦ centeredPullback q (t : ℝ))) := by
      apply hpEnergy.congr
      filter_upwards [] with z
      unfold unitIntervalRawLogEnergyIntegrand
      dsimp only [pfun]
      change ((p.eval (z.1 : ℝ) - p.eval (z.2 : ℝ)) ^ 2 /
          |(z.1 : ℝ) - (z.2 : ℝ)|) =
        ((centeredPullback q (z.1 : ℝ) -
            centeredPullback q (z.2 : ℝ)) ^ 2 /
          |(z.1 : ℝ) - (z.2 : ℝ)|)
      rw [hmode z.1, hmode z.2]
    have hbridge := unitIntervalLogEnergy_centeredPullback q hpEnergy'
    rw [show pfun = fun t : unitInterval ↦
        centeredPullback q (t : ℝ) by
      funext t
      exact (hmode t).symm]
    exact hbridge
  have hbridgeR : unitIntervalLogEnergy f =
      (1 / 4 : ℝ) * centeredRawLogEnergy r := by
    simpa only [f] using unitIntervalLogEnergy_centeredPullback r hfEnergy
  rw [hbridgeG, hbridgeQ, hbridgeR] at hunitExpand
  linarith

/-- Exact raw-log splitting of the intrinsic odd `P₁/P₃` low block from
an arbitrary locally Lipschitz residual with zero low coefficients. -/
theorem centeredRawLogEnergy_one_three_add_tail
    (r : ℝ → ℝ) (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (c d : ℝ) :
    centeredRawLogEnergy (fun x ↦
        c * centeredP1 x + d * centeredP3 x + r x) =
      centeredRawLogEnergy (factorTwoOddStructuralLowProfile c d) +
        centeredRawLogEnergy r := by
  let p : ℝ[X] :=
    -(c • shiftedLegendreReal 1 + d • shiftedLegendreReal 3)
  let q : ℝ → ℝ := factorTwoOddStructuralLowProfile c d
  have hmode : ∀ t : unitInterval,
      centeredPullback q (t : ℝ) = p.eval (t : ℝ) := by
    intro t
    have h1 := centeredPullback_centeredP1_eq_neg_shiftedLegendre (t : ℝ)
    have h3 := centeredPullback_centeredP3_eq_neg_shiftedLegendre (t : ℝ)
    dsimp only [q, p, factorTwoOddStructuralLowProfile]
    simp only [Polynomial.eval_neg, Polynomial.eval_add,
      Polynomial.eval_smul]
    unfold centeredPullback at h1 h3 ⊢
    unfold factorTwoOddStructuralLowProfile
    rw [h1, h3]
    simp only [smul_eq_mul]
    ring
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
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback r hlocal
  have hIntOne : Integrable (fun t : unitInterval ↦
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 1).eval (t : ℝ)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hLip.continuous.mul
        ((shiftedLegendreReal 1).continuous.comp continuous_subtype_val)
    · exact HasCompactSupport.of_compactSpace _
  have hIntThree : Integrable (fun t : unitInterval ↦
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 3).eval (t : ℝ)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hLip.continuous.mul
        ((shiftedLegendreReal 3).continuous.comp continuous_subtype_val)
    · exact HasCompactSupport.of_compactSpace _
  have hpair : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLogKernel p).eval (t : ℝ)) = 0 := by
    rw [hpLog]
    simp only [Polynomial.eval_neg, Polynomial.eval_add,
      Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_C,
      smul_eq_mul]
    rw [show (fun t : unitInterval ↦
        centeredPullback r (t : ℝ) *
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
      ring,
      integral_add (hIntOne.const_mul (-2 * c))
        (hIntThree.const_mul (-(11 / 3 : ℝ) * d)),
      integral_const_mul, integral_const_mul, hpairOne, hpairThree]
    ring
  have hsplit := centeredRawLogEnergy_add_polynomial_tail
    p q r hlocal hmode hpair
  simpa only [q, factorTwoOddStructuralLowProfile, add_assoc] using hsplit

/-- The centered raw energy of a transported shifted-Legendre mode is its
exact harmonic eigenvalue times its exact `L²` mass. -/
private theorem centeredRawLogEnergy_mode_eq_harmonic_mass
    (n : ℕ) (q : ℝ → ℝ)
    (hmode : ∀ t : unitInterval, centeredPullback q (t : ℝ) =
      -(shiftedLegendreReal n).eval (t : ℝ)) :
    centeredRawLogEnergy q =
      8 * (harmonic n : ℝ) *
        ∫ t : unitInterval,
          (shiftedLegendreReal n).eval (t : ℝ) *
            (shiftedLegendreReal n).eval (t : ℝ) := by
  let p : ℝ[X] := shiftedLegendreReal n
  let pfun : unitInterval → ℝ := fun t ↦ p.eval (t : ℝ)
  let qfun : unitInterval → ℝ := fun t ↦ centeredPullback q (t : ℝ)
  have hpEnergy : Integrable (unitIntervalRawLogEnergyIntegrand pfun) := by
    simpa only [pfun] using
      integrable_unitIntervalRawLogEnergyIntegrand_polynomial p
  have hqEnergy : Integrable (unitIntervalRawLogEnergyIntegrand qfun) := by
    apply hpEnergy.congr
    filter_upwards [] with z
    unfold unitIntervalRawLogEnergyIntegrand
    dsimp only [pfun, qfun]
    rw [hmode z.1, hmode z.2]
    dsimp only [p]
    ring
  have hqP : unitIntervalLogEnergy qfun = unitIntervalLogEnergy pfun := by
    unfold unitIntervalLogEnergy
    apply congrArg (fun z : ℝ ↦ (1 / 2 : ℝ) * z)
    apply integral_congr_ae
    filter_upwards [] with z
    unfold unitIntervalRawLogEnergyIntegrand
    dsimp only [pfun, qfun]
    rw [hmode z.1, hmode z.2]
    dsimp only [p]
    ring
  have hpIdentity : unitIntervalLogEnergy pfun =
      ∫ t : unitInterval,
        p.eval (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ) := by
    unfold unitIntervalLogEnergy
    rw [show (∫ z, unitIntervalRawLogEnergyIntegrand pfun z) =
        2 * ∫ t : unitInterval,
          p.eval (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ) by
      simpa only [pfun] using
        integral_unitIntervalRawLogEnergyIntegrand_polynomial p]
    ring
  have hpEigen : (∫ t : unitInterval,
      p.eval (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ)) =
      (2 * (harmonic n : ℝ)) *
        ∫ t : unitInterval, p.eval (t : ℝ) * p.eval (t : ℝ) := by
    rw [show shiftedLogKernel p =
        Polynomial.C (2 * (harmonic n : ℝ)) * p by
      dsimp only [p]
      exact shiftedLogKernel_shiftedLegendreReal n]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  have hbridge := unitIntervalLogEnergy_centeredPullback q hqEnergy
  change unitIntervalLogEnergy qfun =
    (1 / 4 : ℝ) * centeredRawLogEnergy q at hbridge
  rw [hqP, hpIdentity, hpEigen] at hbridge
  dsimp only [p] at hbridge ⊢
  linarith

/-- Exact centered raw-log energy of the intrinsic odd degree-one mode. -/
theorem centeredRawLogEnergy_centeredP1 :
    centeredRawLogEnergy centeredP1 = (8 / 3 : ℝ) := by
  rw [centeredRawLogEnergy_mode_eq_harmonic_mass 1 centeredP1
    (fun t ↦ centeredPullback_centeredP1_eq_neg_shiftedLegendre (t : ℝ))]
  rw [integral_polynomial_mul_eq_inner]
  change 8 * (harmonic 1 : ℝ) *
      inner ℝ (shiftedLegendreL2 1) (shiftedLegendreL2 1) = (8 / 3 : ℝ)
  rw [real_inner_self_eq_norm_sq, norm_sq_shiftedLegendreL2_one]
  norm_num [harmonic]

/-- Exact centered raw-log energy of the intrinsic odd degree-three mode. -/
theorem centeredRawLogEnergy_centeredP3 :
    centeredRawLogEnergy centeredP3 = (44 / 21 : ℝ) := by
  rw [centeredRawLogEnergy_mode_eq_harmonic_mass 3 centeredP3
    (fun t ↦ centeredPullback_centeredP3_eq_neg_shiftedLegendre (t : ℝ))]
  rw [integral_polynomial_mul_eq_inner]
  change 8 * (harmonic 3 : ℝ) *
      inner ℝ (shiftedLegendreL2 3) (shiftedLegendreL2 3) = (44 / 21 : ℝ)
  rw [real_inner_self_eq_norm_sq, norm_sq_shiftedLegendreL2_three]
  norm_num [harmonic]

/-- Homogeneity of the centered raw logarithmic difference energy. -/
theorem centeredRawLogEnergy_const_mul
    (a : ℝ) (u : ℝ → ℝ) :
    centeredRawLogEnergy (fun x ↦ a * u x) =
      a ^ 2 * centeredRawLogEnergy u := by
  unfold centeredRawLogEnergy
  rw [show (fun x : ℝ ↦ ∫ y : ℝ in -1..1,
      (a * u x - a * u y) ^ 2 / |x - y|) =
      fun x ↦ a ^ 2 * ∫ y : ℝ in -1..1,
        (u x - u y) ^ 2 / |x - y| by
    funext x
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _hy
    ring,
    intervalIntegral.integral_const_mul]

/-- The two intrinsic odd modes are exactly diagonal for the centered raw
logarithmic form. -/
theorem centeredRawLogEnergy_factorTwoOddStructuralLowProfile
    (c d : ℝ) :
    centeredRawLogEnergy (factorTwoOddStructuralLowProfile c d) =
      (8 / 3 : ℝ) * c ^ 2 + (44 / 21 : ℝ) * d ^ 2 := by
  let p : ℝ[X] := -(c • shiftedLegendreReal 1)
  let q : ℝ → ℝ := fun x ↦ c * centeredP1 x
  let r : ℝ → ℝ := fun x ↦ d * centeredP3 x
  have hrLocal : LocallyLipschitzOn (Icc (-1) 1) r := by
    have hd : ContDiffOn ℝ 1 r (Icc (-1) 1) := by
      dsimp only [r]
      unfold centeredP3
      fun_prop
    exact hd.locallyLipschitzOn (convex_Icc (-1) 1)
  have hmode : ∀ t : unitInterval,
      centeredPullback q (t : ℝ) = p.eval (t : ℝ) := by
    intro t
    have h1 := centeredPullback_centeredP1_eq_neg_shiftedLegendre (t : ℝ)
    dsimp only [q, p]
    simp only [Polynomial.eval_neg, Polynomial.eval_smul, smul_eq_mul]
    unfold centeredPullback at h1 ⊢
    change c * centeredP1 (2 * (t : ℝ) - 1) =
      -(c * (shiftedLegendreReal 1).eval (t : ℝ))
    rw [h1]
    ring
  have hcenter : (∫ x : ℝ in -1..1, r x * centeredP1 x) = 0 := by
    rw [show (fun x : ℝ ↦ r x * centeredP1 x) =
        fun x ↦ d * (centeredP1 x * centeredP3 x) by
      funext x
      dsimp only [r]
      ring,
      intervalIntegral.integral_const_mul, integral_centeredP1_mul_p3]
    ring
  have hunitOne : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 1).eval (t : ℝ)) = 0 := by
    rw [integral_centeredPullback_mul_shiftedLegendre_eq_neg_half
      1 centeredP1 r centeredPullback_centeredP1_eq_neg_shiftedLegendre,
      hcenter]
    ring
  have hpLog : shiftedLogKernel p =
      -(c • (Polynomial.C 2 * shiftedLegendreReal 1)) := by
    dsimp only [p]
    rw [map_neg, map_smul, shiftedLogKernel_shiftedLegendreReal]
    norm_num [harmonic]
  have hpair : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLogKernel p).eval (t : ℝ)) = 0 := by
    rw [hpLog]
    simp only [Polynomial.eval_neg, Polynomial.eval_smul,
      Polynomial.eval_mul, Polynomial.eval_C, smul_eq_mul]
    rw [show (fun t : unitInterval ↦
        centeredPullback r (t : ℝ) *
          -(c * (2 * (shiftedLegendreReal 1).eval (t : ℝ)))) =
        fun t : unitInterval ↦ (-2 * c) *
          (centeredPullback r (t : ℝ) *
            (shiftedLegendreReal 1).eval (t : ℝ)) by
      funext t
      ring,
      integral_const_mul, hunitOne]
    ring
  have hsplit := centeredRawLogEnergy_add_polynomial_tail
    p q r hrLocal hmode hpair
  have hq : centeredRawLogEnergy q =
      c ^ 2 * centeredRawLogEnergy centeredP1 := by
    simpa only [q] using centeredRawLogEnergy_const_mul c centeredP1
  have hr : centeredRawLogEnergy r =
      d ^ 2 * centeredRawLogEnergy centeredP3 := by
    simpa only [r] using centeredRawLogEnergy_const_mul d centeredP3
  calc
    centeredRawLogEnergy (factorTwoOddStructuralLowProfile c d) =
        centeredRawLogEnergy (fun x ↦ q x + r x) := by
      congr 1
    _ = centeredRawLogEnergy q + centeredRawLogEnergy r := hsplit
    _ = (8 / 3 : ℝ) * c ^ 2 + (44 / 21 : ℝ) * d ^ 2 := by
      rw [hq, hr, centeredRawLogEnergy_centeredP1,
        centeredRawLogEnergy_centeredP3]
      ring

/-- Fully explicit structural raw-energy decomposition of the intrinsic
`P₁/P₃` block and an infinite-dimensional orthogonal residual. -/
theorem centeredRawLogEnergy_one_three_add_tail_explicit
    (r : ℝ → ℝ) (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (c d : ℝ) :
    centeredRawLogEnergy (fun x ↦
        c * centeredP1 x + d * centeredP3 x + r x) =
      (8 / 3 : ℝ) * c ^ 2 + (44 / 21 : ℝ) * d ^ 2 +
        centeredRawLogEnergy r := by
  rw [centeredRawLogEnergy_one_three_add_tail r hlocal hone hthree c d,
    centeredRawLogEnergy_factorTwoOddStructuralLowProfile]

end

end ArithmeticHodge.Analysis.YoshidaEndpointOddOneThreeRawPolarization
