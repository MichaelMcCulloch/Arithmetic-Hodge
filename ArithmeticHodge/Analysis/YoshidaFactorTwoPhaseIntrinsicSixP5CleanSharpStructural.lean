import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5CleanSharpStructural

noncomputable section

open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointScalarStructuralUpper
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicRemainderBound
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaRegularKernelSharpMeanZeroSchur

/-!
# A sharp structural clean reserve for the intrinsic `P5` mode

The four-term octic potential envelope is sufficient for scalar positivity,
but leaves the final odd endpoint Schur determinant unnecessarily thin.  The
eight positive Taylor terms below retain more of the same logarithmic
potential.  This is still a pointwise analytic inequality followed by one
exact polynomial integral; no subdivision or finite certificate is used.
-/

/-- The first eight positive terms of `-log (1 - x^2) / 2`. -/
def yoshidaEndpointHexadecic (x : ℝ) : ℝ :=
  x ^ 2 / 2 + x ^ 4 / 4 + x ^ 6 / 6 + x ^ 8 / 8 +
    x ^ 10 / 10 + x ^ 12 / 12 + x ^ 14 / 14 + x ^ 16 / 16

/-- Structural degree-sixteen lower envelope for the endpoint potential. -/
theorem hexadecic_le_endpointPotential {x : ℝ} (hx : |x| < 1) :
    yoshidaEndpointHexadecic x ≤ yoshidaEndpointPotential x := by
  let R : ℝ → ℝ := fun u ↦
    -Real.log (1 - u) - u - u ^ 2 / 2 - u ^ 3 / 3 - u ^ 4 / 4 -
      u ^ 5 / 5 - u ^ 6 / 6 - u ^ 7 / 7 - u ^ 8 / 8
  have hu0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hu1 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).2 hx
  have hRderiv (u : ℝ) (hu : u < 1) :
      HasDerivAt R (u ^ 8 / (1 - u)) u := by
    have hinner : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) u := by
      convert (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u) using 1
      ring
    have hne : 1 - u ≠ 0 := by linarith
    have hlog := (Real.hasDerivAt_log hne).comp u hinner
    have h2 := ((hasDerivAt_id u).pow 2).div_const 2
    have h3 := ((hasDerivAt_id u).pow 3).div_const 3
    have h4 := ((hasDerivAt_id u).pow 4).div_const 4
    have h5 := ((hasDerivAt_id u).pow 5).div_const 5
    have h6 := ((hasDerivAt_id u).pow 6).div_const 6
    have h7 := ((hasDerivAt_id u).pow 7).div_const 7
    have h8 := ((hasDerivAt_id u).pow 8).div_const 8
    dsimp only [R]
    convert ((((((((hlog.neg.sub (hasDerivAt_id u)).sub h2).sub h3).sub h4).sub
      h5).sub h6).sub h7).sub h8) using 1
    simp only [id_eq, Nat.cast_ofNat]
    field_simp [hne]
    ring
  have hRcont : ContinuousOn R (Icc 0 (x ^ 2)) := by
    intro u hu
    exact (hRderiv u (lt_of_le_of_lt hu.2 hu1)).continuousAt.continuousWithinAt
  have hRmono : MonotoneOn R (Icc 0 (x ^ 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (x ^ 2)) hRcont ?_ ?_
    · intro u hu
      exact (hRderiv u (lt_of_le_of_lt (interior_subset hu).2 hu1))
        |>.differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hRderiv u (lt_of_le_of_lt (interior_subset hu).2 hu1)).deriv]
      exact div_nonneg (by positivity) (by linarith [(interior_subset hu).2])
  have hRnonneg : 0 ≤ R (x ^ 2) := by
    have hmono := hRmono (by exact ⟨le_rfl, hu0⟩)
      (by exact ⟨hu0, le_rfl⟩) hu0
    simpa [R] using hmono
  dsimp only [R] at hRnonneg
  dsimp only [yoshidaEndpointHexadecic, yoshidaEndpointPotential]
  ring_nf at hRnonneg ⊢
  linarith

/-- Exact degree-sixteen potential mass on the centered `P5` mode. -/
theorem integral_hexadecic_mul_factorTwoCenteredP5_sq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointHexadecic x * factorTwoCenteredP5 x ^ 2) =
        1247216389 / 13385572200 := by
  unfold yoshidaEndpointHexadecic factorTwoCenteredP5
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num

/-- The degree-sixteen envelope gives a strictly sharper potential reserve
on `P5` than the previously retained octic truncation. -/
theorem factorTwoCenteredP5_hexadecicPotential_le :
    (1247216389 / 13385572200 : ℝ) ≤
      factorTwoIntrinsicPotentialEnergy factorTwoCenteredP5 := by
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointHexadecic x * factorTwoCenteredP5 x ^ 2)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold yoshidaEndpointHexadecic factorTwoCenteredP5
    fun_prop
  have hpotential := intervalIntegrable_endpointPotential_mul_sq
    factorTwoCenteredP5 continuous_factorTwoCenteredP5
  rw [← integral_hexadecic_mul_factorTwoCenteredP5_sq]
  unfold factorTwoIntrinsicPotentialEnergy
  apply intervalIntegral.integral_mono_on_of_le_Ioo
    (by norm_num : (-1 : ℝ) ≤ 1) hpoly hpotential
  intro x hx
  exact mul_le_mul_of_nonneg_right
    (hexadecic_le_endpointPotential (by simpa only [abs_lt] using hx))
    (sq_nonneg _)

private theorem factorTwoCenteredP5_energy :
    factorTwoIntrinsicEnergy factorTwoCenteredP5 = 2 / 11 := by
  unfold factorTwoIntrinsicEnergy
  exact integral_factorTwoCenteredP5_sq

private theorem hyperbolic_loss_lt_one_sixty_four :
    1 / Real.sqrt 2 - Real.log 2 < (1 / 64 : ℝ) := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtLower : (707 / 500 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hinv : 1 / Real.sqrt 2 < (500 / 707 : ℝ) := by
    rw [div_lt_iff₀ hsqrtPos]
    nlinarith
  have hlog := six_hundred_ninety_three_div_thousand_lt_log_two
  linarith

/-- The clean `P5` diagonal retains `7/5` of its intrinsic energy.  The
improvement is entirely the extra positive potential tail above. -/
theorem seven_fifths_energy_le_clean_P5 :
    (7 / 5 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP5 ≤
      yoshidaEndpointOddCleanQuadratic factorTwoCenteredP5 := by
  have hraw := factorTwoCenteredP5_raw_reserve
  have hpotential := factorTwoCenteredP5_hexadecicPotential_le
  have hscalar := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hregular :=
    endpoint_mul_regularQuadratic_re_le_log_two_div_sixty_four_energy
      factorTwoCenteredP5 continuous_factorTwoCenteredP5
      (centered_interval_integral_eq_zero_of_odd
        factorTwoCenteredP5 odd_factorTwoCenteredP5)
  have hhyper := yoshidaEndpointHyperbolicQuadratic_lower
    (fun x ↦ (factorTwoCenteredP5 x : ℂ))
    (Complex.continuous_ofReal.comp continuous_factorTwoCenteredP5)
  have hlog : Real.log 2 / 64 < (7 / 640 : ℝ) := by
    have := Real.log_two_lt_d9
    linarith
  have hdelta := hyperbolic_loss_lt_one_sixty_four
  rw [factorTwoCenteredP5_energy] at hraw hregular ⊢
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hhyper
  rw [integral_factorTwoCenteredP5_sq] at hhyper
  unfold factorTwoIntrinsicPotentialEnergy at hpotential
  unfold yoshidaEndpointOddCleanQuadratic
  rw [integral_factorTwoCenteredP5_sq]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5CleanSharpStructural
