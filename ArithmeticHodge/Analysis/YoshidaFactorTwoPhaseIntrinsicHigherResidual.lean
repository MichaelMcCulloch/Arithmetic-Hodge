import ArithmeticHodge.Analysis.ShiftedLegendreCenteredParity
import ArithmeticHodge.Analysis.ShiftedLegendreL2HigherGap
import ArithmeticHodge.Analysis.YoshidaEndpointScalarStructuralUpper
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicProjectedRemainder

set_option autoImplicit false

open Complex MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual

open ShiftedLegendreL2Basis
open ShiftedLegendreL2HigherGap
open ShiftedLegendreCenteredParity
open ShiftedLegendreOrthogonality
open YoshidaEndpointHyperbolicBound
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open CenteredOddOneThreeEnergy
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPullbackLipschitz
open YoshidaEndpointScalarStructuralUpper
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicResidual

noncomputable section

/-!
# A structural higher intrinsic residual

The residual-projected smooth estimate becomes coercive once the exact
shifted-Legendre harmonic gap reaches the ninth even and tenth odd levels.
This is an infinite spectral statement: all degrees above the stated level
are controlled at once by the harmonic eigenvalue monotonicity.  No retained
mode is inspected and no finite certificate is used.
-/

/-- Vanishing of every unnormalised shifted-Legendre moment below `k`.
Unlike an `L²` basis coordinate, this predicate does not depend on a proof of
square-integrability. -/
def centeredLegendreMomentsVanishBelow
    (w : ℝ → ℝ) (k : ℕ) : Prop :=
  ∀ n < k,
    (∫ t : unitInterval,
      centeredPullback w (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) = 0

/-- The exact centered harmonic gap obtained after annihilating all degrees
below `k`. -/
theorem harmonic_mul_intrinsicEnergy_le_raw_div_four
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) w)
    (k : ℕ) (hlow : centeredLegendreMomentsVanishBelow w k) :
    (harmonic k : ℝ) * factorTwoIntrinsicEnergy w ≤
      centeredRawLogEnergy w / 4 := by
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback w hlocal
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hf : MemLp f 2 :=
    hfcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hrepr : ∀ n < k,
      shiftedLegendreHilbertBasis.repr (hf.toLp f) n = 0 := by
    intro n hn
    rw [shiftedLegendreHilbertBasis_repr_eq f hf n]
    have hm : (∫ t : unitInterval,
        f t * (shiftedLegendreReal n).eval (t : ℝ)) = 0 := by
      simpa only [f] using hlow n hn
    rw [hm, mul_zero]
  have hgap := harmonic_mul_integral_sq_le_unitIntervalLogEnergy
    f hf henergy k hrepr
  rw [integral_unitInterval_centeredPullback_sq w,
    unitIntervalLogEnergy_centeredPullback w henergy] at hgap
  unfold factorTwoIntrinsicEnergy
  nlinarith

/-! ## One disk estimate for the projected smooth coefficient -/

private theorem dyadic_weight_lt_491_div_1000 :
    Real.log 2 / Real.sqrt 2 < (491 / 1000 : ℝ) := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtLower : (707 / 500 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hlogUpper := Real.log_two_lt_d9
  rw [div_lt_iff₀ hsqrtPos]
  nlinarith

private theorem four_ninths_lt_dyadic_weight :
    (4 / 9 : ℝ) < Real.log 2 / Real.sqrt 2 := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtUpper : Real.sqrt 2 < (3 / 2 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 2]
  have hlogLower := six_hundred_ninety_three_div_thousand_lt_log_two
  rw [lt_div_iff₀ hsqrtPos]
  nlinarith

private theorem prime_three_weight_lt_16_div_25 :
    Real.log 3 / Real.sqrt 3 < (16 / 25 : ℝ) := by
  have hsqrtPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrtLower : (173 / 100 : ℝ) < Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3]
  have hpow : (3 : ℝ) ^ 17 < (2 : ℝ) ^ 27 := by norm_num
  have hlog := Real.strictMonoOn_log (by norm_num) (by norm_num) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  have hlogUpper := Real.log_two_lt_d9
  rw [div_lt_iff₀ hsqrtPos]
  norm_num at hlog
  nlinarith

/-- The two phase coordinates are treated by one Euclidean estimate.  The
negative `a` half-disk is easier because the signed dyadic term then cancels
the self-regular width. -/
theorem projected_phase_variable_le_nineteen_twenty_fourths
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoIntrinsicSelfRegularHalfWidth * |a| +
        (203 / 640 : ℝ) * |b| +
        (Real.log 2 / Real.sqrt 2) * a ≤
      19 / 24 := by
  let d := factorTwoIntrinsicSelfRegularHalfWidth
  let alpha := Real.log 2 / Real.sqrt 2
  have hlogLower := six_hundred_ninety_three_div_thousand_lt_log_two
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
      (by norm_num)
  have hd0 : 0 ≤ d := by
    dsimp only [d]
    unfold factorTwoIntrinsicSelfRegularHalfWidth yoshidaEndpointA
    linarith
  have hdUpper : d < (43 / 200 : ℝ) := by
    dsimp only [d]
    unfold factorTwoIntrinsicSelfRegularHalfWidth yoshidaEndpointA
    linarith
  have halphaUpper : alpha < (491 / 1000 : ℝ) := by
    simpa only [alpha] using dyadic_weight_lt_491_div_1000
  have halphaLower : (4 / 9 : ℝ) < alpha := by
    simpa only [alpha] using four_ninths_lt_dyadic_weight
  have hdAlpha : d ≤ alpha := by linarith
  have hsum : d + alpha ≤ (17 / 24 : ℝ) := by linarith
  have hbSq : |b| ^ 2 = b ^ 2 := sq_abs b
  have hbDisk : a ^ 2 + |b| ^ 2 ≤ 1 := by simpa only [hbSq] using hab
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    have hfirst : (d + alpha) * a ≤ (17 / 24 : ℝ) * a :=
      mul_le_mul_of_nonneg_right hsum ha
    have hsecond : (203 / 640 : ℝ) * |b| ≤
        (1 / 3 : ℝ) * |b| := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg b)
    have hlinear :
        (d + alpha) * a + (203 / 640 : ℝ) * |b| ≤
          (17 / 24 : ℝ) * a + (1 / 3 : ℝ) * |b| :=
      add_le_add hfirst hsecond
    have hnonneg : 0 ≤
        (17 / 24 : ℝ) * a + (1 / 3 : ℝ) * |b| := by positivity
    have hcauchy := sq_nonneg ((1 / 3 : ℝ) * a -
      (17 / 24 : ℝ) * |b|)
    have htarget :
        (17 / 24 : ℝ) * a + (1 / 3 : ℝ) * |b| ≤
          19 / 24 := by
      nlinarith
    dsimp only [d, alpha] at hlinear ⊢
    nlinarith
  · have haNeg : a < 0 := lt_of_not_ge ha
    rw [abs_of_neg haNeg]
    have hcancel : (alpha - d) * a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hdAlpha) haNeg.le
    have hbOne : |b| ≤ 1 := by
      nlinarith [abs_nonneg b]
    change d * -a + (203 / 640 : ℝ) * |b| + alpha * a ≤ 19 / 24
    rw [show d * -a + (203 / 640 : ℝ) * |b| + alpha * a =
        (alpha - d) * a + (203 / 640 : ℝ) * |b| by ring]
    nlinarith

/-- A rational upper bound for the entire even projected remainder norm. -/
theorem projectedEvenRemainderLoss_lt_structural_bound
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoIntrinsicProjectedEvenRemainderLoss a b <
      (19 / 24 + 8 / 25 + 338887 / 250000 + 7 / 640 : ℝ) := by
  have hphase := projected_phase_variable_le_nineteen_twenty_fourths a b hab
  have hbeta := prime_three_weight_lt_16_div_25
  have hscalar := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hlog : Real.log 2 / 64 < (7 / 640 : ℝ) := by
    have := Real.log_two_lt_d9
    linarith
  unfold factorTwoIntrinsicProjectedEvenRemainderLoss
  linarith

/-- The ninth harmonic gap pays the even projected remainder uniformly on
the closed phase disk. -/
theorem projectedEvenRemainderLoss_le_harmonic_nine
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoIntrinsicProjectedEvenRemainderLoss a b ≤
      (harmonic 9 : ℝ) - Real.log 2 / 2 := by
  have hloss := projectedEvenRemainderLoss_lt_structural_bound a b hab
  have hlog : Real.log 2 < (7 / 10 : ℝ) :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
      (by norm_num)
  norm_num [harmonic, Finset.sum_range_succ] at hloss ⊢
  linarith

/-- The odd hyperbolic loss requires one further harmonic step. -/
theorem projectedOddRemainderLoss_le_harmonic_ten
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoIntrinsicProjectedOddRemainderLoss a b ≤
      (harmonic 10 : ℝ) - Real.log 2 / 2 := by
  have heven := projectedEvenRemainderLoss_lt_structural_bound a b hab
  have hsqrt := inv_sqrt_two_lt_one_hundred_seventy_seven_div_two_hundred_fifty
  have hsqrt' : (Real.sqrt 2)⁻¹ < (177 / 250 : ℝ) := by
    simpa only [one_div] using hsqrt
  have hlogLower := six_hundred_ninety_three_div_thousand_lt_log_two
  unfold factorTwoIntrinsicProjectedOddRemainderLoss
  norm_num [harmonic, Finset.sum_range_succ] at heven ⊢
  linarith

/-! ## Infinite higher-residual phase positivity -/

/-- Complete phase positivity on the infinite subspace above the ninth even
and tenth odd shifted-Legendre gaps.  The named mean hypothesis exposes the
cancellation used by the projected regular estimate; it is automatic for the
corresponding canonical tail.
-/
theorem factorTwoEndpointChannelPhase_nonneg_of_higher_residual
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (heLow : centeredLegendreMomentsVanishBelow e 9)
    (hoLow : centeredLegendreMomentsVanishBelow o 10)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  have heRaw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    e hec helocal 9 heLow
  have hoRaw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    o hoc holocal 10 hoLow
  have hprotected := raw_add_half_potential_sub_half_logMass_le_protected
    e o hec hoc helocal holocal a b hab
  have heLoss := projectedEvenRemainderLoss_le_harmonic_nine a b hab
  have hoLoss := projectedOddRemainderLoss_le_harmonic_ten a b hab
  have hremainder := neg_factorTwoIntrinsicSignedRemainder_le_projected_energy
    e o hec hoc he ho he0 a b hab
  have heEnergy := factorTwoIntrinsicEnergy_nonneg e
  have hoEnergy := factorTwoIntrinsicEnergy_nonneg o
  have heLossScaled := mul_le_mul_of_nonneg_right heLoss heEnergy
  have hoLossScaled := mul_le_mul_of_nonneg_right hoLoss hoEnergy
  have hpotential : 0 ≤ (1 / 2 : ℝ) *
      (factorTwoIntrinsicPotentialEnergy e +
        factorTwoIntrinsicPotentialEnergy o) := by
    exact mul_nonneg (by norm_num)
      (add_nonneg (factorTwoIntrinsicPotentialEnergy_nonneg e)
        (factorTwoIntrinsicPotentialEnergy_nonneg o))
  rw [factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
    e o hec hoc a b]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual
