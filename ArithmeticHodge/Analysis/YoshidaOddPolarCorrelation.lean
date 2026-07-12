import ArithmeticHodge.Analysis.YoshidaOddCorrelationFold

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ComplexConjugate Convolution

namespace ArithmeticHodge.Analysis.YoshidaOddPolarCorrelation

noncomputable section

open YoshidaCauchyPairing
open YoshidaClippedMomentBridge
open YoshidaOddGramPrefix
open YoshidaOddModeRegularity
open YoshidaOddCorrelationFold
open YoshidaOddSpectralBridge

/-!
# Polar terms as odd-mode correlations

The two centered Laplace polar samples are products of exponentially weighted
mode integrals.  Convolution converts those products into whole-line weighted
cross-correlations; evenness and compact support then fold the result to the
full positive correlation interval `[0, yoshidaLength]`.
-/

private def weightedRight (s : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ((Real.exp (s * x) : ℝ) : ℂ) * oddModeFunction n x

private def weightedLeft (s : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ((Real.exp (s * x) : ℝ) : ℂ) * starReflection (oddModeFunction n) x

private theorem weightedRight_integrable (s : ℝ) (n : ℕ) :
    Integrable (weightedRight s n) := by
  have hcont : Continuous (weightedRight s n) := by
    unfold weightedRight oddModeFunction
    have hexp : Continuous (fun x : ℝ ↦
        ((Real.exp (s * x) : ℝ) : ℂ)) := by fun_prop
    exact hexp.mul
      (continuous_yoshidaClippedOddMode yoshidaHalfLength_pos n)
  have hcompact : HasCompactSupport (weightedRight s n) := by
    unfold weightedRight oddModeFunction
    exact (hasCompactSupport_yoshidaClippedOddMode n).mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

private theorem starReflection_oddMode_hasCompactSupport (n : ℕ) :
    HasCompactSupport (starReflection (oddModeFunction n)) := by
  have hneg : HasCompactSupport (fun x : ℝ ↦ oddModeFunction n (-x)) := by
    simpa only [Function.comp_apply] using
      (hasCompactSupport_yoshidaClippedOddMode (a := yoshidaHalfLength) n).comp_homeomorph
        (Homeomorph.neg ℝ)
  simpa only [starReflection, RCLike.star_def] using
    hneg.comp_left (by simp : conj (0 : ℂ) = 0)

private theorem weightedLeft_integrable (s : ℝ) (n : ℕ) :
    Integrable (weightedLeft s n) := by
  have hcont : Continuous (weightedLeft s n) := by
    unfold weightedLeft
    have hexp : Continuous (fun x : ℝ ↦
        ((Real.exp (s * x) : ℝ) : ℂ)) := by fun_prop
    have hstar : Continuous (starReflection (oddModeFunction n)) := by
      unfold starReflection oddModeFunction
      exact ((continuous_yoshidaClippedOddMode
        yoshidaHalfLength_pos n).comp continuous_neg).star
    exact hexp.mul hstar
  have hcompact : HasCompactSupport (weightedLeft s n) := by
    unfold weightedLeft
    exact (starReflection_oddMode_hasCompactSupport n).mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

private theorem weighted_convolution_eq
    (s : ℝ) (n m : ℕ) (u : ℝ) :
    (weightedLeft s n ⋆[ContinuousLinearMap.mul ℂ ℂ] weightedRight s m) u =
      ((Real.exp (s * u) : ℝ) : ℂ) *
        crossCorrelation (oddModeFunction n) (oddModeFunction m) u := by
  rw [MeasureTheory.convolution_def]
  calc
    (∫ t : ℝ,
        ContinuousLinearMap.mul ℂ ℂ (weightedLeft s n t)
          (weightedRight s m (u - t))) =
        ∫ t : ℝ, ((Real.exp (s * u) : ℝ) : ℂ) *
          (starReflection (oddModeFunction n) t * oddModeFunction m (u - t)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      have hexp : Real.exp (s * t) * Real.exp (s * (u - t)) =
          Real.exp (s * u) := by
        rw [← Real.exp_add]
        congr 1
        ring
      dsimp only [weightedLeft, weightedRight]
      calc
        (((Real.exp (s * t) : ℝ) : ℂ) * starReflection (oddModeFunction n) t) *
              (((Real.exp (s * (u - t)) : ℝ) : ℂ) * oddModeFunction m (u - t)) =
            ((((Real.exp (s * t) * Real.exp (s * (u - t)) : ℝ)) : ℂ) *
              (starReflection (oddModeFunction n) t * oddModeFunction m (u - t))) := by
          push_cast
          ring
        _ = (((Real.exp (s * u) : ℝ) : ℂ) *
              (starReflection (oddModeFunction n) t * oddModeFunction m (u - t))) := by
          rw [hexp]
    _ = ((Real.exp (s * u) : ℝ) : ℂ) *
        ∫ t : ℝ,
          starReflection (oddModeFunction n) t * oddModeFunction m (u - t) := by
      exact MeasureTheory.integral_const_mul
        (((Real.exp (s * u) : ℝ) : ℂ))
        (fun t : ℝ ↦ starReflection (oddModeFunction n) t *
          oddModeFunction m (u - t))
    _ = _ := by
      rw [crossCorrelation, MeasureTheory.convolution_def]
      congr 1

private theorem integral_weightedLeft
    (s : ℝ) (n : ℕ) :
    (∫ x : ℝ, weightedLeft s n x) =
      star (∫ x : ℝ, weightedRight (-s) n x) := by
  calc
    (∫ x : ℝ, weightedLeft s n x) =
        ∫ x : ℝ, weightedLeft s n (-x) := by
      exact (MeasureTheory.integral_neg_eq_self (weightedLeft s n) volume).symm
    _ = ∫ x : ℝ, star (weightedRight (-s) n x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [weightedLeft, weightedRight, starReflection, neg_mul,
        neg_neg, RCLike.star_def, map_mul, conj_ofReal]
      congr 2
      congr 1
      ring
    _ = star (∫ x : ℝ, weightedRight (-s) n x) := by
      simpa only [RCLike.star_def] using
        (integral_conj (f := weightedRight (-s) n))

private theorem integral_exp_mul_crossCorrelation
    (s : ℝ) (n m : ℕ) :
    (∫ u : ℝ, ((Real.exp (s * u) : ℝ) : ℂ) *
      crossCorrelation (oddModeFunction n) (oddModeFunction m) u) =
      star (∫ x : ℝ, weightedRight (-s) n x) *
        ∫ x : ℝ, weightedRight s m x := by
  have hconv := MeasureTheory.integral_convolution
    (ContinuousLinearMap.mul ℂ ℂ)
    (weightedLeft_integrable s n) (weightedRight_integrable s m)
  calc
    (∫ u : ℝ, ((Real.exp (s * u) : ℝ) : ℂ) *
        crossCorrelation (oddModeFunction n) (oddModeFunction m) u) =
        ∫ u : ℝ,
          (weightedLeft s n ⋆[ContinuousLinearMap.mul ℂ ℂ] weightedRight s m) u := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact (weighted_convolution_eq s n m u).symm
    _ = (∫ x : ℝ, weightedLeft s n x) *
          ∫ x : ℝ, weightedRight s m x := by
      simpa using hconv
    _ = _ := by rw [integral_weightedLeft]

private theorem exp_mul_crossCorrelation_integrable
    (s : ℝ) (n m : ℕ) :
    Integrable (fun u : ℝ ↦ ((Real.exp (s * u) : ℝ) : ℂ) *
      crossCorrelation (oddModeFunction n) (oddModeFunction m) u) := by
  have hconv := (weightedLeft_integrable s n).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (weightedRight_integrable s m)
  apply hconv.congr
  filter_upwards [] with u
  exact weighted_convolution_eq s n m u

private theorem positivePolar_oddMode_eq_integral (n : ℕ) :
    yoshidaPositivePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
        (yoshidaClippedOddMode yoshidaHalfLength n) =
      ∫ x : ℝ, weightedRight (-(1 / 2)) n x := by
  rw [yoshidaPositivePolarLinear, yoshidaCenteredLaplaceLinear_apply]
  have hpoint (x : ℝ) :
      Complex.exp (-((1 / 2 : ℂ) * (x : ℂ))) *
          yoshidaClippedOddMode yoshidaHalfLength n x =
        weightedRight (-(1 / 2)) n x := by
    unfold weightedRight oddModeFunction
    rw [show -((1 / 2 : ℂ) * (x : ℂ)) =
        (((-(1 / 2)) * x : ℝ) : ℂ) by push_cast; ring]
    rw [(Complex.ofReal_exp ((-(1 / 2)) * x)).symm]
  calc
    (∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength,
        Complex.exp (-((1 / 2 : ℂ) * (x : ℂ))) *
          yoshidaClippedOddMode yoshidaHalfLength n x) =
        ∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength,
          weightedRight (-(1 / 2)) n x := by
      apply intervalIntegral.integral_congr
      intro x _
      exact hpoint x
    _ = ∫ x : ℝ, weightedRight (-(1 / 2)) n x := by
      rw [intervalIntegral.integral_of_le (by linarith [yoshidaHalfLength_pos]),
        ← integral_Icc_eq_integral_Ioc]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
        unfold weightedRight oddModeFunction
        rw [yoshidaClippedSmooth_eq_zero_outside _ hx, mul_zero])

private theorem negativePolar_oddMode_eq_integral (n : ℕ) :
    yoshidaNegativePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
        (yoshidaClippedOddMode yoshidaHalfLength n) =
      ∫ x : ℝ, weightedRight (1 / 2) n x := by
  rw [yoshidaNegativePolarLinear, yoshidaCenteredLaplaceLinear_apply]
  have hpoint (x : ℝ) :
      Complex.exp (-((-1 / 2 : ℂ) * (x : ℂ))) *
          yoshidaClippedOddMode yoshidaHalfLength n x =
        weightedRight (1 / 2) n x := by
    unfold weightedRight oddModeFunction
    rw [show -((-1 / 2 : ℂ) * (x : ℂ)) =
        (((1 / 2) * x : ℝ) : ℂ) by push_cast; ring]
    rw [(Complex.ofReal_exp ((1 / 2) * x)).symm]
  calc
    (∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength,
        Complex.exp (-((-1 / 2 : ℂ) * (x : ℂ))) *
          yoshidaClippedOddMode yoshidaHalfLength n x) =
        ∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength,
          weightedRight (1 / 2) n x := by
      apply intervalIntegral.integral_congr
      intro x _
      exact hpoint x
    _ = ∫ x : ℝ, weightedRight (1 / 2) n x := by
      rw [intervalIntegral.integral_of_le (by linarith [yoshidaHalfLength_pos]),
        ← integral_Icc_eq_integral_Ioc]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
        unfold weightedRight oddModeFunction
        rw [yoshidaClippedSmooth_eq_zero_outside _ hx, mul_zero])

/-- The even polar weight against the odd-mode correlation folds to the
positive compact support interval. -/
theorem integral_polarWeight_crossCorrelation_eq_two_integral_correlation
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    (∫ u : ℝ,
      (((Real.exp (u / 2) + Real.exp (-u / 2) : ℝ) : ℂ) *
        crossCorrelation (oddModeFunction n) (oddModeFunction m) u)) =
      2 * ∫ u : ℝ in 0..yoshidaLength,
        (((Real.exp (u / 2) + Real.exp (-u / 2) : ℝ) : ℂ) *
          (clippedOddCorrelation yoshidaHalfLength n m u : ℂ)) := by
  let W : ℝ → ℂ := fun u ↦
    (((Real.exp (u / 2) + Real.exp (-u / 2) : ℝ) : ℂ) *
      crossCorrelation (oddModeFunction n) (oddModeFunction m) u)
  have hplus : Integrable (fun u : ℝ ↦
      ((Real.exp ((1 / 2 : ℝ) * u) : ℝ) : ℂ) *
        crossCorrelation (oddModeFunction n) (oddModeFunction m) u) :=
    exp_mul_crossCorrelation_integrable (1 / 2) n m
  have hminus : Integrable (fun u : ℝ ↦
      ((Real.exp ((-1 / 2 : ℝ) * u) : ℝ) : ℂ) *
        crossCorrelation (oddModeFunction n) (oddModeFunction m) u) :=
    exp_mul_crossCorrelation_integrable (-1 / 2) n m
  have hWint : Integrable W := by
    apply (hplus.add hminus).congr
    filter_upwards [] with u
    simp only [Pi.add_apply]
    dsimp only [W]
    push_cast
    ring_nf
  have hWeven : Function.Even W := by
    intro u
    dsimp only [W]
    rw [oddCrossCorrelation_even hn hm]
    congr 1
    push_cast
    simp only [neg_div, neg_neg]
    rw [add_comm]
  have hleft : (∫ u : ℝ in Set.Iic 0, W u) =
      ∫ u : ℝ in Set.Ioi 0, W u := by
    calc
      (∫ u : ℝ in Set.Iic 0, W u) =
          ∫ u : ℝ in Set.Iic 0, W (-u) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro u _
        exact (hWeven u).symm
      _ = ∫ u : ℝ in Set.Ioi 0, W u := by
        simpa only [neg_zero] using integral_comp_neg_Iic 0 W
  have hwhole : (∫ u : ℝ, W u) =
      2 * ∫ u : ℝ in Set.Ioi 0, W u := by
    rw [← intervalIntegral.integral_Iic_add_Ioi
        hWint.integrableOn hWint.integrableOn,
      hleft]
    ring
  have hpositive : (∫ u : ℝ in Set.Ioi 0, W u) =
      ∫ u : ℝ in 0..yoshidaLength, W u := by
    rw [intervalIntegral.integral_of_le yoshidaLength_pos.le]
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self
    intro u hu
    have huLt : yoshidaLength < u := by
      rcases hu with ⟨hu0, huNot⟩
      simp only [mem_Ioi] at hu0
      simp only [mem_Ioc, not_and, not_le] at huNot
      exact huNot hu0
    dsimp only [W]
    rw [oddCrossCorrelation_eq_zero_of_length_lt huLt, mul_zero]
  have hinterval : (∫ u : ℝ in 0..yoshidaLength, W u) =
      ∫ u : ℝ in 0..yoshidaLength,
        (((Real.exp (u / 2) + Real.exp (-u / 2) : ℝ) : ℂ) *
          (clippedOddCorrelation yoshidaHalfLength n m u : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc (0 : ℝ) yoshidaLength := by
      simpa only [uIcc_of_le yoshidaLength_pos.le] using hu
    dsimp only [W]
    rw [oddCrossCorrelation_eq_clippedOddCorrelation hu'.1 hu'.2 hn hm]
  change (∫ u : ℝ, W u) = _
  rw [hwhole, hpositive, hinterval]

/-- Production polar cross-term as the compact real-space correlation integral.
The factor `2` is from folding the even whole-line integrand. -/
theorem oddPolarCrossTerm_eq_two_integral_correlation
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    star (yoshidaPositivePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
        (yoshidaClippedOddMode yoshidaHalfLength n)) *
        yoshidaNegativePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
          (yoshidaClippedOddMode yoshidaHalfLength m) +
      star (yoshidaNegativePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
        (yoshidaClippedOddMode yoshidaHalfLength n)) *
        yoshidaPositivePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
          (yoshidaClippedOddMode yoshidaHalfLength m) =
      2 * ∫ u : ℝ in 0..yoshidaLength,
        (((Real.exp (u / 2) + Real.exp (-u / 2) : ℝ) : ℂ) *
          (clippedOddCorrelation yoshidaHalfLength n m u : ℂ)) := by
  have hpos := integral_exp_mul_crossCorrelation (1 / 2) n m
  have hneg := integral_exp_mul_crossCorrelation (-(1 / 2)) n m
  simp only [neg_neg] at hneg
  rw [← positivePolar_oddMode_eq_integral n,
    ← negativePolar_oddMode_eq_integral m] at hpos
  rw [← negativePolar_oddMode_eq_integral n,
    ← positivePolar_oddMode_eq_integral m] at hneg
  have hplusInt := exp_mul_crossCorrelation_integrable (1 / 2) n m
  have hminusInt := exp_mul_crossCorrelation_integrable (-(1 / 2)) n m
  calc
    star (yoshidaPositivePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
          (yoshidaClippedOddMode yoshidaHalfLength n)) *
          yoshidaNegativePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
            (yoshidaClippedOddMode yoshidaHalfLength m) +
        star (yoshidaNegativePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
          (yoshidaClippedOddMode yoshidaHalfLength n)) *
          yoshidaPositivePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
            (yoshidaClippedOddMode yoshidaHalfLength m) =
        (∫ u : ℝ, ((Real.exp ((1 / 2 : ℝ) * u) : ℝ) : ℂ) *
            crossCorrelation (oddModeFunction n) (oddModeFunction m) u) +
          ∫ u : ℝ, ((Real.exp ((-(1 / 2) : ℝ) * u) : ℝ) : ℂ) *
            crossCorrelation (oddModeFunction n) (oddModeFunction m) u := by
      rw [hpos, hneg]
    _ = ∫ u : ℝ,
        (((Real.exp (u / 2) + Real.exp (-u / 2) : ℝ) : ℂ) *
          crossCorrelation (oddModeFunction n) (oddModeFunction m) u) := by
      rw [← MeasureTheory.integral_add hplusInt hminusInt]
      apply integral_congr_ae
      filter_upwards [] with u
      push_cast
      ring_nf
    _ = _ := integral_polarWeight_crossCorrelation_eq_two_integral_correlation hn hm

end

end ArithmeticHodge.Analysis.YoshidaOddPolarCorrelation
