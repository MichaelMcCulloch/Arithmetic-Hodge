import ArithmeticHodge.Analysis.YoshidaFactorTwoCrossDistribution
import ArithmeticHodge.Analysis.MultiplicativeWeilPrimeCorrelation

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ComplexConjugate

namespace ArithmeticHodge.Analysis.YoshidaCriticalLogCorrelation

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaCauchyPairing
open YoshidaFactorTwoCrossDistribution

/-!
# Critical logarithmic correlation and multiplicative dilation

The critical logarithmic pullback is an exact `L²(dx)` isometry.  This module
records the corresponding cross-correlation identity and transports the two
factor-two prime atoms into the same physical correlation used by the
archimedean symbol.
-/

private theorem expNeg_deriv :
    ∀ u ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (fun v : ℝ ↦ Real.exp (-v))
        (-Real.exp (-u)) Set.univ u := by
  intro u _hu
  change HasDerivWithinAt (Real.exp ∘ Neg.neg) _ Set.univ u
  exact mul_neg_one (Real.exp (-u)) ▸
    ((Real.hasDerivAt_exp (-u)).comp u
      (hasDerivAt_neg u)).hasDerivWithinAt

private theorem expNeg_image_univ :
    (fun u : ℝ ↦ Real.exp (-u)) '' Set.univ = Set.Ioi 0 := by
  rw [show (fun u : ℝ ↦ Real.exp (-u)) = Real.exp ∘ Neg.neg by rfl,
    Set.image_comp, Set.image_univ_of_surjective neg_surjective,
    Set.image_univ, Real.range_exp]

private theorem expNeg_injOn_univ :
    Set.InjOn (fun u : ℝ ↦ Real.exp (-u)) Set.univ :=
  Real.exp_injective.injOn.comp neg_injective.injOn
    (Set.univ.mapsTo_univ _)

/-- Ordinary Lebesgue measure on the positive half-line becomes the critical
Jacobian weight under `y = exp (-u)`. -/
theorem integral_Ioi_eq_integral_expNeg_mul (h : ℝ → ℂ) :
    (∫ y : ℝ in Set.Ioi 0, h y) =
      ∫ u : ℝ, ((Real.exp (-u) : ℝ) : ℂ) * h (Real.exp (-u)) := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ expNeg_deriv expNeg_injOn_univ h
  rw [expNeg_image_univ] at hchange
  calc
    (∫ y : ℝ in Set.Ioi 0, h y) =
        ∫ u : ℝ in Set.univ,
          |-Real.exp (-u)| • h (Real.exp (-u)) := hchange
    _ = ∫ u : ℝ, ((Real.exp (-u) : ℝ) : ℂ) *
          h (Real.exp (-u)) := by
      rw [setIntegral_univ]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [abs_neg, abs_of_pos (Real.exp_pos _), Complex.real_smul]

theorem bombieriCriticalCrossCorrelation_zero_eq_inner
    (f g : BombieriTest) :
    bombieriCriticalCrossCorrelation f g 0 =
      ∫ y : ℝ in Set.Ioi 0, starRingEnd ℂ (f y) * g y := by
  rw [bombieriCriticalCrossCorrelation, crossCorrelation_apply,
    integral_Ioi_eq_integral_expNeg_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [BombieriTest.logarithmicPullbackSchwartz_apply,
    BombieriTest.logarithmicPullback, zero_add]
  have hweight :
      (Real.exp (-(1 / 2) * u) : ℂ) *
          (Real.exp (-(1 / 2) * u) : ℂ) =
        (Real.exp (-u) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring
  change (starRingEnd ℂ)
      (((Real.exp (-(1 / 2) * u) : ℝ) : ℂ) * f (Real.exp (-u))) *
      (((Real.exp (-(1 / 2) * u) : ℝ) : ℂ) * g (Real.exp (-u))) =
    ((Real.exp (-u) : ℝ) : ℂ) *
      ((starRingEnd ℂ) (f (Real.exp (-u))) * g (Real.exp (-u)))
  rw [map_mul, Complex.conj_ofReal]
  calc
    (((Real.exp (-(1 / 2) * u) : ℝ) : ℂ) *
          (starRingEnd ℂ) (f (Real.exp (-u)))) *
        (((Real.exp (-(1 / 2) * u) : ℝ) : ℂ) *
          g (Real.exp (-u))) =
        (((Real.exp (-(1 / 2) * u) : ℝ) : ℂ) *
          ((Real.exp (-(1 / 2) * u) : ℝ) : ℂ)) *
          ((starRingEnd ℂ) (f (Real.exp (-u))) *
            g (Real.exp (-u))) := by ring
    _ = _ := by rw [hweight]

theorem bombieriCriticalCrossCorrelation_zero_dilation
    (g : BombieriTest) (lambda : ℝ) (hlambda : 0 < lambda) :
    bombieriCriticalCrossCorrelation g
        (normalizedDilation lambda hlambda g) 0 =
      criticalDilationCorrelation g lambda := by
  rw [bombieriCriticalCrossCorrelation_zero_eq_inner,
    criticalDilationCorrelation_eq_normalizedDilation_inner
      g lambda hlambda]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _hy
  ring

theorem factorTwoSelfCorrelation_neg
    (g : BombieriTest) (s : ℝ) :
    factorTwoSelfCorrelation g (-s) =
      starRingEnd ℂ (factorTwoSelfCorrelation g s) := by
  rw [factorTwoSelfCorrelation, factorTwoSelfCorrelation,
    crossCorrelation_apply, crossCorrelation_apply]
  let F : ℝ → ℂ :=
    g.logarithmicPullbackSchwartz (1 / 2)
  let G : ℝ → ℂ := fun y ↦ star (F (y + s)) * F y
  calc
    (∫ x : ℝ, star (F x) * F (-s + x)) =
        ∫ x : ℝ, G (x + (-s)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [G]
      congr 2 <;> ring_nf
    _ = ∫ y : ℝ, G y := MeasureTheory.integral_add_right_eq_self G (-s)
    _ = ∫ y : ℝ, star (star (F y) * F (s + y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp only [G]
      change conj (F (y + s)) * F y =
        conj (conj (F y) * F (s + y))
      rw [map_mul, conj_conj, add_comm y s, mul_comm]
    _ = star (∫ y : ℝ, star (F y) * F (s + y)) := by
      simpa only [RCLike.star_def] using
        (integral_conj (f := fun y : ℝ ↦ star (F y) * F (s + y)))

theorem factorTwoSelfCorrelation_neg_log_eq_sqrt_mul_quadratic
    (g : BombieriTest) (lambda : ℝ) (hlambda : 0 < lambda) :
    factorTwoSelfCorrelation g (-Real.log lambda) =
      ((Real.sqrt lambda : ℝ) : ℂ) * bombieriQuadraticTest g lambda := by
  calc
    factorTwoSelfCorrelation g (-Real.log lambda) =
        bombieriCriticalCrossCorrelation g
          (normalizedDilation lambda hlambda g) 0 := by
      rw [factorTwoSelfCorrelation, bombieriCriticalCrossCorrelation,
        crossCorrelation_apply, crossCorrelation_apply]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [normalizedDilation_logarithmicPullbackSchwartz_critical]
      congr 2
      ring
    _ = criticalDilationCorrelation g lambda :=
      bombieriCriticalCrossCorrelation_zero_dilation g lambda hlambda
    _ = ((Real.sqrt lambda : ℝ) : ℂ) *
        bombieriQuadraticTest g lambda :=
      criticalDilationCorrelation_eq_sqrt_mul_quadraticTest g lambda

theorem star_quadratic_eq_inv_sqrt_mul_selfCorrelation
    (g : BombieriTest) (lambda : ℝ) (hlambda : 0 < lambda) :
    starRingEnd ℂ (bombieriQuadraticTest g lambda) =
      (((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) *
        factorTwoSelfCorrelation g (Real.log lambda) := by
  have hneg := factorTwoSelfCorrelation_neg_log_eq_sqrt_mul_quadratic
    g lambda hlambda
  have hsym := factorTwoSelfCorrelation_neg g (Real.log lambda)
  have hroot : Real.sqrt lambda ≠ 0 := (Real.sqrt_pos.2 hlambda).ne'
  have hcorr : factorTwoSelfCorrelation g (Real.log lambda) =
      ((Real.sqrt lambda : ℝ) : ℂ) *
        starRingEnd ℂ (bombieriQuadraticTest g lambda) := by
    calc
      factorTwoSelfCorrelation g (Real.log lambda) =
          starRingEnd ℂ
            (factorTwoSelfCorrelation g (-Real.log lambda)) := by
        rw [hsym]
        simp
      _ = starRingEnd ℂ
          (((Real.sqrt lambda : ℝ) : ℂ) *
            bombieriQuadraticTest g lambda) := by rw [hneg]
      _ = ((Real.sqrt lambda : ℝ) : ℂ) *
          starRingEnd ℂ (bombieriQuadraticTest g lambda) := by
        rw [map_mul, Complex.conj_ofReal]
  rw [hcorr]
  push_cast
  field_simp [hroot]

end

end ArithmeticHodge.Analysis.YoshidaCriticalLogCorrelation
