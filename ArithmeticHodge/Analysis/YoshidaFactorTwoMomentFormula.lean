import ArithmeticHodge.Analysis.YoshidaBombieriCrossMoments
import ArithmeticHodge.Analysis.YoshidaFactorTwoCrossDistribution

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped FourierTransform SchwartzMap

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoMomentFormula

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaBombieriCrossMoments
open YoshidaFactorTwoCrossDistribution
open YoshidaRenormalizedGeometricKernel

/-!
# Exact rank-one moment formula for the factor-two symbol

The one-sided adjacent-cell support turns each Cauchy summand into a product
of two logarithmic moments.  The first decaying summand then cancels one polar
factor exactly, leaving one growing rank-one term, an infinite decaying
rank-one tail, and the two structurally isolated prime atoms.
-/

theorem bombieriCriticalMoment_normalizedDilation_two
    (g : BombieriTest) (s : ℝ) :
    bombieriCriticalMoment (normalizedDilation 2 (by norm_num) g) s =
      ((Real.exp (s * factorTwoLogLength) : ℝ) : ℂ) *
        bombieriCriticalMoment g s := by
  let F : ℝ → ℂ :=
    g.logarithmicPullbackSchwartz (1 / 2)
  let H : ℝ → ℂ := fun x ↦
    ((Real.exp (s * (x + factorTwoLogLength)) : ℝ) : ℂ) * F x
  unfold bombieriCriticalMoment
  calc
    (∫ x : ℝ, ((Real.exp (s * x) : ℝ) : ℂ) *
        (normalizedDilation 2 (by norm_num) g).logarithmicPullbackSchwartz
          (1 / 2) x) =
        ∫ x : ℝ, ((Real.exp (s * x) : ℝ) : ℂ) *
          F (x - factorTwoLogLength) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [normalizedDilation_logarithmicPullbackSchwartz_critical]
      rfl
    _ = ∫ x : ℝ, H (x + (-factorTwoLogLength)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [H, F]
      congr 2
      congr 1
      ring
    _ = ∫ x : ℝ, H x := MeasureTheory.integral_add_right_eq_self H _
    _ = ∫ x : ℝ,
        ((Real.exp (s * factorTwoLogLength) : ℝ) : ℂ) *
          (((Real.exp (s * x) : ℝ) : ℂ) * F x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [H]
      rw [show s * (x + factorTwoLogLength) =
          s * factorTwoLogLength + s * x by ring,
        Real.exp_add]
      push_cast
      ring
    _ = ((Real.exp (s * factorTwoLogLength) : ℝ) : ℂ) *
        ∫ x : ℝ, ((Real.exp (s * x) : ℝ) : ℂ) * F x := by
      exact MeasureTheory.integral_const_mul _ _

theorem bombieriCauchyCrossValue_dilation_two_eq_moment
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) (k : ℕ) :
    bombieriCauchyCrossValue g
        (normalizedDilation 2 (by norm_num) g) k =
      ((Real.exp (-oddRate k * factorTwoLogLength) : ℝ) : ℂ) *
        starRingEnd ℂ (bombieriCriticalMoment g (oddRate k)) *
        bombieriCriticalMoment g (-oddRate k) := by
  have hremoveAbs :
      bombieriCauchyCrossValue g
          (normalizedDilation 2 (by norm_num) g) k =
        ∫ u : ℝ,
          ((Real.exp ((-oddRate k) * u) : ℝ) : ℂ) *
            bombieriCriticalCrossCorrelation g
              (normalizedDilation 2 (by norm_num) g) u := by
    rw [bombieriCauchyCrossValue]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hu : u ∈ Set.Icc 0 (2 * factorTwoLogLength)
    · rw [abs_of_nonneg hu.1]
      congr 2
    · have hz := factorTwoAdjacentCorrelation_eq_zero_outside
        g ha hab hsupport hratio hu
      have hz' : bombieriCriticalCrossCorrelation g
          (normalizedDilation 2 (by norm_num) g) u = 0 := by
        simpa only [factorTwoAdjacentCorrelation] using hz
      rw [hz', mul_zero, mul_zero]
  rw [hremoveAbs,
    integral_exp_mul_bombieriCriticalCrossCorrelation,
    bombieriCriticalMoment_normalizedDilation_two]
  simp only [neg_neg, starRingEnd_apply]
  ring

def factorTwoGrowingMomentSymbol (g : BombieriTest) : ℂ :=
  ((Real.exp (factorTwoLogLength / 2) : ℝ) : ℂ) *
    starRingEnd ℂ (bombieriCriticalMoment g (-(1 / 2))) *
    bombieriCriticalMoment g (1 / 2)

def factorTwoTailMomentTerm (g : BombieriTest) (k : ℕ) : ℂ :=
  ((Real.exp (-oddRate (k + 1) * factorTwoLogLength) : ℝ) : ℂ) *
    starRingEnd ℂ (bombieriCriticalMoment g (oddRate (k + 1))) *
    bombieriCriticalMoment g (-oddRate (k + 1))

def factorTwoTailMomentSymbol (g : BombieriTest) : ℂ :=
  ∑' k : ℕ, factorTwoTailMomentTerm g k

private theorem exp_factorTwoLogLength_half_eq_sqrt_two :
    Real.exp (factorTwoLogLength / 2) = Real.sqrt 2 := by
  unfold factorTwoLogLength
  rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.exp_log (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]

private theorem exp_neg_factorTwoLogLength_half_eq_inv_sqrt_two :
    Real.exp (-factorTwoLogLength / 2) = (Real.sqrt 2)⁻¹ := by
  rw [show -factorTwoLogLength / 2 =
      -(factorTwoLogLength / 2) by ring,
    Real.exp_neg, exp_factorTwoLogLength_half_eq_sqrt_two]

theorem factorTwoLocalCrossSpectralSymbol_eq_moment
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoLocalCrossSpectralSymbol g =
      factorTwoGrowingMomentSymbol g - factorTwoTailMomentSymbol g := by
  have hcritical := normalized_factorTwoLocalCriticalKernel_eq_neg_cauchySeries
    g ha hab hsupport hratio
  have hzero := bombieriCauchyCrossValue_dilation_two_eq_moment
    g ha hab hsupport hratio 0
  have htail :
      (∑' k : ℕ,
        bombieriCauchyCrossValue g
          (normalizedDilation 2 (by norm_num) g) (k + 1)) =
        factorTwoTailMomentSymbol g := by
    apply tsum_congr
    intro k
    exact bombieriCauchyCrossValue_dilation_two_eq_moment
      g ha hab hsupport hratio (k + 1)
  rw [hzero, htail] at hcritical
  unfold factorTwoLocalCrossSpectralSymbol
  rw [factorTwoMellinWeight_zero, factorTwoMellinPhase_zero,
    factorTwoMellinWeight_one, factorTwoMellinWeight_half]
  simp only [one_mul, mul_one]
  have hcriticalAssoc :
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          bombieriLocalCriticalKernel v *
            starRingEnd ℂ
              (mellin (g : ℝ → ℂ)
                ((1 / 2 : ℝ) + v * Complex.I)) *
            (factorTwoMellinPhase v *
              mellin (g : ℝ → ℂ)
                ((1 / 2 : ℝ) + v * Complex.I))) =
        -(↑(Real.exp (-oddRate 0 * factorTwoLogLength)) *
              starRingEnd ℂ (bombieriCriticalMoment g (oddRate 0)) *
              bombieriCriticalMoment g (-oddRate 0) +
            factorTwoTailMomentSymbol g) := by
    calc
      _ = (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ,
            bombieriLocalCriticalKernel v *
              (starRingEnd ℂ
                (mellin (g : ℝ → ℂ)
                  ((1 / 2 : ℝ) + v * Complex.I)) *
                (factorTwoMellinPhase v *
                  mellin (g : ℝ → ℂ)
                    ((1 / 2 : ℝ) + v * Complex.I)))) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with v
        ring
      _ = _ := hcritical
  rw [hcriticalAssoc]
  rw [← YoshidaBombieriCrossMoments.bombieriCriticalMoment_neg_half_eq_mellin_one,
    ← YoshidaBombieriCrossMoments.bombieriCriticalMoment_half_eq_mellin_zero]
  unfold factorTwoGrowingMomentSymbol factorTwoTailMomentSymbol
  rw [show oddRate 0 = (1 / 2 : ℝ) by norm_num [oddRate]]
  rw [show -(1 / 2 : ℝ) * factorTwoLogLength =
      -factorTwoLogLength / 2 by ring]
  rw [exp_factorTwoLogLength_half_eq_sqrt_two,
    exp_neg_factorTwoLogLength_half_eq_inv_sqrt_two]
  simp only [starRingEnd_apply]
  ring

theorem factorTwoGlobalCrossSymbol_eq_moment_sub_prime
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoGlobalCrossSymbol g =
      factorTwoGrowingMomentSymbol g - factorTwoTailMomentSymbol g -
        factorTwoPrimeCrossSymbol g := by
  rw [factorTwoGlobalCrossSymbol_eq_spectral_sub_prime,
    factorTwoLocalCrossSpectralSymbol_eq_moment
      g ha hab hsupport hratio]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoMomentFormula
