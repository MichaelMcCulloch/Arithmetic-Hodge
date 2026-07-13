import ArithmeticHodge.Analysis.YoshidaBombieriCrossDistribution

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ComplexConjugate Convolution

namespace ArithmeticHodge.Analysis.YoshidaBombieriCrossMoments

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaCauchyPairing

/-!
# Rank-one moments of the Bombieri cross-correlation

Exponential weights turn logarithmic cross-correlations into products of
one-dimensional Laplace moments.  This exact factorization is the
dimension-free replacement for finite Gram-table calculations.
-/

def bombieriCriticalMoment (f : BombieriTest) (s : ℝ) : ℂ :=
  ∫ x : ℝ, ((Real.exp (s * x) : ℝ) : ℂ) *
    f.logarithmicPullbackSchwartz (1 / 2) x

private def weightedCriticalRight
    (s : ℝ) (f : BombieriTest) (x : ℝ) : ℂ :=
  ((Real.exp (s * x) : ℝ) : ℂ) *
    f.logarithmicPullbackSchwartz (1 / 2) x

private def weightedCriticalLeft
    (s : ℝ) (f : BombieriTest) (x : ℝ) : ℂ :=
  ((Real.exp (s * x) : ℝ) : ℂ) *
    starReflection
      (f.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ) x

private theorem weightedCriticalRight_integrable
    (s : ℝ) (f : BombieriTest) :
    Integrable (weightedCriticalRight s f) := by
  have hcont : Continuous (weightedCriticalRight s f) := by
    unfold weightedCriticalRight
    have hexp : Continuous (fun x : ℝ ↦
        ((Real.exp (s * x) : ℝ) : ℂ)) := by fun_prop
    exact hexp.mul
      (f.logarithmicPullbackSchwartz (1 / 2)).continuous
  have hcompact : HasCompactSupport (weightedCriticalRight s f) := by
    unfold weightedCriticalRight
    exact (f.logarithmicPullback_hasCompactSupport (1 / 2)).mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

private theorem starReflection_criticalPullback_hasCompactSupport
    (f : BombieriTest) :
    HasCompactSupport (starReflection
      (f.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ)) := by
  have hneg : HasCompactSupport (fun x : ℝ ↦
      f.logarithmicPullbackSchwartz (1 / 2) (-x)) := by
    simpa only [Function.comp_apply] using
      (f.logarithmicPullback_hasCompactSupport (1 / 2)).comp_homeomorph
        (Homeomorph.neg ℝ)
  simpa only [starReflection, RCLike.star_def] using
    hneg.comp_left (by simp : conj (0 : ℂ) = 0)

private theorem weightedCriticalLeft_integrable
    (s : ℝ) (f : BombieriTest) :
    Integrable (weightedCriticalLeft s f) := by
  have hcont : Continuous (weightedCriticalLeft s f) := by
    unfold weightedCriticalLeft starReflection
    have hexp : Continuous (fun x : ℝ ↦
        ((Real.exp (s * x) : ℝ) : ℂ)) := by fun_prop
    exact hexp.mul
      (((f.logarithmicPullbackSchwartz (1 / 2)).continuous.comp
        continuous_neg).star)
  have hcompact : HasCompactSupport (weightedCriticalLeft s f) := by
    unfold weightedCriticalLeft
    exact (starReflection_criticalPullback_hasCompactSupport f).mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

private theorem weightedCritical_convolution_eq
    (s : ℝ) (f g : BombieriTest) (u : ℝ) :
    (weightedCriticalLeft s f ⋆[ContinuousLinearMap.mul ℂ ℂ]
        weightedCriticalRight s g) u =
      ((Real.exp (s * u) : ℝ) : ℂ) *
        bombieriCriticalCrossCorrelation f g u := by
  rw [MeasureTheory.convolution_def]
  calc
    (∫ t : ℝ,
        ContinuousLinearMap.mul ℂ ℂ (weightedCriticalLeft s f t)
          (weightedCriticalRight s g (u - t))) =
        ∫ t : ℝ, ((Real.exp (s * u) : ℝ) : ℂ) *
          (starReflection
              (f.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ) t *
            g.logarithmicPullbackSchwartz (1 / 2) (u - t)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      have hexp : Real.exp (s * t) * Real.exp (s * (u - t)) =
          Real.exp (s * u) := by
        rw [← Real.exp_add]
        congr 1
        ring
      dsimp only [weightedCriticalLeft, weightedCriticalRight]
      calc
        (((Real.exp (s * t) : ℝ) : ℂ) *
              starReflection
                (f.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ) t) *
            (((Real.exp (s * (u - t)) : ℝ) : ℂ) *
              g.logarithmicPullbackSchwartz (1 / 2) (u - t)) =
            ((((Real.exp (s * t) * Real.exp (s * (u - t)) : ℝ)) : ℂ) *
              (starReflection
                  (f.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ) t *
                g.logarithmicPullbackSchwartz (1 / 2) (u - t))) := by
          push_cast
          ring
        _ = _ := by rw [hexp]
    _ = ((Real.exp (s * u) : ℝ) : ℂ) *
        ∫ t : ℝ,
          starReflection
              (f.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ) t *
            g.logarithmicPullbackSchwartz (1 / 2) (u - t) := by
      exact MeasureTheory.integral_const_mul
        (((Real.exp (s * u) : ℝ) : ℂ)) _
    _ = _ := by
      rw [bombieriCriticalCrossCorrelation, crossCorrelation,
        MeasureTheory.convolution_def]
      congr 1

private theorem integral_weightedCriticalLeft
    (s : ℝ) (f : BombieriTest) :
    (∫ x : ℝ, weightedCriticalLeft s f x) =
      star (bombieriCriticalMoment f (-s)) := by
  calc
    (∫ x : ℝ, weightedCriticalLeft s f x) =
        ∫ x : ℝ, weightedCriticalLeft s f (-x) :=
      (MeasureTheory.integral_neg_eq_self
        (weightedCriticalLeft s f) volume).symm
    _ = ∫ x : ℝ, star (weightedCriticalRight (-s) f x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [weightedCriticalLeft, weightedCriticalRight,
        starReflection, neg_mul, neg_neg, RCLike.star_def, map_mul,
        conj_ofReal]
      congr 2
      congr 1
      ring
    _ = star (∫ x : ℝ, weightedCriticalRight (-s) f x) := by
      simpa only [RCLike.star_def] using
        (integral_conj (f := weightedCriticalRight (-s) f))
    _ = star (bombieriCriticalMoment f (-s)) := by rfl

theorem integral_exp_mul_bombieriCriticalCrossCorrelation
    (s : ℝ) (f g : BombieriTest) :
    (∫ u : ℝ, ((Real.exp (s * u) : ℝ) : ℂ) *
      bombieriCriticalCrossCorrelation f g u) =
      star (bombieriCriticalMoment f (-s)) *
        bombieriCriticalMoment g s := by
  have hconv := MeasureTheory.integral_convolution
    (ContinuousLinearMap.mul ℂ ℂ)
    (weightedCriticalLeft_integrable s f)
    (weightedCriticalRight_integrable s g)
  calc
    (∫ u : ℝ, ((Real.exp (s * u) : ℝ) : ℂ) *
        bombieriCriticalCrossCorrelation f g u) =
        ∫ u : ℝ,
          (weightedCriticalLeft s f ⋆[ContinuousLinearMap.mul ℂ ℂ]
            weightedCriticalRight s g) u := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact (weightedCritical_convolution_eq s f g u).symm
    _ = (∫ x : ℝ, weightedCriticalLeft s f x) *
          ∫ x : ℝ, weightedCriticalRight s g x := by
      simpa using hconv
    _ = _ := by
      rw [integral_weightedCriticalLeft]
      rfl

theorem exp_mul_bombieriCriticalCrossCorrelation_integrable
    (s : ℝ) (f g : BombieriTest) :
    Integrable (fun u : ℝ ↦ ((Real.exp (s * u) : ℝ) : ℂ) *
      bombieriCriticalCrossCorrelation f g u) := by
  have hconv := (weightedCriticalLeft_integrable s f).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ)
    (weightedCriticalRight_integrable s g)
  apply hconv.congr
  filter_upwards [] with u
  exact weightedCritical_convolution_eq s f g u

end

end ArithmeticHodge.Analysis.YoshidaBombieriCrossMoments
