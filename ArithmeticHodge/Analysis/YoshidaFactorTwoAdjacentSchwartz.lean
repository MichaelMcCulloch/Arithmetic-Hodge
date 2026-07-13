import ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeCorrelationSymbol
import Mathlib.Analysis.Fourier.Convolution

set_option autoImplicit false

open Complex Real
open scoped Convolution SchwartzMap

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoAdjacentSchwartz

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaCauchyPairing
open YoshidaFactorTwoCrossDistribution

/-!
# Schwartz regularity of the adjacent-cell correlation

The physical adjacent correlation is itself a Schwartz function.  Bundling
that fact exposes all derivative and weighted-integrability properties needed
for structural kernel interchanges without modewise decay estimates.
-/

def criticalStarReflectionSchwartz (g : BombieriTest) : SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.conjCLE
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      ((LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv))
        (g.logarithmicPullbackSchwartz (1 / 2)))

@[simp] theorem criticalStarReflectionSchwartz_apply
    (g : BombieriTest) (x : ℝ) :
    criticalStarReflectionSchwartz g x =
      starReflection
        (g.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ) x := by
  simp [criticalStarReflectionSchwartz, starReflection,
    Complex.conjCLE_apply, RCLike.star_def]

def factorTwoAdjacentCorrelationSchwartz
    (g : BombieriTest) : SchwartzMap ℝ ℂ :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
    (criticalStarReflectionSchwartz g)
    ((normalizedDilation 2 (by norm_num) g).logarithmicPullbackSchwartz
      (1 / 2))

@[simp] theorem factorTwoAdjacentCorrelationSchwartz_apply
    (g : BombieriTest) (u : ℝ) :
    factorTwoAdjacentCorrelationSchwartz g u =
      factorTwoAdjacentCorrelation g u := by
  rw [factorTwoAdjacentCorrelationSchwartz,
    SchwartzMap.convolution_apply]
  unfold factorTwoAdjacentCorrelation bombieriCriticalCrossCorrelation
  rw [show (criticalStarReflectionSchwartz g : ℝ → ℂ) =
      starReflection
        (g.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ) by
    funext x
    exact criticalStarReflectionSchwartz_apply g x]
  rfl

theorem factorTwoAdjacentCorrelation_contDiff
    (g : BombieriTest) (n : ℕ∞) :
    ContDiff ℝ n (factorTwoAdjacentCorrelation g) := by
  have hfun : factorTwoAdjacentCorrelation g =
      (factorTwoAdjacentCorrelationSchwartz g : ℝ → ℂ) := by
    funext u
    exact (factorTwoAdjacentCorrelationSchwartz_apply g u).symm
  rw [hfun]
  exact (factorTwoAdjacentCorrelationSchwartz g).smooth n

theorem factorTwoAdjacentCorrelation_integrable
    (g : BombieriTest) :
    MeasureTheory.Integrable (factorTwoAdjacentCorrelation g) := by
  apply (factorTwoAdjacentCorrelationSchwartz g).integrable.congr
  filter_upwards [] with u
  exact factorTwoAdjacentCorrelationSchwartz_apply g u

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoAdjacentSchwartz
