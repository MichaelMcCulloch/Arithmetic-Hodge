import ArithmeticHodge.Analysis.MultiplicativeWeilCorrectedChebyshevPotentialStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilDirectedCorrelationDerivativeStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ContDiff

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCorrectedPotentialStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilCorrectedChebyshevPotentialStructural
open MultiplicativeWeilDirectedCorrelationDerivativeStructural

/-- The conjugated-correlation derivative integrand for two coherent cuts of
one parent.  The two summands respectively expose the partition boundary and
the derivative of the common parent. -/
def coherentStarCorrelationDerivativeIntegrand
    (parent : BombieriTest) (eta theta : ℝ → ℝ) (x y : ℝ) : ℂ :=
  (((y * deriv eta (x * y) * theta y : ℝ) : ℂ) *
      (starRingEnd ℂ (parent (x * y)) * parent y) +
    ((y * eta (x * y) * theta y : ℝ) : ℂ) *
      (starRingEnd ℂ (deriv parent (x * y)) * parent y))

/-- A strictly support-separated pair of coherent cuts has an exact corrected
Chebyshev representation in which the partition-boundary and parent-derivative
terms remain visibly separate.  The dilation parameter is one, so every
physical separated pair can use the same two outer kernels. -/
theorem bombieriTwoBlockGlobalCrossSymbol_eq_coherent_correctedPotential
    (parent f h : BombieriTest) (eta theta : ℝ → ℝ)
    (heta : ContDiff ℝ ∞ eta)
    (hfcoh : ∀ z : ℝ, f z = (eta z : ℂ) * parent z)
    (hhcoh : ∀ z : ℝ, h z = (theta z : ℂ) * parent z)
    {af bf ah bh : ℝ}
    (hah : 0 < ah) (hbh : 0 < bh)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hh : tsupport h ⊆ Set.Icc ah bh)
    (hsep : bh < af) :
    bombieriTwoBlockGlobalCrossSymbol f h =
      (∫ x : ℝ in Set.Ioi 0,
        ((Chebyshev.psi x - x : ℝ) : ℂ) *
          ∫ y : ℝ in Set.Ioi 0,
            coherentStarCorrelationDerivativeIntegrand
              parent eta theta x y) +
      ∫ x : ℝ in Set.Ioi 0,
        ((correctedChebyshevPotential x : ℝ) : ℂ) *
          ∫ y : ℝ in Set.Ioi 0,
            coherentStarCorrelationDerivativeIntegrand
              parent eta theta x y := by
  have haf : 0 < af := hbh.trans hsep
  have hratio : bh / af < 1 := by
    rw [div_lt_one haf]
    exact hsep
  have H :=
    sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_chebyshevError_add_correctedPotential
      f h (r := 1) (by norm_num) haf hah hbh hf hh hratio
  simp only [Real.sqrt_one, Complex.ofReal_one, one_mul,
    normalizedDilation_one] at H
  rw [H]
  congr 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x _hx
    simp only
    rw [(star_bombieriDirectedCorrelation_hasDerivAt_coherentWeights
      f h parent eta theta heta hfcoh hhcoh x).deriv]
    rfl
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x _hx
    simp only
    rw [(star_bombieriDirectedCorrelation_hasDerivAt_coherentWeights
      f h parent eta theta heta hfcoh hhcoh x).deriv]
    rfl

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCorrectedPotentialStructural
