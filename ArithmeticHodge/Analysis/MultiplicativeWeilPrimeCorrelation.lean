import ArithmeticHodge.Analysis.MultiplicativeWeilGlobalPrimeDecomposition
import ArithmeticHodge.Analysis.MultiplicativeWeilDilation

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Prime terms as normalized-dilation correlations

The prime term missing from the ratio-two theorem is an explicit family of
long-range correlations.  In critical logarithmic coordinates normalized
dilation is translation, so these are precisely the lags invisible to one
fixed support-width window.
-/

/-- Correlation of a test with its `L²(dx)`-normalized multiplicative
dilation. -/
def criticalDilationCorrelation (g : BombieriTest) (lambda : ℝ) : ℂ :=
  ∫ y : ℝ in Set.Ioi 0,
    ((Real.sqrt lambda : ℝ) : ℂ) * g (lambda * y) *
      starRingEnd ℂ (g y)

/-- The dilation correlation is the normalized-dilation inner product. -/
theorem criticalDilationCorrelation_eq_normalizedDilation_inner
    (g : BombieriTest) (lambda : ℝ) (hlambda : 0 < lambda) :
    criticalDilationCorrelation g lambda =
      ∫ y : ℝ in Set.Ioi 0,
        normalizedDilation lambda hlambda g y * starRingEnd ℂ (g y) := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _hy
  rfl

/-- Equivalently, the normalized correlation is `sqrt(lambda)` times the
multiplicative autocorrelation at `lambda`. -/
theorem criticalDilationCorrelation_eq_sqrt_mul_quadraticTest
    (g : BombieriTest) (lambda : ℝ) :
    criticalDilationCorrelation g lambda =
      ((Real.sqrt lambda : ℝ) : ℂ) * bombieriQuadraticTest g lambda := by
  rw [bombieriQuadraticTest_apply]
  unfold criticalDilationCorrelation autocorrelation
  calc
    (∫ y : ℝ in Set.Ioi 0,
        ((Real.sqrt lambda : ℝ) : ℂ) * g (lambda * y) *
          starRingEnd ℂ (g y)) =
        ∫ y : ℝ in Set.Ioi 0,
          ((Real.sqrt lambda : ℝ) : ℂ) *
            (g (lambda * y) * starRingEnd ℂ (g y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = ((Real.sqrt lambda : ℝ) : ℂ) *
        ∫ y : ℝ in Set.Ioi 0,
          g (lambda * y) * starRingEnd ℂ (g y) := by
      exact MeasureTheory.integral_const_mul
        (μ := volume.restrict (Set.Ioi 0)) _ _

/-- Hermitian symmetry makes each quadratic prime kernel twice the real part
of one directed autocorrelation. -/
theorem primeKernel_bombieriQuadraticTest_eq_two_re
    (g : BombieriTest) (k : ℕ) :
    primeKernel (bombieriQuadraticTest g) k =
      ((2 * (bombieriQuadraticTest g ((k + 1 : ℕ) : ℝ)).re : ℝ) : ℂ) := by
  rw [primeKernel,
    transpose_bombieriQuadraticTest_apply_eq_conj g
      (by positivity : 0 < ((k + 1 : ℕ) : ℝ))]
  apply Complex.ext
  · simp
    ring
  · simp

/-- Exact prime-lag formula without division: multiplying a prime kernel by
`sqrt(k+1)` gives twice the real normalized-dilation correlation. -/
theorem sqrt_mul_primeKernel_bombieriQuadraticTest_eq_correlation_re
    (g : BombieriTest) (k : ℕ) :
    (((Real.sqrt ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
        primeKernel (bombieriQuadraticTest g) k) =
      ((2 * (criticalDilationCorrelation g ((k + 1 : ℕ) : ℝ)).re : ℝ) : ℂ) := by
  let n : ℝ := ((k + 1 : ℕ) : ℝ)
  have hn : 0 < n := by
    dsimp only [n]
    positivity
  have hcorr := congrArg Complex.re
    (criticalDilationCorrelation_eq_sqrt_mul_quadraticTest g n)
  rw [primeKernel_bombieriQuadraticTest_eq_two_re]
  change (((Real.sqrt n : ℝ) : ℂ) *
      ((2 * (bombieriQuadraticTest g n).re : ℝ) : ℂ)) =
    ((2 * (criticalDilationCorrelation g n).re : ℝ) : ℂ)
  apply Complex.ext
  · norm_num at hcorr ⊢
    nlinarith
  · simp

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
