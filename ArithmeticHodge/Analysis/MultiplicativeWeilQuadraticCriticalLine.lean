import ArithmeticHodge.Analysis.MultiplicativeWeilArchPolarLimit
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticMellin
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticSupport

/-!
# Critical-line form of Bombieri's quadratic local terms

For a quadratic test, the critical-line Mellin transform is a squared norm.
This rewrites the archimedean term as a real digamma-weighted squared-norm
integral and evaluates the two polar terms as a real cross product.
-/

set_option autoImplicit false

open Complex MeasureTheory Real Set Topology
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The quadratic Mellin transform is a squared norm on the critical line. -/
theorem mellin_bombieriQuadraticTest_critical_eq_normSq
    (g : BombieriTest) (v : ℝ) :
    mellin (bombieriQuadraticTest g : ℝ → ℂ)
        ((1 / 2 : ℝ) + v * I) =
      (Complex.normSq
        (mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)) : ℂ) := by
  change mellin ((bombieriQuadraticTestData g).test : ℝ → ℂ)
      ((1 / 2 : ℝ) + v * I) = _
  rw [(bombieriQuadraticTestData_hasMellin
    g ((1 / 2 : ℝ) + v * I)).2]
  apply spectralTerm_eq_normSq_of_re_eq_half
  norm_num

/-- The archimedean value of a quadratic test is the real gamma kernel
integrated against its critical-line Mellin squared norm. -/
theorem bombieriArchTerm_quadratic_eq_critical_normSq_integral
    (g : BombieriTest) :
    bombieriArchTerm (bombieriQuadraticTest g) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi : ℝ) : ℂ) *
              (Complex.normSq
                (mellin (g : ℝ → ℂ)
                  ((1 / 2 : ℝ) + v * I)) : ℂ) := by
  calc
    bombieriArchTerm (bombieriQuadraticTest g) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ,
            (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
              Real.log Real.pi : ℝ) : ℂ) *
                mellin (bombieriQuadraticTest g : ℝ → ℂ)
                  ((1 / 2 : ℝ) + v * I) :=
      (bombieriCriticalArchKernel_integral (bombieriQuadraticTest g)).symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      rw [mellin_bombieriQuadraticTest_critical_eq_normSq]

/-- The two polar Mellin values of a quadratic test form twice a real cross
product of the endpoint Mellin values of the original test. -/
theorem bombieriQuadratic_polar_eq_two_re
    (g : BombieriTest) :
    mellin (bombieriQuadraticTest g : ℝ → ℂ) 1 +
        mellin (bombieriQuadraticTest g : ℝ → ℂ) 0 =
      ((2 * (mellin (g : ℝ → ℂ) 1 *
        starRingEnd ℂ (mellin (g : ℝ → ℂ) 0)).re : ℝ) : ℂ) := by
  change mellin ((bombieriQuadraticTestData g).test : ℝ → ℂ) 1 +
      mellin ((bombieriQuadraticTestData g).test : ℝ → ℂ) 0 = _
  rw [(bombieriQuadraticTestData_hasMellin g 1).2,
    (bombieriQuadraticTestData_hasMellin g 0).2]
  unfold spectralTerm coefficientConjugate
  apply Complex.ext <;> simp <;> ring

/-- Exact small-support reduction to Bombieri--Yoshida's local weighted
Fourier inequality. -/
theorem bombieriFunctional_quadratic_eq_local_critical_form
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Icc a b) (hratio : b / a < 2) :
    bombieriFunctional (bombieriQuadraticTest g) =
      ((2 * (mellin (g : ℝ → ℂ) 1 *
        starRingEnd ℂ (mellin (g : ℝ → ℂ) 0)).re : ℝ) : ℂ) +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi : ℝ) : ℂ) *
              (Complex.normSq
                (mellin (g : ℝ → ℂ)
                  ((1 / 2 : ℝ) + v * I)) : ℂ) := by
  rw [bombieriFunctional_quadratic_eq_polar_add_arch_of_support_ratio_lt_two
      g ha hab hsupport hratio,
    bombieriQuadratic_polar_eq_two_re,
    bombieriArchTerm_quadratic_eq_critical_normSq_integral]

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
