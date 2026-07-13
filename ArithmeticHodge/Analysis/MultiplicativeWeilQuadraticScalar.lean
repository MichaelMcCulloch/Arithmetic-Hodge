import ArithmeticHodge.Analysis.MultiplicativeWeilTwoBumpPrimeFormula

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Scalar homogeneity of Bombieri's quadratic test

Complex scaling of the underlying test scales its autocorrelation by the
real squared norm.  This supplies the diagonal coefficient in the two-bump
Hermitian reduction.
-/

theorem bombieriQuadraticTest_smul
    (c : ℂ) (g : BombieriTest) :
    bombieriQuadraticTest (c • g) =
      ((Complex.normSq c : ℝ) : ℂ) • bombieriQuadraticTest g := by
  ext x
  simp only [bombieriQuadraticTest_apply, TestFunction.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  unfold autocorrelation
  change (∫ y : ℝ in Set.Ioi 0,
      (c * g (x * y)) * starRingEnd ℂ (c * g y)) =
    ((Complex.normSq c : ℝ) : ℂ) *
      ∫ y : ℝ in Set.Ioi 0,
        g (x * y) * starRingEnd ℂ (g y)
  calc
    (∫ y : ℝ in Set.Ioi 0,
        (c * g (x * y)) * starRingEnd ℂ (c * g y)) =
        ∫ y : ℝ in Set.Ioi 0,
          ((Complex.normSq c : ℝ) : ℂ) *
            (g (x * y) * starRingEnd ℂ (g y)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _hy
      change (c * g (x * y)) * starRingEnd ℂ (c * g y) =
        ((Complex.normSq c : ℝ) : ℂ) *
          (g (x * y) * starRingEnd ℂ (g y))
      have hconj : starRingEnd ℂ (c * g y) =
          starRingEnd ℂ c * starRingEnd ℂ (g y) :=
        map_mul (starRingEnd ℂ) _ _
      rw [hconj, Complex.normSq_eq_conj_mul_self]
      ring
    _ = ((Complex.normSq c : ℝ) : ℂ) *
        ∫ y : ℝ in Set.Ioi 0,
          g (x * y) * starRingEnd ℂ (g y) := by
      exact MeasureTheory.integral_const_mul
        (μ := volume.restrict (Set.Ioi 0)) _ _

theorem bombieriFunctional_quadratic_smul
    (c : ℂ) (g : BombieriTest) :
    bombieriFunctional (bombieriQuadraticTest (c • g)) =
      ((Complex.normSq c : ℝ) : ℂ) *
        bombieriFunctional (bombieriQuadraticTest g) := by
  rw [bombieriQuadraticTest_smul, map_smul]
  rfl

theorem bombieriFunctional_quadratic_smul_normalizedDilation
    (c : ℂ) (g : BombieriTest) (lambda : ℝ)
    (hlambda : 0 < lambda) :
    bombieriFunctional
        (bombieriQuadraticTest
          (c • normalizedDilation lambda hlambda g)) =
      ((Complex.normSq c : ℝ) : ℂ) *
        bombieriFunctional (bombieriQuadraticTest g) := by
  rw [bombieriFunctional_quadratic_smul,
    bombieriFunctional_quadratic_normalizedDilation]

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
