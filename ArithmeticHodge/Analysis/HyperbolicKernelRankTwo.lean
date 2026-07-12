import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open Complex MeasureTheory Real

namespace ArithmeticHodge.Analysis

noncomputable section

/-!
# Rank-two factorization of the hyperbolic difference kernel

The translation kernel `2 cosh (a (x-y) / 2)` is not a positive kernel.  Its
quadratic form is the difference of the squared cosh and sinh moments.  This
file records that exact structural factorization without discretizing the
operator.
-/

/-- The cosh moment at scale `a`. -/
def hyperbolicCoshMoment
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : X → ℝ) (a : ℝ) (f : X → ℂ) : ℂ :=
  ∫ x, (Real.cosh (a * u x / 2) : ℂ) * f x ∂μ

/-- The sinh moment at scale `a`. -/
def hyperbolicSinhMoment
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : X → ℝ) (a : ℝ) (f : X → ℂ) : ℂ :=
  ∫ x, (Real.sinh (a * u x / 2) : ℂ) * f x ∂μ

/-- Quadratic form of the hyperbolic difference kernel. -/
def hyperbolicDifferenceQuadratic
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : X → ℝ) (a : ℝ) (f : X → ℂ) : ℝ :=
  (∫ p : X × X,
    (Real.cosh (a * (u p.1 - u p.2) / 2) : ℂ) *
      f p.2 * star (f p.1) ∂μ.prod μ).re

theorem hyperbolic_difference_integrand_eq_rankTwo
    (a x y : ℝ) (zx zy : ℂ) :
    (Real.cosh (a * (x - y) / 2) : ℂ) * zy * star zx =
      star ((Real.cosh (a * x / 2) : ℂ) * zx) *
            ((Real.cosh (a * y / 2) : ℂ) * zy) -
        star ((Real.sinh (a * x / 2) : ℂ) * zx) *
          ((Real.sinh (a * y / 2) : ℂ) * zy) := by
  rw [show a * (x - y) / 2 = a * x / 2 - a * y / 2 by ring,
    Real.cosh_sub]
  let cx := Real.cosh (a * x / 2)
  let cy := Real.cosh (a * y / 2)
  let sx := Real.sinh (a * x / 2)
  let sy := Real.sinh (a * y / 2)
  change ((cx * cy - sx * sy : ℝ) : ℂ) * zy * star zx =
    star ((cx : ℂ) * zx) * ((cy : ℂ) * zy) -
      star ((sx : ℂ) * zx) * ((sy : ℂ) * zy)
  push_cast
  rw [star_mul', star_mul']
  have hcx : star (cx : ℂ) = (cx : ℂ) := by
    simpa only [Complex.star_def] using Complex.conj_ofReal cx
  have hsx : star (sx : ℂ) = (sx : ℂ) := by
    simpa only [Complex.star_def] using Complex.conj_ofReal sx
  rw [hcx, hsx]
  ring

theorem hyperbolicDifferenceQuadratic_eq_rankTwo
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (u : X → ℝ) (a : ℝ) (f : X → ℂ)
    (hcosh : Integrable
      (fun x ↦ (Real.cosh (a * u x / 2) : ℂ) * f x) μ)
    (hsinh : Integrable
      (fun x ↦ (Real.sinh (a * u x / 2) : ℂ) * f x) μ) :
    hyperbolicDifferenceQuadratic μ u a f =
      Complex.normSq (hyperbolicCoshMoment μ u a f) -
        Complex.normSq (hyperbolicSinhMoment μ u a f) := by
  let c : X → ℂ := fun x ↦
    (Real.cosh (a * u x / 2) : ℂ) * f x
  let s : X → ℂ := fun x ↦
    (Real.sinh (a * u x / 2) : ℂ) * f x
  have hc : Integrable c μ := by simpa only [c] using hcosh
  have hs : Integrable s μ := by simpa only [s] using hsinh
  have hcstar : Integrable (fun x ↦ star (c x)) μ := by
    simpa only [Complex.conjCLE_apply] using
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hc
  have hsstar : Integrable (fun x ↦ star (s x)) μ := by
    simpa only [Complex.conjCLE_apply] using
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hs
  have hcc : Integrable
      (fun p : X × X ↦ star (c p.1) * c p.2) (μ.prod μ) :=
    hcstar.mul_prod hc
  have hss : Integrable
      (fun p : X × X ↦ star (s p.1) * s p.2) (μ.prod μ) :=
    hsstar.mul_prod hs
  rw [hyperbolicDifferenceQuadratic]
  have hintegrand :
      (fun p : X × X ↦
        (Real.cosh (a * (u p.1 - u p.2) / 2) : ℂ) *
          f p.2 * star (f p.1)) =
      fun p ↦ star (c p.1) * c p.2 - star (s p.1) * s p.2 := by
    funext p
    simpa only [c, s] using
      hyperbolic_difference_integrand_eq_rankTwo
        a (u p.1) (u p.2) (f p.1) (f p.2)
  rw [hintegrand, integral_sub hcc hss]
  have hprodC :
      (∫ p : X × X, star (c p.1) * c p.2 ∂μ.prod μ) =
        (∫ x, star (c x) ∂μ) * ∫ x, c x ∂μ := by
    exact integral_prod_mul (fun x ↦ star (c x)) c
  have hprodS :
      (∫ p : X × X, star (s p.1) * s p.2 ∂μ.prod μ) =
        (∫ x, star (s x) ∂μ) * ∫ x, s x ∂μ := by
    exact integral_prod_mul (fun x ↦ star (s x)) s
  rw [hprodC, hprodS]
  rw [show (∫ x, star (c x) ∂μ) = star (∫ x, c x ∂μ) by
    exact integral_conj]
  rw [show (∫ x, star (s x) ∂μ) = star (∫ x, s x ∂μ) by
    exact integral_conj]
  have hnormC :
      star (∫ x, c x ∂μ) * (∫ x, c x ∂μ) =
        (Complex.normSq (∫ x, c x ∂μ) : ℂ) := by
    simpa only [starRingEnd_apply] using
      (Complex.normSq_eq_conj_mul_self (z := ∫ x, c x ∂μ)).symm
  have hnormS :
      star (∫ x, s x ∂μ) * (∫ x, s x ∂μ) =
        (Complex.normSq (∫ x, s x ∂μ) : ℂ) := by
    simpa only [starRingEnd_apply] using
      (Complex.normSq_eq_conj_mul_self (z := ∫ x, s x ∂μ)).symm
  rw [hnormC, hnormS]
  simp only [hyperbolicCoshMoment, hyperbolicSinhMoment, c, s,
    Complex.sub_re, Complex.ofReal_re]

end

end ArithmeticHodge.Analysis
