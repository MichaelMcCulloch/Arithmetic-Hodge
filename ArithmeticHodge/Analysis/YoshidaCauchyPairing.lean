import ArithmeticHodge.Analysis.MultiplicativeWeilArchimedeanKernel
import Mathlib.Analysis.Fourier.Convolution

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ComplexConjugate Convolution FourierTransform

local notation "FT" => FourierTransform.fourier

namespace ArithmeticHodge.Analysis.YoshidaCauchyPairing

noncomputable section

open MultiplicativeWeil

/-!
# Cauchy Fourier pairing through cross-correlation

The two-sided exponential/Cauchy transform is combined with Mathlib's
convolution theorem to identify weighted products of angular Fourier
transforms with exponentially weighted cross-correlations.  The normalization
is the repository convention `exp (-I * v * x)`, hence the explicit
`1 / (2 * π)` scale.
-/

def angularFourier (H : ℝ → ℂ) (v : ℝ) : ℂ :=
  FT H (v / (2 * Real.pi))

theorem angular_cauchy_fourier_pairing
    {H : ℝ → ℂ} (hH : Integrable H) (hFH : Integrable (FT H))
    (hHcont : Continuous H) (a : ℝ) (ha : 0 < a) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ,
        (2 * a : ℂ) / ((a : ℂ) ^ 2 + (v : ℂ) ^ 2) *
          angularFourier H v) =
      ∫ x : ℝ, laplaceKernel a x * H x := by
  let G : ℝ → ℂ := fun v ↦
    (2 * a : ℂ) / ((a : ℂ) ^ 2 + (v : ℂ) ^ 2) * angularFourier H v
  have hscale := Measure.integral_comp_mul_left G (2 * Real.pi)
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, G v) =
        |(2 * Real.pi)⁻¹| • ∫ v : ℝ, G v := by
      rw [Complex.real_smul]
      congr 1
      rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
      push_cast
      rw [one_div]
    _ = ∫ w : ℝ, G ((2 * Real.pi) * w) := hscale.symm
    _ = ∫ w : ℝ,
        (2 * a : ℂ) / ((a : ℂ) ^ 2 + (2 * Real.pi * w : ℂ) ^ 2) *
          FT H w := by
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [G, angularFourier]
      congr 2
      · push_cast
        ring
      · field_simp [Real.pi_ne_zero]
    _ = ∫ w : ℝ, FT (laplaceKernel a) w * FT H w := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [fourier_laplaceKernel a w ha]
    _ = _ := integral_fourier_laplaceKernel_mul_fourier hH hFH hHcont a ha

def starReflection (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  star (f (-x))

private theorem starReflection_integrable
    {f : ℝ → ℂ} (hf : Integrable f) : Integrable (starReflection f) := by
  have hneg : Integrable (fun x : ℝ ↦ f (-x)) := hf.comp_neg
  simpa only [starReflection, RCLike.star_def] using
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hneg

private theorem starReflection_continuous
    {f : ℝ → ℂ} (hf : Continuous f) : Continuous (starReflection f) := by
  unfold starReflection
  fun_prop

private theorem fourier_conj
    (f : ℝ → ℂ) (w : ℝ) :
    FT (fun x ↦ conj (f x)) w = conj (FT f (-w)) := by
  rw [fourier_real_eq_integral_exp_smul, fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  calc
    (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * w) * I) * conj (f x)) =
        ∫ x : ℝ, conj
          (Complex.exp (↑(-2 * Real.pi * x * (-w)) * I) * f x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [map_mul, ← Complex.exp_conj]
      congr 1
      apply Complex.ext <;> simp [map_ofNat]
    _ = conj (∫ x : ℝ,
        Complex.exp (↑(-2 * Real.pi * x * (-w)) * I) * f x) := integral_conj

theorem fourier_starReflection
    (f : ℝ → ℂ) (w : ℝ) :
    FT (starReflection f) w = star (FT f w) := by
  rw [show starReflection f = fun x ↦ conj ((f ∘ LinearIsometryEquiv.neg ℝ) x) by
    funext x
    simp [starReflection, RCLike.star_def]]
  rw [fourier_conj]
  rw [fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) f (-w)]
  simp [RCLike.star_def]

def crossCorrelation (f g : ℝ → ℂ) : ℝ → ℂ :=
  starReflection f ⋆[ContinuousLinearMap.mul ℂ ℂ] g

theorem fourier_crossCorrelation
    {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g)
    (hfc : Continuous f) (hgc : Continuous g) (w : ℝ) :
    FT (crossCorrelation f g) w = star (FT f w) * FT g w := by
  rw [crossCorrelation,
    Real.fourier_mul_convolution_eq (starReflection_integrable hf) hg
      (starReflection_continuous hfc) hgc]
  rw [fourier_starReflection]

theorem crossCorrelation_apply (f g : ℝ → ℂ) (u : ℝ) :
    crossCorrelation f g u = ∫ x : ℝ, star (f x) * g (u + x) := by
  rw [crossCorrelation, MeasureTheory.convolution_def]
  change (∫ t : ℝ, star (f (-t)) * g (u - t)) = _
  simpa only [neg_neg, sub_neg_eq_add] using
    (MeasureTheory.integral_neg_eq_self
      (fun x : ℝ ↦ star (f x) * g (u + x)) volume)

private theorem crossCorrelation_integrable
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (crossCorrelation f g) := by
  exact (starReflection_integrable hf).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) hg

private theorem crossCorrelation_continuous
    {f g : ℝ → ℂ} (hf : Integrable f)
    (hgcont : Continuous g) (hgcompact : HasCompactSupport g) :
    Continuous (crossCorrelation f g) := by
  exact hgcompact.continuous_convolution_right
    (ContinuousLinearMap.mul ℂ ℂ)
    (starReflection_integrable hf).locallyIntegrable hgcont

private theorem laplaceKernel_eq_real (a u : ℝ) :
    laplaceKernel a u = (Real.exp (-a * |u|) : ℝ) := by
  rw [laplaceKernel]
  calc
    Complex.exp (-(a : ℂ) * (↑|u| : ℂ)) =
        Complex.exp ((-a * |u| : ℝ) : ℂ) := by
      congr 1
      push_cast
      ring
    _ = (Real.exp (-a * |u|) : ℝ) := (Complex.ofReal_exp _).symm

theorem angular_cauchy_crossCorrelation_pairing
    {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g)
    (hfcont : Continuous f) (hgcont : Continuous g)
    (hgcompact : HasCompactSupport g)
    (hprod : Integrable (fun w : ℝ ↦ star (FT f w) * FT g w))
    (a : ℝ) (ha : 0 < a) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ,
        (2 * a : ℂ) / ((a : ℂ) ^ 2 + (v : ℂ) ^ 2) *
          (star (angularFourier f v) * angularFourier g v)) =
      ∫ u : ℝ, (Real.exp (-a * |u|) : ℝ) * crossCorrelation f g u := by
  have hcorrInt : Integrable (crossCorrelation f g) :=
    crossCorrelation_integrable hf hg
  have hcorrCont : Continuous (crossCorrelation f g) :=
    crossCorrelation_continuous hf hgcont hgcompact
  have hfourierCorr : Integrable (FT (crossCorrelation f g)) := by
    apply hprod.congr
    filter_upwards [] with w
    exact (fourier_crossCorrelation hf hg hfcont hgcont w).symm
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ,
        (2 * a : ℂ) / ((a : ℂ) ^ 2 + (v : ℂ) ^ 2) *
          (star (angularFourier f v) * angularFourier g v)) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ,
            (2 * a : ℂ) / ((a : ℂ) ^ 2 + (v : ℂ) ^ 2) *
              angularFourier (crossCorrelation f g) v) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      rw [angularFourier, angularFourier, angularFourier,
        fourier_crossCorrelation hf hg hfcont hgcont]
    _ = ∫ u : ℝ,
        laplaceKernel a u * crossCorrelation f g u :=
      angular_cauchy_fourier_pairing hcorrInt hfourierCorr hcorrCont a ha
    _ = ∫ u : ℝ,
        (Real.exp (-a * |u|) : ℝ) * crossCorrelation f g u := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [laplaceKernel_eq_real]

theorem angular_cauchy_crossCorrelation_pairing_expanded
    {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g)
    (hfcont : Continuous f) (hgcont : Continuous g)
    (hgcompact : HasCompactSupport g)
    (hprod : Integrable (fun w : ℝ ↦ star (FT f w) * FT g w))
    (a : ℝ) (ha : 0 < a) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ,
        (2 * a : ℂ) / ((a : ℂ) ^ 2 + (v : ℂ) ^ 2) *
          (star (angularFourier f v) * angularFourier g v)) =
      ∫ u : ℝ, (Real.exp (-a * |u|) : ℝ) *
        (∫ x : ℝ, star (f x) * g (u + x)) := by
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ,
        (2 * a : ℂ) / ((a : ℂ) ^ 2 + (v : ℂ) ^ 2) *
          (star (angularFourier f v) * angularFourier g v)) =
        ∫ u : ℝ, (Real.exp (-a * |u|) : ℝ) * crossCorrelation f g u :=
      angular_cauchy_crossCorrelation_pairing hf hg hfcont hgcont hgcompact hprod a ha
    _ = ∫ u : ℝ, (Real.exp (-a * |u|) : ℝ) *
        (∫ x : ℝ, star (f x) * g (u + x)) := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [crossCorrelation_apply]

end

end ArithmeticHodge.Analysis.YoshidaCauchyPairing
