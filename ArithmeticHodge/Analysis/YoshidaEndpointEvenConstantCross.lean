import ArithmeticHodge.Analysis.YoshidaEndpointEvenConstantDiagonal
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialIntegrable

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenConstantCross

open UnitIntervalLogEnergyAffine
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaRegularKernelBound
open YoshidaRegularKernelSchur

noncomputable section

/-- The real regular-kernel pairing before restricting to the diagonal. -/
def yoshidaEndpointRegularRealBilinear (u v : ℝ → ℝ) : ℂ :=
  let μ : Measure ℝ := volume.restrict (Icc (-1) 1)
  ∫ p : ℝ × ℝ,
    (yoshidaRegularKernel (yoshidaEndpointA * |p.1 - p.2|) : ℂ) *
      (u p.2 : ℂ) * star (v p.1 : ℂ) ∂μ.prod μ

/-- Symmetric regular-kernel cross functional between the constant profile
and a real residual. -/
def yoshidaEndpointRegularConstantCross (u : ℝ → ℝ) : ℝ :=
  (yoshidaEndpointRegularRealBilinear (fun _ ↦ 1) u +
    yoshidaEndpointRegularRealBilinear u (fun _ ↦ 1)).re

/-- The even hyperbolic moment which couples to the constant profile. -/
def yoshidaEndpointCoshMoment (u : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in -1..1, Real.cosh (yoshidaEndpointA * x / 2) * u x

/-- The exact coefficient of `2 c` in the clean endpoint quadratic of
`c + u`.  The raw logarithmic energy has no constant cross term. -/
def yoshidaEndpointEvenConstantCrossFunctional (u : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x) -
    yoshidaEndpointScalarMassLoss * (∫ x : ℝ in -1..1, u x) -
    (yoshidaEndpointA / 2) * yoshidaEndpointRegularConstantCross u +
    2 * yoshidaEndpointA *
      yoshidaEndpointCoshMoment (fun _ ↦ 1) * yoshidaEndpointCoshMoment u

/-- On the mean-zero subspace the scalar mass cross term cancels exactly. -/
theorem yoshidaEndpointEvenConstantCrossFunctional_of_integral_eq_zero
    (u : ℝ → ℝ) (hmean : (∫ x : ℝ in -1..1, u x) = 0) :
    yoshidaEndpointEvenConstantCrossFunctional u =
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x) -
        (yoshidaEndpointA / 2) * yoshidaEndpointRegularConstantCross u +
        2 * yoshidaEndpointA *
          yoshidaEndpointCoshMoment (fun _ ↦ 1) *
            yoshidaEndpointCoshMoment u := by
  unfold yoshidaEndpointEvenConstantCrossFunctional
  rw [hmean]
  ring

private theorem intervalIntegrable_endpointPotential_mul
    (u : ℝ → ℝ) (hu : Continuous u) :
    IntervalIntegrable
      (fun x ↦ yoshidaEndpointPotential x * u x) volume (-1) 1 := by
  have hplus :=
    YoshidaEndpointPotentialIntegrable.intervalIntegrable_endpointPotential_mul_sq
      (fun x ↦ u x + 1) (hu.add continuous_const)
  have huSq :=
    YoshidaEndpointPotentialIntegrable.intervalIntegrable_endpointPotential_mul_sq
      u hu
  have hone :=
    YoshidaEndpointPotentialIntegrable.intervalIntegrable_endpointPotential_mul_sq
      (fun _ : ℝ ↦ 1) continuous_const
  have hcomb := ((hplus.sub huSq).sub hone).const_mul (1 / 2 : ℝ)
  apply hcomb.congr
  intro x _hx
  ring

private theorem centeredRawLogEnergy_add_constant
    (u : ℝ → ℝ) (c : ℝ) :
    centeredRawLogEnergy (fun x ↦ c + u x) = centeredRawLogEnergy u := by
  unfold centeredRawLogEnergy
  apply intervalIntegral.integral_congr
  intro x _hx
  apply intervalIntegral.integral_congr
  intro y _hy
  ring

private theorem centeredRawLogEnergy_one :
    centeredRawLogEnergy (fun _ : ℝ ↦ 1) = 0 := by
  unfold centeredRawLogEnergy
  norm_num

private theorem integral_endpointPotential_add_constant_sq
    (u : ℝ → ℝ) (hu : Continuous u) (c : ℝ) :
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * (c + u x) ^ 2) =
      c ^ 2 * (∫ x : ℝ in -1..1, yoshidaEndpointPotential x) +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x ^ 2) +
        2 * c * (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * u x) := by
  have hV : IntervalIntegrable yoshidaEndpointPotential volume (-1) 1 := by
    simpa only [one_pow, mul_one] using
      YoshidaEndpointPotentialIntegrable.intervalIntegrable_endpointPotential_mul_sq
        (fun _ : ℝ ↦ 1) continuous_const
  have huSq :=
    YoshidaEndpointPotentialIntegrable.intervalIntegrable_endpointPotential_mul_sq
      u hu
  have hVu := intervalIntegrable_endpointPotential_mul u hu
  have hcV := hV.const_mul (c ^ 2)
  have hcross := hVu.const_mul (2 * c)
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * (c + u x) ^ 2) =
      fun x ↦ c ^ 2 * yoshidaEndpointPotential x +
        (yoshidaEndpointPotential x * u x ^ 2 +
          (2 * c) * (yoshidaEndpointPotential x * u x)) by
    funext x
    ring]
  rw [intervalIntegral.integral_add hcV (huSq.add hcross),
    intervalIntegral.integral_add huSq hcross,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

private theorem integral_add_constant_sq
    (u : ℝ → ℝ) (hu : Continuous u) (c : ℝ) :
    (∫ x : ℝ in -1..1, (c + u x) ^ 2) =
      2 * c ^ 2 + (∫ x : ℝ in -1..1, u x ^ 2) +
        2 * c * (∫ x : ℝ in -1..1, u x) := by
  have huSq : IntervalIntegrable (fun x ↦ u x ^ 2) volume (-1) 1 :=
    (hu.pow 2).intervalIntegrable (-1) 1
  have huInt : IntervalIntegrable u volume (-1) 1 := hu.intervalIntegrable (-1) 1
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ c ^ 2) volume (-1) 1 :=
    continuous_const.intervalIntegrable (-1) 1
  have hcross : IntervalIntegrable (fun x ↦ (2 * c) * u x) volume (-1) 1 :=
    huInt.const_mul (2 * c)
  rw [show (fun x : ℝ ↦ (c + u x) ^ 2) =
      fun x ↦ c ^ 2 + (u x ^ 2 + (2 * c) * u x) by
    funext x
    ring]
  rw [intervalIntegral.integral_add hconst (huSq.add hcross),
    intervalIntegral.integral_add huSq hcross,
    intervalIntegral.integral_const_mul]
  norm_num
  ring

private theorem integrable_endpointRegularRealBilinear
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    Integrable
      (fun p : ℝ × ℝ ↦
        (yoshidaRegularKernel (yoshidaEndpointA * |p.1 - p.2|) : ℂ) *
          (u p.2 : ℂ) * star (v p.1 : ℂ))
      ((volume.restrict (Icc (-1) 1)).prod
        (volume.restrict (Icc (-1) 1))) := by
  let I : Set ℝ := Icc (-1) 1
  let μ : Measure ℝ := volume.restrict I
  let K : ℝ × ℝ → ℂ := fun p ↦
    (yoshidaRegularKernel (yoshidaEndpointA * |p.1 - p.2|) : ℂ)
  let G : ℝ × ℝ → ℂ := fun p ↦ K p * (u p.2 : ℂ) * star (v p.1 : ℂ)
  have hregularMeas : Measurable yoshidaRegularKernel := by
    unfold yoshidaRegularKernel
    apply Measurable.ite (measurableSet_singleton 0)
    · fun_prop
    · fun_prop
  have hKMeas : Measurable K := by
    dsimp only [K]
    fun_prop
  have huInt : Integrable (fun x ↦ (u x : ℂ)) μ := by
    exact (Complex.continuous_ofReal.comp hu).continuousOn.integrableOn_compact
      isCompact_Icc
  have hvInt : Integrable (fun x ↦ (v x : ℂ)) μ := by
    exact (Complex.continuous_ofReal.comp hv).continuousOn.integrableOn_compact
      isCompact_Icc
  have hprodNorm : Integrable
      (fun p : ℝ × ℝ ↦ ‖u p.2‖ * ‖v p.1‖) (μ.prod μ) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, mul_comm] using
      hvInt.norm.mul_prod huInt.norm
  have hdomInt : Integrable
      (fun p : ℝ × ℝ ↦ (1 / 4 : ℝ) * (‖u p.2‖ * ‖v p.1‖))
      (μ.prod μ) := hprodNorm.const_mul (1 / 4 : ℝ)
  have hpMem : ∀ᵐ p ∂μ.prod μ, p ∈ I ×ˢ I := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  have hKBound : ∀ᵐ p ∂μ.prod μ, ‖K p‖ ≤ (1 / 4 : ℝ) := by
    filter_upwards [hpMem] with p hp
    have habs : |p.1 - p.2| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
    have harg0 : 0 ≤ yoshidaEndpointA * |p.1 - p.2| :=
      mul_nonneg yoshidaEndpointA_pos.le (abs_nonneg _)
    have harg2 : yoshidaEndpointA * |p.1 - p.2| ≤ Real.log 2 := by
      unfold yoshidaEndpointA
      nlinarith [mul_le_mul_of_nonneg_left habs
        (by positivity : 0 ≤ Real.log 2 / 2)]
    have hreg := yoshidaRegularKernel_mem_Icc harg0 harg2
    dsimp only [K]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hreg.1]
    exact hreg.2
  have hGMeas : AEStronglyMeasurable G (μ.prod μ) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [G]
    fun_prop
  have hGInt : Integrable G (μ.prod μ) := by
    refine hdomInt.mono' hGMeas ?_
    filter_upwards [hKBound] with p hp
    dsimp only [K] at hp
    dsimp only [G]
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Complex.norm_real]
    simp only [Complex.norm_real, Real.norm_eq_abs] at hp ⊢
    have hnonneg : 0 ≤ ‖u p.2‖ * ‖v p.1‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp hnonneg
  simpa only [I, μ, K, G] using hGInt

private theorem yoshidaEndpointRegularRealBilinear_add_constant_diagonal
    (u : ℝ → ℝ) (hu : Continuous u) (c : ℝ) :
    yoshidaEndpointRegularRealBilinear (fun x ↦ c + u x)
        (fun x ↦ c + u x) =
      (c ^ 2 : ℂ) *
          yoshidaEndpointRegularRealBilinear (fun _ ↦ 1) (fun _ ↦ 1) +
        yoshidaEndpointRegularRealBilinear u u +
        (c : ℂ) *
          (yoshidaEndpointRegularRealBilinear (fun _ ↦ 1) u +
            yoshidaEndpointRegularRealBilinear u (fun _ ↦ 1)) := by
  let μ : Measure ℝ := volume.restrict (Icc (-1) 1)
  let G : (ℝ → ℝ) → (ℝ → ℝ) → ℝ × ℝ → ℂ := fun f g p ↦
    (yoshidaRegularKernel (yoshidaEndpointA * |p.1 - p.2|) : ℂ) *
      (f p.2 : ℂ) * star (g p.1 : ℂ)
  have h11 : Integrable (G (fun _ ↦ 1) (fun _ ↦ 1)) (μ.prod μ) := by
    simpa only [G, μ] using integrable_endpointRegularRealBilinear
      (fun _ ↦ 1) (fun _ ↦ 1) continuous_const continuous_const
  have huu : Integrable (G u u) (μ.prod μ) := by
    simpa only [G, μ] using integrable_endpointRegularRealBilinear u u hu hu
  have h1u : Integrable (G (fun _ ↦ 1) u) (μ.prod μ) := by
    simpa only [G, μ] using integrable_endpointRegularRealBilinear
      (fun _ ↦ 1) u continuous_const hu
  have hu1 : Integrable (G u (fun _ ↦ 1)) (μ.prod μ) := by
    simpa only [G, μ] using integrable_endpointRegularRealBilinear
      u (fun _ ↦ 1) hu continuous_const
  have hcross : Integrable
      (fun p ↦ (c : ℂ) * (G (fun _ ↦ 1) u p + G u (fun _ ↦ 1) p))
      (μ.prod μ) := (h1u.add hu1).const_mul (c : ℂ)
  have hconst : Integrable
      (fun p ↦ (c ^ 2 : ℂ) * G (fun _ ↦ 1) (fun _ ↦ 1) p)
      (μ.prod μ) := h11.const_mul (c ^ 2 : ℂ)
  unfold yoshidaEndpointRegularRealBilinear
  dsimp only
  change (∫ p : ℝ × ℝ, G (fun x ↦ c + u x) (fun x ↦ c + u x) p
      ∂μ.prod μ) = _
  rw [show (fun p : ℝ × ℝ ↦
      G (fun x ↦ c + u x) (fun x ↦ c + u x) p) =
      fun p ↦ (c ^ 2 : ℂ) * G (fun _ ↦ 1) (fun _ ↦ 1) p +
        G u u p +
        (c : ℂ) * (G (fun _ ↦ 1) u p + G u (fun _ ↦ 1) p) by
    funext p
    dsimp only [G]
    simp
    ring]
  change (∫ p : ℝ × ℝ,
      ((c ^ 2 : ℂ) * G (fun _ ↦ 1) (fun _ ↦ 1) p + G u u p) +
        (c : ℂ) * (G (fun _ ↦ 1) u p + G u (fun _ ↦ 1) p)
      ∂μ.prod μ) =
    (c ^ 2 : ℂ) * (∫ p : ℝ × ℝ, G (fun _ ↦ 1) (fun _ ↦ 1) p ∂μ.prod μ) +
      (∫ p : ℝ × ℝ, G u u p ∂μ.prod μ) +
      (c : ℂ) * ((∫ p : ℝ × ℝ, G (fun _ ↦ 1) u p ∂μ.prod μ) +
        ∫ p : ℝ × ℝ, G u (fun _ ↦ 1) p ∂μ.prod μ)
  calc
    _ = (∫ p : ℝ × ℝ,
          (c ^ 2 : ℂ) * G (fun _ ↦ 1) (fun _ ↦ 1) p + G u u p
          ∂μ.prod μ) +
        ∫ p : ℝ × ℝ,
          (c : ℂ) * (G (fun _ ↦ 1) u p + G u (fun _ ↦ 1) p)
          ∂μ.prod μ := by
      simpa only [Pi.add_apply] using integral_add (hconst.add huu) hcross
    _ = ((∫ p : ℝ × ℝ,
          (c ^ 2 : ℂ) * G (fun _ ↦ 1) (fun _ ↦ 1) p ∂μ.prod μ) +
        ∫ p : ℝ × ℝ, G u u p ∂μ.prod μ) +
        ∫ p : ℝ × ℝ,
          (c : ℂ) * (G (fun _ ↦ 1) u p + G u (fun _ ↦ 1) p)
          ∂μ.prod μ := by
      rw [integral_add hconst huu]
    _ = _ := by
      have hconstEq :
          (∫ p : ℝ × ℝ,
              (c ^ 2 : ℂ) * G (fun _ ↦ 1) (fun _ ↦ 1) p ∂μ.prod μ) =
            (c ^ 2 : ℂ) *
              ∫ p : ℝ × ℝ, G (fun _ ↦ 1) (fun _ ↦ 1) p ∂μ.prod μ :=
        integral_const_mul _ _
      have hcrossEq :
          (∫ p : ℝ × ℝ,
              (c : ℂ) * (G (fun _ ↦ 1) u p + G u (fun _ ↦ 1) p)
              ∂μ.prod μ) =
            (c : ℂ) * ∫ p : ℝ × ℝ,
              G (fun _ ↦ 1) u p + G u (fun _ ↦ 1) p ∂μ.prod μ :=
        integral_const_mul _ _
      rw [hconstEq, hcrossEq, integral_add h1u hu1]

private theorem yoshidaEndpointRegularQuadratic_eq_bilinear
    (u : ℝ → ℝ) :
    yoshidaEndpointRegularQuadratic (fun x ↦ (u x : ℂ)) =
      yoshidaEndpointRegularRealBilinear u u := by
  unfold yoshidaEndpointRegularQuadratic
  unfold yoshidaEndpointRegularRealBilinear
  unfold yoshidaEndpointA
  rfl

private theorem yoshidaEndpointRegularQuadratic_add_constant
    (u : ℝ → ℝ) (hu : Continuous u) (c : ℝ) :
    (yoshidaEndpointRegularQuadratic
      (fun x ↦ ((c + u x : ℝ) : ℂ))).re =
      c ^ 2 *
          (yoshidaEndpointRegularQuadratic (fun _ : ℝ ↦ (1 : ℂ))).re +
        (yoshidaEndpointRegularQuadratic (fun x ↦ (u x : ℂ))).re +
        c * yoshidaEndpointRegularConstantCross u := by
  have h := yoshidaEndpointRegularRealBilinear_add_constant_diagonal u hu c
  have hcu := yoshidaEndpointRegularQuadratic_eq_bilinear
    (fun x ↦ c + u x)
  have hone : yoshidaEndpointRegularQuadratic (fun _ : ℝ ↦ (1 : ℂ)) =
      yoshidaEndpointRegularRealBilinear (fun _ ↦ 1) (fun _ ↦ 1) := by
    simpa only [ofReal_one] using
      yoshidaEndpointRegularQuadratic_eq_bilinear (fun _ : ℝ ↦ 1)
  have huu := yoshidaEndpointRegularQuadratic_eq_bilinear u
  rw [hcu, hone, huu, h]
  unfold yoshidaEndpointRegularConstantCross
  rw [← ofReal_pow]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]

private def yoshidaEndpointSinhMoment (u : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in -1..1, Real.sinh (yoshidaEndpointA * x / 2) * u x

private theorem complex_coshMoment_eq (u : ℝ → ℝ) :
    (∫ x : ℝ in -1..1,
        (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * (u x : ℂ)) =
      (yoshidaEndpointCoshMoment u : ℂ) := by
  unfold yoshidaEndpointCoshMoment
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x _hx
  norm_num

private theorem complex_sinhMoment_eq (u : ℝ → ℝ) :
    (∫ x : ℝ in -1..1,
        (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * (u x : ℂ)) =
      (yoshidaEndpointSinhMoment u : ℂ) := by
  unfold yoshidaEndpointSinhMoment
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x _hx
  norm_num

private theorem yoshidaEndpointCoshMoment_add_constant
    (u : ℝ → ℝ) (hu : Continuous u) (c : ℝ) :
    yoshidaEndpointCoshMoment (fun x ↦ c + u x) =
      c * yoshidaEndpointCoshMoment (fun _ ↦ 1) +
        yoshidaEndpointCoshMoment u := by
  have hweight : Continuous
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2)) := by fun_prop
  have hconst : IntervalIntegrable
      (fun x : ℝ ↦ c * Real.cosh (yoshidaEndpointA * x / 2))
      volume (-1) 1 := (hweight.intervalIntegrable (-1) 1).const_mul c
  have huInt : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * u x)
      volume (-1) 1 := (hweight.mul hu).intervalIntegrable (-1) 1
  unfold yoshidaEndpointCoshMoment
  rw [show (fun x : ℝ ↦
      Real.cosh (yoshidaEndpointA * x / 2) * (c + u x)) =
      fun x ↦ c * Real.cosh (yoshidaEndpointA * x / 2) +
        Real.cosh (yoshidaEndpointA * x / 2) * u x by
    funext x
    ring]
  rw [intervalIntegral.integral_add hconst huInt,
    intervalIntegral.integral_const_mul]
  simp only [mul_one]

private theorem yoshidaEndpointSinhMoment_add_constant
    (u : ℝ → ℝ) (hu : Continuous u) (c : ℝ) :
    yoshidaEndpointSinhMoment (fun x ↦ c + u x) =
      c * yoshidaEndpointSinhMoment (fun _ ↦ 1) +
        yoshidaEndpointSinhMoment u := by
  have hweight : Continuous
      (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2)) := by fun_prop
  have hconst : IntervalIntegrable
      (fun x : ℝ ↦ c * Real.sinh (yoshidaEndpointA * x / 2))
      volume (-1) 1 := (hweight.intervalIntegrable (-1) 1).const_mul c
  have huInt : IntervalIntegrable
      (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2) * u x)
      volume (-1) 1 := (hweight.mul hu).intervalIntegrable (-1) 1
  unfold yoshidaEndpointSinhMoment
  rw [show (fun x : ℝ ↦
      Real.sinh (yoshidaEndpointA * x / 2) * (c + u x)) =
      fun x ↦ c * Real.sinh (yoshidaEndpointA * x / 2) +
        Real.sinh (yoshidaEndpointA * x / 2) * u x by
    funext x
    ring]
  rw [intervalIntegral.integral_add hconst huInt,
    intervalIntegral.integral_const_mul]
  simp only [mul_one]

private theorem yoshidaEndpointSinhMoment_one :
    yoshidaEndpointSinhMoment (fun _ ↦ 1) = 0 := by
  have hodd : Function.Odd
      (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2)) := by
    intro x
    change Real.sinh (yoshidaEndpointA * -x / 2) =
      -Real.sinh (yoshidaEndpointA * x / 2)
    rw [show yoshidaEndpointA * -x / 2 =
      -(yoshidaEndpointA * x / 2) by ring, Real.sinh_neg]
  unfold yoshidaEndpointSinhMoment
  simp only [mul_one]
  have hchange := intervalIntegral.integral_comp_neg
    (f := fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2))
    (a := (-1 : ℝ)) (b := 1)
  have hneg :
      (∫ x : ℝ in -1..1, Real.sinh (yoshidaEndpointA * -x / 2)) =
        -(∫ x : ℝ in -1..1,
          Real.sinh (yoshidaEndpointA * x / 2)) := by
    rw [show (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * -x / 2)) =
        fun x ↦ -Real.sinh (yoshidaEndpointA * x / 2) by
      funext x
      exact hodd x,
      intervalIntegral.integral_neg]
  norm_num only [neg_neg] at hchange
  rw [hneg] at hchange
  linarith

private theorem yoshidaEndpointHyperbolicQuadratic_ofReal_eq_moments
    (u : ℝ → ℝ) :
    yoshidaEndpointHyperbolicQuadratic (fun x ↦ (u x : ℂ)) =
      2 * yoshidaEndpointA *
        (yoshidaEndpointCoshMoment u ^ 2 - yoshidaEndpointSinhMoment u ^ 2) := by
  unfold yoshidaEndpointHyperbolicQuadratic
  rw [complex_coshMoment_eq, complex_sinhMoment_eq]
  simp only [Complex.normSq_ofReal]
  ring

private theorem yoshidaEndpointHyperbolicQuadratic_add_constant
    (u : ℝ → ℝ) (hu : Continuous u) (c : ℝ) :
    yoshidaEndpointHyperbolicQuadratic
        (fun x ↦ ((c + u x : ℝ) : ℂ)) =
      c ^ 2 * yoshidaEndpointHyperbolicQuadratic (fun _ : ℝ ↦ (1 : ℂ)) +
        yoshidaEndpointHyperbolicQuadratic (fun x ↦ (u x : ℂ)) +
        4 * yoshidaEndpointA * c *
          yoshidaEndpointCoshMoment (fun _ ↦ 1) *
          yoshidaEndpointCoshMoment u := by
  have hC := yoshidaEndpointCoshMoment_add_constant u hu c
  have hS := yoshidaEndpointSinhMoment_add_constant u hu c
  have hS1 := yoshidaEndpointSinhMoment_one
  have hcu := yoshidaEndpointHyperbolicQuadratic_ofReal_eq_moments
    (fun x ↦ c + u x)
  have hone : yoshidaEndpointHyperbolicQuadratic (fun _ : ℝ ↦ (1 : ℂ)) =
      2 * yoshidaEndpointA *
        (yoshidaEndpointCoshMoment (fun _ ↦ 1) ^ 2 -
          yoshidaEndpointSinhMoment (fun _ ↦ 1) ^ 2) := by
    simpa only [ofReal_one] using
      yoshidaEndpointHyperbolicQuadratic_ofReal_eq_moments (fun _ : ℝ ↦ 1)
  have huu := yoshidaEndpointHyperbolicQuadratic_ofReal_eq_moments u
  rw [hcu, hone, huu, hC, hS, hS1]
  simp
  ring

/-- Exact constant/residual polarization of the clean endpoint quadratic. -/
theorem yoshidaEndpointOddCleanQuadratic_add_constant
    (u : ℝ → ℝ) (hu : Continuous u) (c : ℝ) :
    yoshidaEndpointOddCleanQuadratic (fun x ↦ c + u x) =
      c ^ 2 * yoshidaEndpointOddCleanQuadratic (fun _ ↦ 1) +
        yoshidaEndpointOddCleanQuadratic u +
        2 * c * yoshidaEndpointEvenConstantCrossFunctional u := by
  unfold yoshidaEndpointOddCleanQuadratic
  dsimp only
  rw [centeredRawLogEnergy_add_constant,
    integral_endpointPotential_add_constant_sq u hu c,
    integral_add_constant_sq u hu c,
    yoshidaEndpointRegularQuadratic_add_constant u hu c,
    yoshidaEndpointHyperbolicQuadratic_add_constant u hu c,
    centeredRawLogEnergy_one]
  unfold yoshidaEndpointEvenConstantCrossFunctional
  norm_num [intervalIntegral.integral_const]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenConstantCross
