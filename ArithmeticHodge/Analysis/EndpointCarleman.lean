import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.EndpointCarleman

noncomputable section

/-!
# Endpoint Carleman estimates

The Carleman kernel `1 / (p + q)` is controlled by the Schur weight
`p ↦ p⁻¹ᐟ²`.  This file records the weighted scalar inequality and its
endpoint integral consequences.
-/

/-- Weighted two-square inequality in the exact form used by the Carleman
Schur argument. -/
theorem two_mul_abs_mul_le_weighted_sq
    (x y r : ℝ) (hr : 0 < r) :
    2 * |x * y| ≤ r * x ^ 2 + y ^ 2 / r := by
  have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hamgm := two_mul_le_add_sq
    (Real.sqrt r * |x|) (|y| / Real.sqrt r)
  calc
    2 * |x * y| =
        2 * (Real.sqrt r * |x|) * (|y| / Real.sqrt r) := by
      rw [abs_mul]
      field_simp [hsqrt.ne']
    _ ≤ (Real.sqrt r * |x|) ^ 2 +
        (|y| / Real.sqrt r) ^ 2 := hamgm
    _ = r * x ^ 2 + y ^ 2 / r := by
      rw [mul_pow, div_pow, Real.sq_sqrt hr.le, sq_abs, sq_abs]

/-- Pointwise Carleman domination by the reciprocal square-root Schur
weights. -/
theorem two_mul_abs_mul_div_add_le_carleman_weights
    (x y p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    2 * |x * y| / (p + q) ≤
      ((Real.sqrt p / Real.sqrt q) * x ^ 2 +
        (Real.sqrt q / Real.sqrt p) * y ^ 2) / (p + q) := by
  have hsqrtp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hweight := two_mul_abs_mul_le_weighted_sq x y
    (Real.sqrt p / Real.sqrt q) (div_pos hsqrtp hsqrtq)
  have hrewrite :
      y ^ 2 / (Real.sqrt p / Real.sqrt q) =
        (Real.sqrt q / Real.sqrt p) * y ^ 2 := by
    field_simp [hsqrtp.ne', hsqrtq.ne']
  rw [hrewrite] at hweight
  exact div_le_div_of_nonneg_right hweight (by positivity)

/-- The reciprocal square-root Schur density has total mass `π` on the
positive half-line. -/
theorem integral_Ioi_inv_sqrt_mul_one_add :
    (∫ t : ℝ in Ioi 0,
      1 / (Real.sqrt t * (1 + t))) = Real.pi := by
  let h : ℝ → ℝ := fun t ↦ 1 / (Real.sqrt t * (1 + t))
  have hpow := integral_comp_rpow_Ioi_of_pos
    (g := h) (p := (2 : ℝ)) (by norm_num)
  have hchange :
      (∫ t : ℝ in Ioi 0, h t) =
        ∫ x : ℝ in Ioi 0, 2 * (1 + x ^ 2)⁻¹ := by
    rw [← hpow]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := hx
    dsimp only [h]
    norm_num
    have hsqrt : Real.sqrt (x ^ 2) = x := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hx0]
    rw [hsqrt]
    field_simp [hx0.ne']
  rw [show (∫ t : ℝ in Ioi 0,
      1 / (Real.sqrt t * (1 + t))) = ∫ t : ℝ in Ioi 0, h t by rfl,
    hchange, MeasureTheory.integral_const_mul,
    integral_Ioi_inv_one_add_sq]
  norm_num
  ring

/-- Integrability accompanying `integral_Ioi_inv_sqrt_mul_one_add`. -/
theorem integrableOn_Ioi_inv_sqrt_mul_one_add :
    IntegrableOn
      (fun t : ℝ ↦ 1 / (Real.sqrt t * (1 + t))) (Ioi 0) := by
  let h : ℝ → ℝ := fun t ↦ 1 / (Real.sqrt t * (1 + t))
  have hbase : IntegrableOn
      (fun x : ℝ ↦ 2 * (1 + x ^ 2)⁻¹) (Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul 2).integrableOn
  have hchange : IntegrableOn
      (fun x : ℝ ↦ (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) •
        h (x ^ (2 : ℝ))) (Ioi 0) := by
    apply hbase.congr_fun
    intro x hx
    have hx0 : 0 < x := hx
    dsimp only [h]
    norm_num
    have hsqrt : Real.sqrt (x ^ 2) = x := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hx0]
    rw [hsqrt]
    field_simp [hx0.ne']
    exact measurableSet_Ioi
  have hiff := integrableOn_Ioi_comp_rpow_iff h
    (p := (2 : ℝ)) (by norm_num)
  exact hiff.mp hchange

/-- Exact Schur row sum of the Carleman kernel against the weight
`q ↦ q⁻¹ᐟ²`. -/
theorem integral_Ioi_carleman_schur_weight
    (p : ℝ) (hp : 0 < p) :
    (∫ q : ℝ in Ioi 0,
      (Real.sqrt p / Real.sqrt q) / (p + q)) = Real.pi := by
  let k : ℝ → ℝ := fun q ↦
    (Real.sqrt p / Real.sqrt q) / (p + q)
  let h : ℝ → ℝ := fun t ↦
    1 / (Real.sqrt t * (1 + t))
  have hscale := integral_comp_mul_left_Ioi k 0 hp
  simp only [mul_zero, smul_eq_mul] at hscale
  field_simp [hp.ne'] at hscale
  have hpoint : ∀ t ∈ Ioi (0 : ℝ), p * k (p * t) = h t := by
    intro t ht
    have ht0 : 0 < t := ht
    have hsqrtp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
    have hsqrtt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    dsimp only [k, h]
    rw [Real.sqrt_mul hp.le]
    field_simp [hp.ne', hsqrtp.ne', hsqrtt.ne']
  calc
    (∫ q : ℝ in Ioi 0,
        (Real.sqrt p / Real.sqrt q) / (p + q)) =
        ∫ q : ℝ in Ioi 0, k q := by rfl
    _ = p * ∫ t : ℝ in Ioi 0, k (p * t) := hscale.symm
    _ = ∫ t : ℝ in Ioi 0, p * k (p * t) := by
      rw [MeasureTheory.integral_const_mul]
    _ = ∫ t : ℝ in Ioi 0, h t := by
      apply setIntegral_congr_fun measurableSet_Ioi hpoint
    _ = Real.pi := by
      simpa only [h] using integral_Ioi_inv_sqrt_mul_one_add

/-- Integrability accompanying the exact Carleman Schur row sum. -/
theorem integrableOn_Ioi_carleman_schur_weight
    (p : ℝ) (hp : 0 < p) :
    IntegrableOn
      (fun q : ℝ ↦ (Real.sqrt p / Real.sqrt q) / (p + q))
      (Ioi 0) := by
  let k : ℝ → ℝ := fun q ↦
    (Real.sqrt p / Real.sqrt q) / (p + q)
  let h : ℝ → ℝ := fun t ↦
    1 / (Real.sqrt t * (1 + t))
  have hh : IntegrableOn h (Ioi 0) := by
    simpa only [h] using integrableOn_Ioi_inv_sqrt_mul_one_add
  have hcomp : IntegrableOn (fun t : ℝ ↦ k (p * t)) (Ioi 0) := by
    have hscaled : IntegrableOn (fun t : ℝ ↦ (1 / p) * h t) (Ioi 0) :=
      hh.const_mul (1 / p)
    apply hscaled.congr_fun
    intro t ht
    have ht0 : 0 < t := ht
    have hsqrtp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
    have hsqrtt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    dsimp only [k, h]
    rw [Real.sqrt_mul hp.le]
    field_simp [hp.ne', hsqrtp.ne', hsqrtt.ne']
    exact measurableSet_Ioi
  simpa only [k, mul_zero] using
    (integrableOn_Ioi_comp_mul_left_iff k 0 hp).mp hcomp

/-- The first weighted square in the Carleman Schur decomposition. -/
def carlemanFirstSchurMajorant
    (f : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  f z.1 ^ 2 *
    ((Real.sqrt z.1 / Real.sqrt z.2) / (z.1 + z.2))

/-- The second weighted square in the Carleman Schur decomposition. -/
def carlemanSecondSchurMajorant
    (g : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  g z.2 ^ 2 *
    ((Real.sqrt z.2 / Real.sqrt z.1) / (z.1 + z.2))

/-- The absolute Carleman bilinear density. -/
def carlemanAbsBilinearDensity
    (f g : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  |f z.1 * g z.2| / (z.1 + z.2)

theorem carlemanSecondSchurMajorant_eq_first_swap
    (g : ℝ → ℝ) (z : ℝ × ℝ) :
    carlemanSecondSchurMajorant g z =
      carlemanFirstSchurMajorant g z.swap := by
  rcases z with ⟨p, q⟩
  unfold carlemanSecondSchurMajorant carlemanFirstSchurMajorant
  simp only [Prod.swap_prod_mk]
  rw [add_comm]

/-- The first Schur majorant is integrable whenever the input square is
integrable on the positive half-line. -/
theorem integrable_carlemanFirstSchurMajorant
    (f : ℝ → ℝ) (hfcont : Continuous f)
    (hf2 : IntegrableOn (fun p : ℝ ↦ f p ^ 2) (Ioi 0)) :
    Integrable (carlemanFirstSchurMajorant f)
      ((volume.restrict (Ioi 0)).prod
        (volume.restrict (Ioi 0))) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  have hmeas : Measurable (carlemanFirstSchurMajorant f) := by
    unfold carlemanFirstSchurMajorant
    fun_prop
  have hinner : ∀ᵐ p ∂μ,
      Integrable (fun q : ℝ ↦
        carlemanFirstSchurMajorant f (p, q)) μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hk := integrableOn_Ioi_carleman_schur_weight p hp
    simpa only [μ, carlemanFirstSchurMajorant] using
      hk.const_mul (f p ^ 2)
  have hinnerNorm : ∀ᵐ p ∂μ,
      (∫ q : ℝ, ‖carlemanFirstSchurMajorant f (p, q)‖ ∂μ) =
        Real.pi * f p ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hp0 : 0 < p := hp
    calc
      (∫ q : ℝ, ‖carlemanFirstSchurMajorant f (p, q)‖ ∂μ) =
          ∫ q : ℝ,
            f p ^ 2 *
              ((Real.sqrt p / Real.sqrt q) / (p + q)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
        have hq0 : 0 < q := hq
        change |f p ^ 2 *
          ((Real.sqrt p / Real.sqrt q) / (p + q))| = _
        rw [abs_of_nonneg]
        exact mul_nonneg (sq_nonneg _)
          (div_nonneg (div_nonneg (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)) (by linarith))
      _ = f p ^ 2 *
          (∫ q : ℝ in Ioi 0,
            (Real.sqrt p / Real.sqrt q) / (p + q)) := by
        simp only [μ, MeasureTheory.integral_const_mul]
      _ = Real.pi * f p ^ 2 := by
        rw [integral_Ioi_carleman_schur_weight p hp0]
        ring
  have houter : Integrable
      (fun p : ℝ ↦
        ∫ q : ℝ, ‖carlemanFirstSchurMajorant f (p, q)‖ ∂μ) μ := by
    have hpi : Integrable (fun p : ℝ ↦ Real.pi * f p ^ 2) μ := by
      simpa only [μ] using hf2.const_mul Real.pi
    apply hpi.congr
    filter_upwards [hinnerNorm] with p hp
    exact hp.symm
  change Integrable (carlemanFirstSchurMajorant f) (μ.prod μ)
  exact (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    ⟨hinner, houter⟩

/-- Exact integral of the first Schur majorant. -/
theorem integral_carlemanFirstSchurMajorant
    (f : ℝ → ℝ) (hfcont : Continuous f)
    (hf2 : IntegrableOn (fun p : ℝ ↦ f p ^ 2) (Ioi 0)) :
    (∫ z : ℝ × ℝ, carlemanFirstSchurMajorant f z
      ∂((volume.restrict (Ioi 0)).prod
        (volume.restrict (Ioi 0)))) =
      Real.pi * (∫ p : ℝ in Ioi 0, f p ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  have hmajorant := integrable_carlemanFirstSchurMajorant
    f hfcont hf2
  change (∫ z : ℝ × ℝ, carlemanFirstSchurMajorant f z ∂μ.prod μ) = _
  rw [integral_prod _ hmajorant]
  calc
    (∫ p : ℝ,
        ∫ q : ℝ, carlemanFirstSchurMajorant f (p, q) ∂μ ∂μ) =
        ∫ p : ℝ, Real.pi * f p ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
      change (∫ q : ℝ,
        f p ^ 2 *
          ((Real.sqrt p / Real.sqrt q) / (p + q)) ∂μ) = _
      rw [MeasureTheory.integral_const_mul]
      change f p ^ 2 *
        (∫ q : ℝ in Ioi 0,
          (Real.sqrt p / Real.sqrt q) / (p + q)) = _
      rw [integral_Ioi_carleman_schur_weight p hp]
      ring
    _ = Real.pi * (∫ p : ℝ in Ioi 0, f p ^ 2) := by
      simp only [μ, MeasureTheory.integral_const_mul]

/-- The second Schur majorant is the swapped first majorant. -/
theorem integrable_carlemanSecondSchurMajorant
    (g : ℝ → ℝ) (hgcont : Continuous g)
    (hg2 : IntegrableOn (fun q : ℝ ↦ g q ^ 2) (Ioi 0)) :
    Integrable (carlemanSecondSchurMajorant g)
      ((volume.restrict (Ioi 0)).prod
        (volume.restrict (Ioi 0))) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  have hfirst := integrable_carlemanFirstSchurMajorant g hgcont hg2
  have hswap := hfirst.swap
  change Integrable (carlemanSecondSchurMajorant g) (μ.prod μ)
  apply hswap.congr
  filter_upwards [] with z
  exact (carlemanSecondSchurMajorant_eq_first_swap g z).symm

/-- Exact integral of the second Schur majorant. -/
theorem integral_carlemanSecondSchurMajorant
    (g : ℝ → ℝ) (hgcont : Continuous g)
    (hg2 : IntegrableOn (fun q : ℝ ↦ g q ^ 2) (Ioi 0)) :
    (∫ z : ℝ × ℝ, carlemanSecondSchurMajorant g z
      ∂((volume.restrict (Ioi 0)).prod
        (volume.restrict (Ioi 0)))) =
      Real.pi * (∫ q : ℝ in Ioi 0, g q ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  have hfirst := integrable_carlemanFirstSchurMajorant g hgcont hg2
  have hfirstIntegral := integral_carlemanFirstSchurMajorant g hgcont hg2
  calc
    (∫ z : ℝ × ℝ, carlemanSecondSchurMajorant g z ∂μ.prod μ) =
        ∫ z : ℝ × ℝ,
          carlemanFirstSchurMajorant g z.swap ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact carlemanSecondSchurMajorant_eq_first_swap g z
    _ = ∫ z : ℝ × ℝ,
          carlemanFirstSchurMajorant g z ∂μ.prod μ := by
      exact integral_prod_swap (carlemanFirstSchurMajorant g)
    _ = Real.pi * (∫ q : ℝ in Ioi 0, g q ^ 2) := by
      simpa only [μ] using hfirstIntegral

/-- Pointwise Schur domination of the absolute Carleman density. -/
theorem two_mul_carlemanAbsBilinearDensity_le_majorants
    (f g : ℝ → ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    2 * carlemanAbsBilinearDensity f g (p, q) ≤
      carlemanFirstSchurMajorant f (p, q) +
        carlemanSecondSchurMajorant g (p, q) := by
  have hpoint := two_mul_abs_mul_div_add_le_carleman_weights
    (f p) (g q) p q hp hq
  unfold carlemanAbsBilinearDensity carlemanFirstSchurMajorant
    carlemanSecondSchurMajorant
  calc
    2 * (|f p * g q| / (p + q)) =
        2 * |f p * g q| / (p + q) := by ring
    _ ≤ ((Real.sqrt p / Real.sqrt q) * f p ^ 2 +
          (Real.sqrt q / Real.sqrt p) * g q ^ 2) / (p + q) :=
      hpoint
    _ = f p ^ 2 * ((Real.sqrt p / Real.sqrt q) / (p + q)) +
        g q ^ 2 * ((Real.sqrt q / Real.sqrt p) / (p + q)) := by
      ring

/-- The absolute Carleman bilinear density is integrable for continuous
positive-half-line `L²` data. -/
theorem integrable_carlemanAbsBilinearDensity
    (f g : ℝ → ℝ) (hfcont : Continuous f) (hgcont : Continuous g)
    (hf2 : IntegrableOn (fun p : ℝ ↦ f p ^ 2) (Ioi 0))
    (hg2 : IntegrableOn (fun q : ℝ ↦ g q ^ 2) (Ioi 0)) :
    Integrable (carlemanAbsBilinearDensity f g)
      ((volume.restrict (Ioi 0)).prod
        (volume.restrict (Ioi 0))) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let M : ℝ × ℝ → ℝ := fun z ↦
    (1 / 2 : ℝ) *
      (carlemanFirstSchurMajorant f z +
        carlemanSecondSchurMajorant g z)
  have hfirst := integrable_carlemanFirstSchurMajorant f hfcont hf2
  have hsecond := integrable_carlemanSecondSchurMajorant g hgcont hg2
  have hM : Integrable M (μ.prod μ) := by
    dsimp only [M]
    exact (hfirst.add hsecond).const_mul (1 / 2 : ℝ)
  have hCmeas : Measurable (carlemanAbsBilinearDensity f g) := by
    unfold carlemanAbsBilinearDensity
    fun_prop
  have hpq : ∀ᵐ z ∂μ.prod μ, z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  change Integrable (carlemanAbsBilinearDensity f g) (μ.prod μ)
  apply hM.mono' hCmeas.aestronglyMeasurable
  filter_upwards [hpq] with z hz
  have hp : 0 < z.1 := hz.1
  have hq : 0 < z.2 := hz.2
  have hC0 : 0 ≤ carlemanAbsBilinearDensity f g z := by
    unfold carlemanAbsBilinearDensity
    exact div_nonneg (abs_nonneg _) (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg hC0]
  dsimp only [M]
  have hpoint := two_mul_carlemanAbsBilinearDensity_le_majorants
    f g z.1 z.2 hp hq
  nlinarith

/-- Sharp Schur-form Carleman bound on the positive half-line. -/
theorem integral_carlemanAbsBilinearDensity_le
    (f g : ℝ → ℝ) (hfcont : Continuous f) (hgcont : Continuous g)
    (hf2 : IntegrableOn (fun p : ℝ ↦ f p ^ 2) (Ioi 0))
    (hg2 : IntegrableOn (fun q : ℝ ↦ g q ^ 2) (Ioi 0)) :
    (∫ z : ℝ × ℝ, carlemanAbsBilinearDensity f g z
      ∂((volume.restrict (Ioi 0)).prod
        (volume.restrict (Ioi 0)))) ≤
      (Real.pi / 2) *
        ((∫ p : ℝ in Ioi 0, f p ^ 2) +
          (∫ q : ℝ in Ioi 0, g q ^ 2)) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let M : ℝ × ℝ → ℝ := fun z ↦
    (1 / 2 : ℝ) *
      (carlemanFirstSchurMajorant f z +
        carlemanSecondSchurMajorant g z)
  have hfirst := integrable_carlemanFirstSchurMajorant f hfcont hf2
  have hsecond := integrable_carlemanSecondSchurMajorant g hgcont hg2
  have hC := integrable_carlemanAbsBilinearDensity
    f g hfcont hgcont hf2 hg2
  have hM : Integrable M (μ.prod μ) := by
    dsimp only [M]
    exact (hfirst.add hsecond).const_mul (1 / 2 : ℝ)
  have hpq : ∀ᵐ z ∂μ.prod μ, z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  have hpoint : ∀ᵐ z ∂μ.prod μ,
      carlemanAbsBilinearDensity f g z ≤ M z := by
    filter_upwards [hpq] with z hz
    have h := two_mul_carlemanAbsBilinearDensity_le_majorants
      f g z.1 z.2 hz.1 hz.2
    dsimp only [M]
    linarith
  have hmono :
      (∫ z : ℝ × ℝ, carlemanAbsBilinearDensity f g z ∂μ.prod μ) ≤
        ∫ z : ℝ × ℝ, M z ∂μ.prod μ :=
    integral_mono_ae hC hM hpoint
  calc
    (∫ z : ℝ × ℝ, carlemanAbsBilinearDensity f g z ∂μ.prod μ) ≤
        ∫ z : ℝ × ℝ, M z ∂μ.prod μ := hmono
    _ = (1 / 2 : ℝ) *
        ((∫ z : ℝ × ℝ, carlemanFirstSchurMajorant f z ∂μ.prod μ) +
          ∫ z : ℝ × ℝ,
            carlemanSecondSchurMajorant g z ∂μ.prod μ) := by
      dsimp only [M]
      rw [MeasureTheory.integral_const_mul, integral_add hfirst hsecond]
    _ = (Real.pi / 2) *
        ((∫ p : ℝ in Ioi 0, f p ^ 2) +
          (∫ q : ℝ in Ioi 0, g q ^ 2)) := by
      rw [show (∫ z : ℝ × ℝ,
          carlemanFirstSchurMajorant f z ∂μ.prod μ) =
          Real.pi * (∫ p : ℝ in Ioi 0, f p ^ 2) by
            simpa only [μ] using
              integral_carlemanFirstSchurMajorant f hfcont hf2,
        show (∫ z : ℝ × ℝ,
          carlemanSecondSchurMajorant g z ∂μ.prod μ) =
          Real.pi * (∫ q : ℝ in Ioi 0, g q ^ 2) by
            simpa only [μ] using
              integral_carlemanSecondSchurMajorant g hgcont hg2]
      ring

end

end ArithmeticHodge.Analysis.EndpointCarleman
