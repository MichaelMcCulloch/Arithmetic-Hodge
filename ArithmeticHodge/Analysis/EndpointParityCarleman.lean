import ArithmeticHodge.Analysis.EndpointCarleman
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.EndpointParityCarleman

noncomputable section

open EndpointCarleman

/-!
# Parity-folded endpoint Carleman estimate

After reflection parity folds the endpoint correlation triangle onto the
positive unit square, its two scalar branches have kernel

`1 / (p + q) + 1 / (2 - |p - q|)`.

The second denominator is bounded below by `1 + p * q`.  The resulting two
Schur rows are complementary pieces of the positive-half-line Carleman row,
so their sum is exactly `π` rather than `2 * π`.
-/

/-- The exact scalar kernel obtained by folding the correlation triangle. -/
def parityFoldedTriangleKernel (p q : ℝ) : ℝ :=
  1 / (p + q) + 1 / (2 - |p - q|)

/-- The parity-compatible Carleman majorant on the unit square. -/
def parityUnitCarlemanKernel (p q : ℝ) : ℝ :=
  1 / (p + q) + 1 / (1 + p * q)

/-- The elementary denominator inequality behind the folded-kernel
domination. -/
theorem one_add_mul_le_two_sub_abs_sub
    {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    1 + p * q ≤ 2 - |p - q| := by
  rcases le_total p q with hpq | hqp
  · rw [abs_of_nonpos (sub_nonpos.mpr hpq)]
    have hprod : 0 ≤ (1 - q) * (1 + p) :=
      mul_nonneg (sub_nonneg.mpr hq1) (by linarith)
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hqp)]
    have hprod : 0 ≤ (1 - p) * (1 + q) :=
      mul_nonneg (sub_nonneg.mpr hp1) (by linarith)
    nlinarith

/-- On the closed unit square, the exact parity-folded triangle kernel is
pointwise dominated by the two-piece Carleman kernel. -/
theorem parityFoldedTriangleKernel_le_parityUnitCarlemanKernel
    {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    parityFoldedTriangleKernel p q ≤ parityUnitCarlemanKernel p q := by
  have hden := one_add_mul_le_two_sub_abs_sub hp0 hp1 hq0 hq1
  have hleft : 0 < 1 + p * q := by positivity
  have hright : 0 < 2 - |p - q| := hleft.trans_le hden
  unfold parityFoldedTriangleKernel parityUnitCarlemanKernel
  gcongr

/-- The lower-half-line piece of the weighted Carleman row. -/
theorem integral_zero_one_first_parity_schur_piece
    (p : ℝ) (hp : 0 < p) :
    (∫ q : ℝ in 0..1,
      (Real.sqrt p / Real.sqrt q) / (p + q)) =
      2 * Real.arctan (Real.sqrt p)⁻¹ := by
  let c : ℝ := Real.sqrt p
  let k : ℝ → ℝ := fun q ↦ (c / Real.sqrt q) / (p + q)
  have hc : 0 < c := Real.sqrt_pos.2 hp
  have hcsq : c ^ 2 = p := Real.sq_sqrt hp.le
  have hsubst := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := 1)
    (f := fun x : ℝ ↦ x ^ 2) (f' := fun x : ℝ ↦ 2 * x)
    (g := k)
    (by fun_prop)
    (by
      intro x _hx
      convert (hasDerivAt_pow 2 x) using 1
      all_goals ring)
    (by
      intro x hx
      norm_num at hx
      exact (mul_nonneg (by norm_num) hx.1.le))
  have hleft :
      (∫ x : ℝ in 0..1,
        (k ∘ fun y : ℝ ↦ y ^ 2) x * (2 * x)) =
      ∫ x : ℝ in 0..1, 2 * c / (c ^ 2 + x ^ 2) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [show ∀ᵐ x : ℝ ∂volume, x ≠ 0 by
      simp [ae_iff, measure_singleton]] with x hx0
    intro hxmem
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hxmem
    have hx : 0 < x := hxmem.1
    dsimp only [Function.comp_apply, k]
    have hsqrt : Real.sqrt (x ^ 2) = |x| := Real.sqrt_sq_eq_abs x
    rw [hsqrt, abs_of_pos hx]
    field_simp [hx.ne', hc.ne']
    nlinarith [hcsq]
  have hrational :
      (∫ x : ℝ in 0..1, 2 * c / (c ^ 2 + x ^ 2)) =
        2 * Real.arctan c⁻¹ := by
    calc
      (∫ x : ℝ in 0..1, 2 * c / (c ^ 2 + x ^ 2)) =
          2 * ∫ x : ℝ in 0..1, c / (c ^ 2 + x ^ 2) := by
        rw [show (fun x : ℝ ↦ 2 * c / (c ^ 2 + x ^ 2)) =
            fun x : ℝ ↦ 2 * (c / (c ^ 2 + x ^ 2)) by
          funext x
          ring,
          intervalIntegral.integral_const_mul]
      _ = 2 * (Real.arctan (1 / c) - Real.arctan (0 / c)) := by
        rw [integral_div_sq_add_sq]
      _ = 2 * Real.arctan c⁻¹ := by simp [one_div]
  have hsubst' :
      (∫ x : ℝ in 0..1,
        (k ∘ fun y : ℝ ↦ y ^ 2) x * (2 * x)) =
      ∫ q : ℝ in 0..1, k q := by
    norm_num [pow_two] at hsubst
    simpa only [Function.comp_apply, pow_two] using hsubst
  change (∫ q : ℝ in 0..1, k q) = _
  rw [← hsubst', hleft, hrational]

/-- The reciprocal-tail piece of the weighted Carleman row. -/
theorem integral_zero_one_second_parity_schur_piece
    (p : ℝ) (hp : 0 < p) :
    (∫ q : ℝ in 0..1,
      (Real.sqrt p / Real.sqrt q) / (1 + p * q)) =
      2 * Real.arctan (Real.sqrt p) := by
  let c : ℝ := Real.sqrt p
  let k : ℝ → ℝ := fun q ↦ (c / Real.sqrt q) / (1 + p * q)
  have hc : 0 < c := Real.sqrt_pos.2 hp
  have hcsq : c ^ 2 = p := Real.sq_sqrt hp.le
  have hsubst := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := 1)
    (f := fun x : ℝ ↦ x ^ 2) (f' := fun x : ℝ ↦ 2 * x)
    (g := k)
    (by fun_prop)
    (by
      intro x _hx
      convert (hasDerivAt_pow 2 x) using 1
      all_goals ring)
    (by
      intro x hx
      norm_num at hx
      exact (mul_nonneg (by norm_num) hx.1.le))
  have hleft :
      (∫ x : ℝ in 0..1,
        (k ∘ fun y : ℝ ↦ y ^ 2) x * (2 * x)) =
      ∫ x : ℝ in 0..1, 2 * c / (1 + c ^ 2 * x ^ 2) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [show ∀ᵐ x : ℝ ∂volume, x ≠ 0 by
      simp [ae_iff, measure_singleton]] with x hx0
    intro hxmem
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hxmem
    have hx : 0 < x := hxmem.1
    dsimp only [Function.comp_apply, k]
    have hsqrt : Real.sqrt (x ^ 2) = |x| := Real.sqrt_sq_eq_abs x
    rw [hsqrt, abs_of_pos hx]
    field_simp [hx.ne']
    nlinarith [hcsq]
  have hscale := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := 1)
    (f := fun x : ℝ ↦ c * x) (f' := fun _x : ℝ ↦ c)
    (g := fun y : ℝ ↦ (1 + y ^ 2)⁻¹)
    (by
      intro x _hx
      convert (hasDerivAt_id x).const_mul c using 1
      all_goals ring)
    (by fun_prop)
    (by
      have hcont : Continuous (fun x : ℝ ↦ (1 : ℝ) + x ^ 2) := by
        fun_prop
      exact hcont.inv₀ (fun x hx ↦ by nlinarith [sq_nonneg x]))
  have hrational :
      (∫ x : ℝ in 0..1, 2 * c / (1 + c ^ 2 * x ^ 2)) =
        2 * Real.arctan c := by
    calc
      (∫ x : ℝ in 0..1, 2 * c / (1 + c ^ 2 * x ^ 2)) =
          2 * ∫ x : ℝ in 0..1, (1 + (c * x) ^ 2)⁻¹ * c := by
        rw [show (fun x : ℝ ↦ 2 * c / (1 + c ^ 2 * x ^ 2)) =
            fun x : ℝ ↦ 2 * ((1 + (c * x) ^ 2)⁻¹ * c) by
          funext x
          field_simp,
          intervalIntegral.integral_const_mul]
      _ = 2 * ∫ y : ℝ in c * 0..c * 1, (1 + y ^ 2)⁻¹ := by
        exact congrArg (fun z : ℝ ↦ 2 * z)
          (by simpa only [Function.comp_apply] using hscale)
      _ = 2 * Real.arctan c := by simp
  have hsubst' :
      (∫ x : ℝ in 0..1,
        (k ∘ fun y : ℝ ↦ y ^ 2) x * (2 * x)) =
      ∫ q : ℝ in 0..1, k q := by
    norm_num [pow_two] at hsubst
    simpa only [Function.comp_apply, pow_two] using hsubst
  change (∫ q : ℝ in 0..1, k q) = _
  rw [← hsubst', hleft, hrational]

/-- The two unit-square pieces form exactly one full Carleman Schur row. -/
theorem integral_zero_one_parity_schur_row
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∫ q : ℝ in 0..1,
      (Real.sqrt p / Real.sqrt q) * parityUnitCarlemanKernel p q) =
      Real.pi := by
  have hfirst : IntervalIntegrable
      (fun q : ℝ ↦ (Real.sqrt p / Real.sqrt q) / (p + q))
      volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2
      ((integrableOn_Ioi_carleman_schur_weight p hp).mono_set
        Ioc_subset_Ioi_self)
  have hsecond : IntervalIntegrable
      (fun q : ℝ ↦ (Real.sqrt p / Real.sqrt q) / (1 + p * q))
      volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    have hdom : IntegrableOn
        (fun q : ℝ ↦ (Real.sqrt p / Real.sqrt q) / (p + q))
        (Ioc 0 1) :=
      (integrableOn_Ioi_carleman_schur_weight p hp).mono_set
        (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self)
    apply hdom.mono'
    · exact (by fun_prop : Measurable (fun q : ℝ ↦
          (Real.sqrt p / Real.sqrt q) / (1 + p * q))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
      have hq0 : 0 < q := hq.1
      have hq1 : q ≤ 1 := hq.2
      have hden : p + q ≤ 1 + p * q := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1)]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  rw [show (fun q : ℝ ↦
      (Real.sqrt p / Real.sqrt q) * parityUnitCarlemanKernel p q) =
      fun q : ℝ ↦
        (Real.sqrt p / Real.sqrt q) / (p + q) +
          (Real.sqrt p / Real.sqrt q) / (1 + p * q) by
    funext q
    unfold parityUnitCarlemanKernel
    ring]
  rw [intervalIntegral.integral_add hfirst hsecond]
  rw [integral_zero_one_first_parity_schur_piece p hp,
    integral_zero_one_second_parity_schur_piece p hp]
  have hc : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  rw [Real.arctan_inv_of_pos hc]
  ring

/-- Integrability accompanying the exact parity Schur row. -/
theorem integrableOn_Ioc_parity_schur_row
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    IntegrableOn
      (fun q : ℝ ↦
        (Real.sqrt p / Real.sqrt q) * parityUnitCarlemanKernel p q)
      (Ioc 0 1) := by
  have hfirst : IntegrableOn
      (fun q : ℝ ↦ (Real.sqrt p / Real.sqrt q) / (p + q))
      (Ioc 0 1) :=
    (integrableOn_Ioi_carleman_schur_weight p hp).mono_set
      (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self)
  have hsecond : IntegrableOn
      (fun q : ℝ ↦ (Real.sqrt p / Real.sqrt q) / (1 + p * q))
      (Ioc 0 1) := by
    apply hfirst.mono'
    · exact (by fun_prop : Measurable (fun q : ℝ ↦
          (Real.sqrt p / Real.sqrt q) / (1 + p * q))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
      have hq0 : 0 < q := hq.1
      have hq1 : q ≤ 1 := hq.2
      have hden : p + q ≤ 1 + p * q := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1)]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  apply (hfirst.add hsecond).congr_fun
  · intro q _hq
    unfold parityUnitCarlemanKernel
    simp only [Pi.add_apply]
    ring
  · exact measurableSet_Ioc

/-- The parity unit kernel is symmetric. -/
theorem parityUnitCarlemanKernel_comm (p q : ℝ) :
    parityUnitCarlemanKernel p q = parityUnitCarlemanKernel q p := by
  unfold parityUnitCarlemanKernel
  rw [add_comm p q, mul_comm p q]

/-- The exact folded triangle kernel is symmetric. -/
theorem parityFoldedTriangleKernel_comm (p q : ℝ) :
    parityFoldedTriangleKernel p q = parityFoldedTriangleKernel q p := by
  unfold parityFoldedTriangleKernel
  rw [add_comm p q, abs_sub_comm]

/-- First weighted square in the parity-unit Schur decomposition. -/
def parityFirstSchurMajorant
    (f : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  f z.1 ^ 2 *
    ((Real.sqrt z.1 / Real.sqrt z.2) *
      parityUnitCarlemanKernel z.1 z.2)

/-- Second weighted square in the parity-unit Schur decomposition. -/
def paritySecondSchurMajorant
    (g : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  g z.2 ^ 2 *
    ((Real.sqrt z.2 / Real.sqrt z.1) *
      parityUnitCarlemanKernel z.1 z.2)

/-- Absolute bilinear density for the parity-unit Carleman majorant. -/
def parityUnitAbsBilinearDensity
    (f g : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  |f z.1 * g z.2| * parityUnitCarlemanKernel z.1 z.2

/-- Absolute bilinear density for the exact parity-folded triangle kernel. -/
def parityFoldedTriangleAbsBilinearDensity
    (f g : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  |f z.1 * g z.2| * parityFoldedTriangleKernel z.1 z.2

theorem paritySecondSchurMajorant_eq_first_swap
    (g : ℝ → ℝ) (z : ℝ × ℝ) :
    paritySecondSchurMajorant g z =
      parityFirstSchurMajorant g z.swap := by
  rcases z with ⟨p, q⟩
  unfold paritySecondSchurMajorant parityFirstSchurMajorant
  simp only [Prod.swap_prod_mk]
  rw [parityUnitCarlemanKernel_comm]

/-- The first parity Schur majorant is integrable on the positive unit
square for continuous data. -/
theorem integrable_parityFirstSchurMajorant
    (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable (parityFirstSchurMajorant f)
      ((volume.restrict (Ioc 0 1)).prod
        (volume.restrict (Ioc 0 1))) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  have hmeas : Measurable (parityFirstSchurMajorant f) := by
    unfold parityFirstSchurMajorant parityUnitCarlemanKernel
    fun_prop
  have hinner : ∀ᵐ p ∂μ,
      Integrable (fun q : ℝ ↦ parityFirstSchurMajorant f (p, q)) μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with p hp
    have hrow := integrableOn_Ioc_parity_schur_row p hp.1 hp.2
    simpa only [μ, parityFirstSchurMajorant] using
      hrow.const_mul (f p ^ 2)
  have hinnerNorm : ∀ᵐ p ∂μ,
      (∫ q : ℝ, ‖parityFirstSchurMajorant f (p, q)‖ ∂μ) =
        Real.pi * f p ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with p hp
    calc
      (∫ q : ℝ, ‖parityFirstSchurMajorant f (p, q)‖ ∂μ) =
          ∫ q : ℝ,
            f p ^ 2 *
              ((Real.sqrt p / Real.sqrt q) *
                parityUnitCarlemanKernel p q) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
        change |f p ^ 2 *
          ((Real.sqrt p / Real.sqrt q) *
            parityUnitCarlemanKernel p q)| = _
        rw [abs_of_nonneg]
        exact mul_nonneg (sq_nonneg _) <| mul_nonneg
          (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) <| by
            unfold parityUnitCarlemanKernel
            exact add_nonneg
              (one_div_nonneg.mpr (add_pos hp.1 hq.1).le)
              (one_div_nonneg.mpr (by
                nlinarith [mul_nonneg hp.1.le hq.1.le]))
      _ = f p ^ 2 *
          (∫ q : ℝ in Ioc 0 1,
            (Real.sqrt p / Real.sqrt q) *
              parityUnitCarlemanKernel p q) := by
        simp only [μ, MeasureTheory.integral_const_mul]
      _ = Real.pi * f p ^ 2 := by
        have hrow := integral_zero_one_parity_schur_row p hp.1 hp.2
        rw [intervalIntegral.integral_of_le (by norm_num)] at hrow
        rw [hrow]
        ring
  have houter : Integrable
      (fun p : ℝ ↦
        ∫ q : ℝ, ‖parityFirstSchurMajorant f (p, q)‖ ∂μ) μ := by
    have hsq : IntegrableOn (fun p : ℝ ↦ f p ^ 2) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1
        ((hf.pow 2).intervalIntegrable 0 1)
    have hpi : Integrable (fun p : ℝ ↦ Real.pi * f p ^ 2) μ := by
      simpa only [μ] using hsq.const_mul Real.pi
    apply hpi.congr
    filter_upwards [hinnerNorm] with p hp
    exact hp.symm
  change Integrable (parityFirstSchurMajorant f) (μ.prod μ)
  exact (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    ⟨hinner, houter⟩

/-- Exact integral of the first parity Schur majorant. -/
theorem integral_parityFirstSchurMajorant
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z : ℝ × ℝ, parityFirstSchurMajorant f z
      ∂((volume.restrict (Ioc 0 1)).prod
        (volume.restrict (Ioc 0 1)))) =
      Real.pi * (∫ p : ℝ in 0..1, f p ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  have hmajorant := integrable_parityFirstSchurMajorant f hf
  change (∫ z : ℝ × ℝ, parityFirstSchurMajorant f z ∂μ.prod μ) = _
  rw [integral_prod _ hmajorant]
  calc
    (∫ p : ℝ,
        ∫ q : ℝ, parityFirstSchurMajorant f (p, q) ∂μ ∂μ) =
        ∫ p : ℝ, Real.pi * f p ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with p hp
      change (∫ q : ℝ,
        f p ^ 2 *
          ((Real.sqrt p / Real.sqrt q) *
            parityUnitCarlemanKernel p q) ∂μ) = _
      rw [MeasureTheory.integral_const_mul]
      change f p ^ 2 *
        (∫ q : ℝ in Ioc 0 1,
          (Real.sqrt p / Real.sqrt q) *
            parityUnitCarlemanKernel p q) = _
      have hrow := integral_zero_one_parity_schur_row p hp.1 hp.2
      rw [intervalIntegral.integral_of_le (by norm_num)] at hrow
      rw [hrow]
      ring
    _ = Real.pi * (∫ p : ℝ in 0..1, f p ^ 2) := by
      rw [show (∫ p : ℝ, Real.pi * f p ^ 2 ∂μ) =
          Real.pi * ∫ p : ℝ, f p ^ 2 ∂μ by
        exact MeasureTheory.integral_const_mul Real.pi (fun p : ℝ ↦ f p ^ 2)]
      rw [intervalIntegral.integral_of_le (by norm_num)]

/-- The second parity Schur majorant is the swapped first majorant. -/
theorem integrable_paritySecondSchurMajorant
    (g : ℝ → ℝ) (hg : Continuous g) :
    Integrable (paritySecondSchurMajorant g)
      ((volume.restrict (Ioc 0 1)).prod
        (volume.restrict (Ioc 0 1))) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  have hfirst := integrable_parityFirstSchurMajorant g hg
  have hswap := hfirst.swap
  change Integrable (paritySecondSchurMajorant g) (μ.prod μ)
  apply hswap.congr
  filter_upwards [] with z
  exact (paritySecondSchurMajorant_eq_first_swap g z).symm

/-- Exact integral of the second parity Schur majorant. -/
theorem integral_paritySecondSchurMajorant
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ z : ℝ × ℝ, paritySecondSchurMajorant g z
      ∂((volume.restrict (Ioc 0 1)).prod
        (volume.restrict (Ioc 0 1)))) =
      Real.pi * (∫ q : ℝ in 0..1, g q ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  have hfirstIntegral := integral_parityFirstSchurMajorant g hg
  calc
    (∫ z : ℝ × ℝ, paritySecondSchurMajorant g z ∂μ.prod μ) =
        ∫ z : ℝ × ℝ,
          parityFirstSchurMajorant g z.swap ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact paritySecondSchurMajorant_eq_first_swap g z
    _ = ∫ z : ℝ × ℝ,
          parityFirstSchurMajorant g z ∂μ.prod μ := by
      exact integral_prod_swap (parityFirstSchurMajorant g)
    _ = Real.pi * (∫ q : ℝ in 0..1, g q ^ 2) := by
      simpa only [μ] using hfirstIntegral

/-- Pointwise Schur domination of the parity-unit absolute bilinear
density. -/
theorem two_mul_parityUnitAbsBilinearDensity_le_majorants
    (f g : ℝ → ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    2 * parityUnitAbsBilinearDensity f g (p, q) ≤
      parityFirstSchurMajorant f (p, q) +
        paritySecondSchurMajorant g (p, q) := by
  have hsqrtp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hweighted := two_mul_abs_mul_le_weighted_sq
    (f p) (g q) (Real.sqrt p / Real.sqrt q)
      (div_pos hsqrtp hsqrtq)
  have hrewrite :
      g q ^ 2 / (Real.sqrt p / Real.sqrt q) =
        (Real.sqrt q / Real.sqrt p) * g q ^ 2 := by
    field_simp [hsqrtp.ne', hsqrtq.ne']
  rw [hrewrite] at hweighted
  have hkernel : 0 ≤ parityUnitCarlemanKernel p q := by
    unfold parityUnitCarlemanKernel
    exact add_nonneg
      (one_div_nonneg.mpr (add_pos hp hq).le)
      (one_div_nonneg.mpr (by
        nlinarith [mul_nonneg hp.le hq.le]))
  have hscaled := mul_le_mul_of_nonneg_right hweighted hkernel
  unfold parityUnitAbsBilinearDensity parityFirstSchurMajorant
    paritySecondSchurMajorant
  nlinarith

/-- The parity-unit absolute bilinear density is integrable for continuous
unit-interval data. -/
theorem integrable_parityUnitAbsBilinearDensity
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Integrable (parityUnitAbsBilinearDensity f g)
      ((volume.restrict (Ioc 0 1)).prod
        (volume.restrict (Ioc 0 1))) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  let M : ℝ × ℝ → ℝ := fun z ↦
    (1 / 2 : ℝ) *
      (parityFirstSchurMajorant f z + paritySecondSchurMajorant g z)
  have hfirst := integrable_parityFirstSchurMajorant f hf
  have hsecond := integrable_paritySecondSchurMajorant g hg
  have hM : Integrable M (μ.prod μ) := by
    dsimp only [M]
    exact (hfirst.add hsecond).const_mul (1 / 2 : ℝ)
  have hmeas : Measurable (parityUnitAbsBilinearDensity f g) := by
    unfold parityUnitAbsBilinearDensity parityUnitCarlemanKernel
    fun_prop
  have hpq : ∀ᵐ z ∂μ.prod μ, z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  change Integrable (parityUnitAbsBilinearDensity f g) (μ.prod μ)
  apply hM.mono' hmeas.aestronglyMeasurable
  filter_upwards [hpq] with z hz
  have hD0 : 0 ≤ parityUnitAbsBilinearDensity f g z := by
    unfold parityUnitAbsBilinearDensity parityUnitCarlemanKernel
    exact mul_nonneg (abs_nonneg _) <| add_nonneg
      (one_div_nonneg.mpr (add_pos hz.1.1 hz.2.1).le)
      (one_div_nonneg.mpr (by
        nlinarith [mul_nonneg hz.1.1.le hz.2.1.le]))
  rw [Real.norm_eq_abs, abs_of_nonneg hD0]
  dsimp only [M]
  have hpoint := two_mul_parityUnitAbsBilinearDensity_le_majorants
    f g z.1 z.2 hz.1.1 hz.2.1
  nlinarith

/-- Product-measure Schur bound for the parity-unit kernel. -/
theorem integral_parityUnitAbsBilinearDensity_le
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ z : ℝ × ℝ, parityUnitAbsBilinearDensity f g z
      ∂((volume.restrict (Ioc 0 1)).prod
        (volume.restrict (Ioc 0 1)))) ≤
      (Real.pi / 2) *
        ((∫ p : ℝ in 0..1, f p ^ 2) +
          (∫ q : ℝ in 0..1, g q ^ 2)) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  let M : ℝ × ℝ → ℝ := fun z ↦
    (1 / 2 : ℝ) *
      (parityFirstSchurMajorant f z + paritySecondSchurMajorant g z)
  have hfirst := integrable_parityFirstSchurMajorant f hf
  have hsecond := integrable_paritySecondSchurMajorant g hg
  have hD := integrable_parityUnitAbsBilinearDensity f g hf hg
  have hM : Integrable M (μ.prod μ) := by
    dsimp only [M]
    exact (hfirst.add hsecond).const_mul (1 / 2 : ℝ)
  have hpq : ∀ᵐ z ∂μ.prod μ, z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hpoint : ∀ᵐ z ∂μ.prod μ,
      parityUnitAbsBilinearDensity f g z ≤ M z := by
    filter_upwards [hpq] with z hz
    have h := two_mul_parityUnitAbsBilinearDensity_le_majorants
      f g z.1 z.2 hz.1.1 hz.2.1
    dsimp only [M]
    linarith
  have hmono :
      (∫ z : ℝ × ℝ, parityUnitAbsBilinearDensity f g z ∂μ.prod μ) ≤
        ∫ z : ℝ × ℝ, M z ∂μ.prod μ :=
    integral_mono_ae hD hM hpoint
  calc
    (∫ z : ℝ × ℝ, parityUnitAbsBilinearDensity f g z ∂μ.prod μ) ≤
        ∫ z : ℝ × ℝ, M z ∂μ.prod μ := hmono
    _ = (1 / 2 : ℝ) *
        ((∫ z : ℝ × ℝ, parityFirstSchurMajorant f z ∂μ.prod μ) +
          ∫ z : ℝ × ℝ, paritySecondSchurMajorant g z ∂μ.prod μ) := by
      dsimp only [M]
      rw [MeasureTheory.integral_const_mul, integral_add hfirst hsecond]
    _ = (Real.pi / 2) *
        ((∫ p : ℝ in 0..1, f p ^ 2) +
          (∫ q : ℝ in 0..1, g q ^ 2)) := by
      rw [show (∫ z : ℝ × ℝ,
          parityFirstSchurMajorant f z ∂μ.prod μ) =
          Real.pi * (∫ p : ℝ in 0..1, f p ^ 2) by
            simpa only [μ] using integral_parityFirstSchurMajorant f hf,
        show (∫ z : ℝ × ℝ,
          paritySecondSchurMajorant g z ∂μ.prod μ) =
          Real.pi * (∫ q : ℝ in 0..1, g q ^ 2) by
            simpa only [μ] using integral_paritySecondSchurMajorant g hg]
      ring

/-- The exact folded-triangle density is integrable on the unit square.
This is the Fubini boundary needed when transporting the original endpoint
correlation triangle. -/
theorem integrable_parityFoldedTriangleAbsBilinearDensity
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Integrable (parityFoldedTriangleAbsBilinearDensity f g)
      ((volume.restrict (Ioc 0 1)).prod
        (volume.restrict (Ioc 0 1))) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  have hunit := integrable_parityUnitAbsBilinearDensity f g hf hg
  have hmeas : Measurable
      (parityFoldedTriangleAbsBilinearDensity f g) := by
    unfold parityFoldedTriangleAbsBilinearDensity parityFoldedTriangleKernel
    fun_prop
  have hpq : ∀ᵐ z ∂μ.prod μ, z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  change Integrable (parityFoldedTriangleAbsBilinearDensity f g) (μ.prod μ)
  apply hunit.mono' hmeas.aestronglyMeasurable
  filter_upwards [hpq] with z hz
  have hfold0 : 0 ≤ parityFoldedTriangleKernel z.1 z.2 := by
    unfold parityFoldedTriangleKernel
    have hdiff : |z.1 - z.2| < 2 := by
      rw [abs_lt]
      constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
    exact add_nonneg
      (one_div_nonneg.mpr (add_pos hz.1.1 hz.2.1).le)
      (one_div_nonneg.mpr (by linarith))
  have hunit0 : 0 ≤ parityUnitCarlemanKernel z.1 z.2 := by
    unfold parityUnitCarlemanKernel
    exact add_nonneg
      (one_div_nonneg.mpr (add_pos hz.1.1 hz.2.1).le)
      (one_div_nonneg.mpr (by
        nlinarith [mul_nonneg hz.1.1.le hz.2.1.le]))
  unfold parityFoldedTriangleAbsBilinearDensity
    parityUnitAbsBilinearDensity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hfold0)]
  exact mul_le_mul_of_nonneg_left
    (parityFoldedTriangleKernel_le_parityUnitCarlemanKernel
      hz.1.1.le hz.1.2 hz.2.1.le hz.2.2)
    (abs_nonneg _)

/-- Additive Schur bound for the exact folded-triangle kernel. -/
theorem integral_parityFoldedTriangleAbsBilinearDensity_le
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ z : ℝ × ℝ, parityFoldedTriangleAbsBilinearDensity f g z
      ∂((volume.restrict (Ioc 0 1)).prod
        (volume.restrict (Ioc 0 1)))) ≤
      (Real.pi / 2) *
        ((∫ p : ℝ in 0..1, f p ^ 2) +
          (∫ q : ℝ in 0..1, g q ^ 2)) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  have hfold := integrable_parityFoldedTriangleAbsBilinearDensity
    f g hf hg
  have hunit := integrable_parityUnitAbsBilinearDensity f g hf hg
  have hpq : ∀ᵐ z ∂μ.prod μ, z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hpoint : ∀ᵐ z ∂μ.prod μ,
      parityFoldedTriangleAbsBilinearDensity f g z ≤
        parityUnitAbsBilinearDensity f g z := by
    filter_upwards [hpq] with z hz
    unfold parityFoldedTriangleAbsBilinearDensity
      parityUnitAbsBilinearDensity
    exact mul_le_mul_of_nonneg_left
      (parityFoldedTriangleKernel_le_parityUnitCarlemanKernel
        hz.1.1.le hz.1.2 hz.2.1.le hz.2.2)
      (abs_nonneg _)
  exact (integral_mono_ae hfold hunit hpoint).trans
    (integral_parityUnitAbsBilinearDensity_le f g hf hg)

/-- Geometric-mean product-measure bound for the exact folded-triangle
kernel.  This is the sharp form of the parity gain: each half-profile pays
only its own half-energy. -/
theorem integral_parityFoldedTriangleAbsBilinearDensity_le_pi_mul_sqrt_energy
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ z : ℝ × ℝ, parityFoldedTriangleAbsBilinearDensity f g z
      ∂((volume.restrict (Ioc 0 1)).prod
        (volume.restrict (Ioc 0 1)))) ≤
      Real.pi * Real.sqrt
        ((∫ p : ℝ in 0..1, f p ^ 2) *
          (∫ q : ℝ in 0..1, g q ^ 2)) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  let Ef : ℝ := ∫ p : ℝ in 0..1, f p ^ 2
  let Eg : ℝ := ∫ q : ℝ in 0..1, g q ^ 2
  let I : ℝ := ∫ z : ℝ × ℝ,
    parityFoldedTriangleAbsBilinearDensity f g z ∂μ.prod μ
  have hEf : 0 ≤ Ef := by
    dsimp only [Ef]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun p _hp ↦ sq_nonneg (f p))
  have hEg : 0 ≤ Eg := by
    dsimp only [Eg]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun q _hq ↦ sq_nonneg (g q))
  by_cases hEf0 : Ef = 0
  · have hfi : IntervalIntegrable (fun p : ℝ ↦ f p ^ 2) volume 0 1 :=
      (hf.pow 2).intervalIntegrable 0 1
    have hsqAe : (fun p : ℝ ↦ f p ^ 2) =ᵐ[μ] 0 := by
      dsimp only [μ]
      exact (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
        (by norm_num)
        (Filter.Eventually.of_forall (fun p ↦ sq_nonneg (f p))) hfi).1 hEf0
    have hsqOn : Set.EqOn (fun p : ℝ ↦ f p ^ 2) 0 (Ioc 0 1) :=
      Measure.eqOn_Ioc_of_ae_eq volume hsqAe
        (hf.pow 2).continuousOn continuousOn_const
    have hpq : ∀ᵐ z ∂μ.prod μ,
        z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
      dsimp only [μ]
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    have hzero :
        parityFoldedTriangleAbsBilinearDensity f g =ᵐ[μ.prod μ] 0 := by
      filter_upwards [hpq] with z hz
      have hfz : f z.1 = 0 := (sq_eq_zero_iff).mp (hsqOn hz.1)
      unfold parityFoldedTriangleAbsBilinearDensity
      simp [hfz]
    have hI0 : I = 0 := by
      dsimp only [I]
      exact integral_eq_zero_of_ae hzero
    change I ≤ Real.pi * Real.sqrt (Ef * Eg)
    rw [hI0, hEf0, zero_mul, Real.sqrt_zero, mul_zero]
  · have hEfPos : 0 < Ef := lt_of_le_of_ne hEf (Ne.symm hEf0)
    by_cases hEg0 : Eg = 0
    · have hgi : IntervalIntegrable (fun q : ℝ ↦ g q ^ 2) volume 0 1 :=
        (hg.pow 2).intervalIntegrable 0 1
      have hsqAe : (fun q : ℝ ↦ g q ^ 2) =ᵐ[μ] 0 := by
        dsimp only [μ]
        exact (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
          (by norm_num)
          (Filter.Eventually.of_forall (fun q ↦ sq_nonneg (g q))) hgi).1 hEg0
      have hsqOn : Set.EqOn (fun q : ℝ ↦ g q ^ 2) 0 (Ioc 0 1) :=
        Measure.eqOn_Ioc_of_ae_eq volume hsqAe
          (hg.pow 2).continuousOn continuousOn_const
      have hpq : ∀ᵐ z ∂μ.prod μ,
          z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
        dsimp only [μ]
        rw [Measure.prod_restrict]
        exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
      have hzero :
          parityFoldedTriangleAbsBilinearDensity f g =ᵐ[μ.prod μ] 0 := by
        filter_upwards [hpq] with z hz
        have hgz : g z.2 = 0 := (sq_eq_zero_iff).mp (hsqOn hz.2)
        unfold parityFoldedTriangleAbsBilinearDensity
        simp [hgz]
      have hI0 : I = 0 := by
        dsimp only [I]
        exact integral_eq_zero_of_ae hzero
      change I ≤ Real.pi * Real.sqrt (Ef * Eg)
      rw [hI0, hEg0, mul_zero, Real.sqrt_zero, mul_zero]
    · have hEgPos : 0 < Eg := lt_of_le_of_ne hEg (Ne.symm hEg0)
      let sf : ℝ := Real.sqrt Eg
      let sg : ℝ := Real.sqrt Ef
      have hsf : 0 < sf := Real.sqrt_pos.2 hEgPos
      have hsg : 0 < sg := Real.sqrt_pos.2 hEfPos
      have hscaled := integral_parityFoldedTriangleAbsBilinearDensity_le
        (sf • f) (sg • g) (hf.const_smul sf) (hg.const_smul sg)
      have hscaledDensity :
          (∫ z : ℝ × ℝ,
              parityFoldedTriangleAbsBilinearDensity (sf • f) (sg • g) z
                ∂μ.prod μ) =
            (sf * sg) * I := by
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with z
        unfold parityFoldedTriangleAbsBilinearDensity
        simp only [Pi.smul_apply, smul_eq_mul, abs_mul,
          abs_of_pos hsf, abs_of_pos hsg]
        ring
      have hscaledEf :
          (∫ p : ℝ in 0..1, (sf • f) p ^ 2) = Eg * Ef := by
        calc
          (∫ p : ℝ in 0..1, (sf • f) p ^ 2) =
              sf ^ 2 * (∫ p : ℝ in 0..1, f p ^ 2) := by
            simp only [Pi.smul_apply, smul_eq_mul, mul_pow,
              intervalIntegral.integral_const_mul]
          _ = Eg * Ef := by
            rw [Real.sq_sqrt hEg]
      have hscaledEg :
          (∫ q : ℝ in 0..1, (sg • g) q ^ 2) = Ef * Eg := by
        calc
          (∫ q : ℝ in 0..1, (sg • g) q ^ 2) =
              sg ^ 2 * (∫ q : ℝ in 0..1, g q ^ 2) := by
            simp only [Pi.smul_apply, smul_eq_mul, mul_pow,
              intervalIntegral.integral_const_mul]
          _ = Ef * Eg := by
            rw [Real.sq_sqrt hEf]
      change I ≤ Real.pi * Real.sqrt (Ef * Eg)
      change (∫ z : ℝ × ℝ,
          parityFoldedTriangleAbsBilinearDensity (sf • f) (sg • g) z
            ∂μ.prod μ) ≤ _ at hscaled
      rw [hscaledDensity, hscaledEf, hscaledEg] at hscaled
      have hsqrtMul : sf * sg = Real.sqrt (Ef * Eg) := by
        dsimp only [sf, sg]
        calc
          Real.sqrt Eg * Real.sqrt Ef =
              Real.sqrt Ef * Real.sqrt Eg := mul_comm _ _
          _ = Real.sqrt (Ef * Eg) := (Real.sqrt_mul hEf _).symm
      have hsqrtPos : 0 < Real.sqrt (Ef * Eg) :=
        Real.sqrt_pos.2 (mul_pos hEfPos hEgPos)
      apply le_of_mul_le_mul_left
        (a := Real.sqrt (Ef * Eg))
        (b := I) (c := Real.pi * Real.sqrt (Ef * Eg))
      · calc
          Real.sqrt (Ef * Eg) * I = (sf * sg) * I := by rw [hsqrtMul]
          _ ≤ (Real.pi / 2) * (Eg * Ef + Ef * Eg) := hscaled
          _ = Real.pi * (Ef * Eg) := by ring
          _ = Real.pi * Real.sqrt (Ef * Eg) ^ 2 := by
            rw [Real.sq_sqrt (mul_nonneg hEf hEg)]
          _ = Real.sqrt (Ef * Eg) *
              (Real.pi * Real.sqrt (Ef * Eg)) := by ring
      · exact hsqrtPos

end

end ArithmeticHodge.Analysis.EndpointParityCarleman
