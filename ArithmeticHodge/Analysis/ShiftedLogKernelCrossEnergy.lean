import ArithmeticHodge.Analysis.ShiftedLogKernelRawPolynomial
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Polynomial

set_option autoImplicit false

open Finset Polynomial Set
open MeasureTheory
open scoped unitInterval

namespace ArithmeticHodge.Analysis.ShiftedLogKernelCrossEnergy

open ShiftedLegendreLogKernel
open ShiftedLogKernelRawPolynomial

noncomputable section

/-!
# Structural cross-energy control for the logarithmic kernel

The removable polynomial quotient is uniformly bounded on the unit square.
This is the domination input for pairing the singular logarithmic-difference
form with an arbitrary integrable function; no degree cutoff is involved.
-/

/-- A coefficientwise global bound for the removable quotient on `[0,1]^2`. -/
def polynomialDifferenceQuotientBound (p : ℝ[X]) : ℝ :=
  p.sum fun k a ↦ |a| * k

theorem polynomialDifferenceQuotientBound_nonneg (p : ℝ[X]) :
    0 ≤ polynomialDifferenceQuotientBound p := by
  rw [polynomialDifferenceQuotientBound, Polynomial.sum_def]
  exact Finset.sum_nonneg fun k _hk ↦
    mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

private theorem abs_monomialDifferenceQuotient_le
    (k : ℕ) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |monomialDifferenceQuotient k x y| ≤ k := by
  rw [monomialDifferenceQuotient]
  calc
    |∑ j ∈ Finset.range k, x ^ j * y ^ (k - 1 - j)| ≤
        ∑ j ∈ Finset.range k, |x ^ j * y ^ (k - 1 - j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [abs_mul, abs_of_nonneg (pow_nonneg hx.1 _),
        abs_of_nonneg (pow_nonneg hy.1 _)]
      exact mul_le_one₀ (pow_le_one₀ hx.1 hx.2)
        (pow_nonneg hy.1 _) (pow_le_one₀ hy.1 hy.2)
    _ = k := by simp

/-- The coefficientwise removable quotient is uniformly bounded on the whole
unit square. -/
theorem abs_polynomialDifferenceQuotient_le
    (p : ℝ[X]) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |polynomialDifferenceQuotient p x y| ≤
      polynomialDifferenceQuotientBound p := by
  rw [polynomialDifferenceQuotient, polynomialDifferenceQuotientBound,
    Polynomial.sum_def, Polynomial.sum_def]
  calc
    |∑ k ∈ p.support,
        p.coeff k * monomialDifferenceQuotient k x y| ≤
        ∑ k ∈ p.support,
          |p.coeff k * monomialDifferenceQuotient k x y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ p.support, |p.coeff k| * k := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_monomialDifferenceQuotient_le k hx hy) (abs_nonneg _)

/-- The original absolute-distance quotient inherits the same bound; the
diagonal value is harmless and both open half-squares are the two signs of
the removable quotient. -/
theorem abs_eval_sub_div_abs_le
    (p : ℝ[X]) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    abs ((p.eval x - p.eval y) / |x - y|) ≤
      polynomialDifferenceQuotientBound p := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · rw [← neg_polynomialDifferenceQuotient_eq_div_abs_of_lt p hxy,
      abs_neg]
    exact abs_polynomialDifferenceQuotient_le p hx hy
  · subst y
    simp only [sub_self, abs_zero, zero_div]
    exact polynomialDifferenceQuotientBound_nonneg p
  · rw [← polynomialDifferenceQuotient_eq_div_abs_of_lt p hyx]
    exact abs_polynomialDifferenceQuotient_le p hx hy

/-- The raw polynomial logarithmic kernel on the unit square. -/
def unitIntervalRawPolynomialLogKernel
    (p : ℝ[X]) (z : unitInterval × unitInterval) : ℝ :=
  (p.eval (z.1 : ℝ) - p.eval (z.2 : ℝ)) /
    |(z.1 : ℝ) - (z.2 : ℝ)|

theorem measurable_unitIntervalRawPolynomialLogKernel (p : ℝ[X]) :
    Measurable (unitIntervalRawPolynomialLogKernel p) := by
  unfold unitIntervalRawPolynomialLogKernel
  have hx : Measurable
      (fun z : unitInterval × unitInterval ↦ (z.1 : ℝ)) :=
    continuous_subtype_val.measurable.comp measurable_fst
  have hy : Measurable
      (fun z : unitInterval × unitInterval ↦ (z.2 : ℝ)) :=
    continuous_subtype_val.measurable.comp measurable_snd
  have hden : Measurable
      (fun z : unitInterval × unitInterval ↦
        |(z.1 : ℝ) - (z.2 : ℝ)|) := by
    simpa only [Real.norm_eq_abs] using (hx.sub hy).norm
  exact ((p.continuous.measurable.comp hx).sub
    (p.continuous.measurable.comp hy)).div hden

theorem norm_unitIntervalRawPolynomialLogKernel_le
    (p : ℝ[X]) (z : unitInterval × unitInterval) :
    ‖unitIntervalRawPolynomialLogKernel p z‖ ≤
      polynomialDifferenceQuotientBound p := by
  rw [Real.norm_eq_abs]
  exact abs_eval_sub_div_abs_le p z.1.property z.2.property

theorem unitIntervalRawPolynomialLogKernel_swap
    (p : ℝ[X]) (z : unitInterval × unitInterval) :
    unitIntervalRawPolynomialLogKernel p z.swap =
      -unitIntervalRawPolynomialLogKernel p z := by
  rcases z with ⟨x, y⟩
  unfold unitIntervalRawPolynomialLogKernel
  simp only [Prod.swap_prod_mk]
  rw [abs_sub_comm]
  ring

theorem integral_unitIntervalRawPolynomialLogKernel
    (p : ℝ[X]) (x : unitInterval) :
    (∫ y : unitInterval,
      unitIntervalRawPolynomialLogKernel p (x, y)) =
        (shiftedLogKernel p).eval (x : ℝ) := by
  change (∫ y : unitInterval,
      (p.eval (x : ℝ) - p.eval (y : ℝ)) /
        |(x : ℝ) - (y : ℝ)|) = _
  calc
    _ = ∫ y : ℝ in Set.Icc 0 1,
        (p.eval (x : ℝ) - p.eval y) /
          |(x : ℝ) - y| :=
      unitInterval.measurePreserving_coe.integral_comp
        unitInterval.measurableEmbedding_coe _
    _ = ∫ y : ℝ in 0..1,
        (p.eval (x : ℝ) - p.eval y) /
          |(x : ℝ) - y| := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ = _ := (eval_shiftedLogKernel_eq_integral_div_abs p x.property).symm

theorem integrable_fst_mul_unitIntervalRawPolynomialLogKernel
    (f : unitInterval → ℝ) (hf : Integrable f)
    (p : ℝ[X]) :
    Integrable (fun z : unitInterval × unitInterval ↦
      f z.1 * unitIntervalRawPolynomialLogKernel p z) := by
  have hone : Integrable (fun _ : unitInterval ↦ (1 : ℝ)) :=
    integrable_const 1
  have hfirst : Integrable (fun z : unitInterval × unitInterval ↦ f z.1) := by
    simpa using hf.mul_prod hone
  exact hfirst.mul_bdd
    (measurable_unitIntervalRawPolynomialLogKernel p).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (norm_unitIntervalRawPolynomialLogKernel_le p))

theorem integrable_snd_mul_unitIntervalRawPolynomialLogKernel
    (f : unitInterval → ℝ) (hf : Integrable f)
    (p : ℝ[X]) :
    Integrable (fun z : unitInterval × unitInterval ↦
      f z.2 * unitIntervalRawPolynomialLogKernel p z) := by
  have hone : Integrable (fun _ : unitInterval ↦ (1 : ℝ)) :=
    integrable_const 1
  have hsecond : Integrable (fun z : unitInterval × unitInterval ↦ f z.2) := by
    simpa using hone.mul_prod hf
  exact hsecond.mul_bdd
    (measurable_unitIntervalRawPolynomialLogKernel p).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (norm_unitIntervalRawPolynomialLogKernel_le p))

/-- The raw cross integrand with a polynomial is integrable for every
integrable function on the unit interval. -/
theorem integrable_sub_mul_unitIntervalRawPolynomialLogKernel
    (f : unitInterval → ℝ) (hf : Integrable f)
    (p : ℝ[X]) :
    Integrable (fun z : unitInterval × unitInterval ↦
      (f z.1 - f z.2) * unitIntervalRawPolynomialLogKernel p z) := by
  have hone : Integrable (fun _ : unitInterval ↦ (1 : ℝ)) :=
    integrable_const 1
  have hfirst : Integrable (fun z : unitInterval × unitInterval ↦ f z.1) := by
    simpa using hf.mul_prod hone
  have hsecond : Integrable (fun z : unitInterval × unitInterval ↦ f z.2) := by
    simpa using hone.mul_prod hf
  have hkernelMeas : AEStronglyMeasurable
      (unitIntervalRawPolynomialLogKernel p) := by
    exact (measurable_unitIntervalRawPolynomialLogKernel p).aestronglyMeasurable
  have hkernelBound : ∀ᵐ z : unitInterval × unitInterval,
      ‖unitIntervalRawPolynomialLogKernel p z‖ ≤
        polynomialDifferenceQuotientBound p := by
    filter_upwards [] with z
    exact norm_unitIntervalRawPolynomialLogKernel_le p z
  exact (hfirst.sub hsecond).mul_bdd hkernelMeas hkernelBound

/-- The raw double cross form with a polynomial equals twice the single
pairing against the exact polynomial logarithmic operator. -/
theorem integral_sub_mul_unitIntervalRawPolynomialLogKernel_eq
    (f : unitInterval → ℝ) (hf : Integrable f)
    (p : ℝ[X]) :
    (∫ z : unitInterval × unitInterval,
      (f z.1 - f z.2) * unitIntervalRawPolynomialLogKernel p z) =
        2 * ∫ x : unitInterval,
          f x * (shiftedLogKernel p).eval (x : ℝ) := by
  have hfst :=
    integrable_fst_mul_unitIntervalRawPolynomialLogKernel f hf p
  have hsnd :=
    integrable_snd_mul_unitIntervalRawPolynomialLogKernel f hf p
  have hswap :
      (∫ z : unitInterval × unitInterval,
        f z.2 * unitIntervalRawPolynomialLogKernel p z) =
        -∫ z : unitInterval × unitInterval,
          f z.1 * unitIntervalRawPolynomialLogKernel p z := by
    calc
      _ = ∫ z : unitInterval × unitInterval,
          (fun w : unitInterval × unitInterval ↦
            f w.2 * unitIntervalRawPolynomialLogKernel p w) z.swap :=
        (MeasureTheory.integral_prod_swap _).symm
      _ = ∫ z : unitInterval × unitInterval,
          -(f z.1 * unitIntervalRawPolynomialLogKernel p z) := by
        apply integral_congr_ae
        filter_upwards [] with z
        rcases z with ⟨x, y⟩
        simp only [Prod.swap_prod_mk]
        have hkernel :=
          unitIntervalRawPolynomialLogKernel_swap p (x, y)
        simp only [Prod.swap_prod_mk] at hkernel
        rw [hkernel]
        ring
      _ = _ := by rw [integral_neg]
  have hfst_eval :
      (∫ z : unitInterval × unitInterval,
        f z.1 * unitIntervalRawPolynomialLogKernel p z) =
        ∫ x : unitInterval,
          f x * (shiftedLogKernel p).eval (x : ℝ) := by
    calc
      _ = ∫ x : unitInterval, ∫ y : unitInterval,
          f x * unitIntervalRawPolynomialLogKernel p (x, y) :=
        MeasureTheory.integral_prod _ hfst
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [MeasureTheory.integral_const_mul,
          integral_unitIntervalRawPolynomialLogKernel]
  rw [show (fun z : unitInterval × unitInterval ↦
      (f z.1 - f z.2) * unitIntervalRawPolynomialLogKernel p z) =
      fun z ↦
        f z.1 * unitIntervalRawPolynomialLogKernel p z -
          f z.2 * unitIntervalRawPolynomialLogKernel p z by
    funext z
    ring,
    integral_sub hfst hsnd, hswap, hfst_eval]
  ring

end

end ArithmeticHodge.Analysis.ShiftedLogKernelCrossEnergy
