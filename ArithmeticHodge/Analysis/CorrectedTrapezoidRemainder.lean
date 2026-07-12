import ArithmeticHodge.Analysis.TrapezoidalErrorBounds

set_option autoImplicit false

noncomputable section

open Set MeasureTheory intervalIntegral

namespace ArithmeticHodge.Analysis.CorrectedTrapezoidRemainder

/-!
The unit-cell Euler--Maclaurin remainder after the first- and third-derivative
endpoint corrections.  The kernel is the negative normalized fifth Bernoulli
polynomial, `-B₅ / 120`, with the sign convenient for repeated integration
by parts.
-/

def correctedTrapezoidFifthKernel (a t : ℝ) : ℝ :=
  (t - a) / 720 - (t - a) ^ 3 / 72 +
    (t - a) ^ 4 / 48 - (t - a) ^ 5 / 120

private def correctedTrapezoidFifthKernelFirst (a t : ℝ) : ℝ :=
  1 / 720 - (t - a) ^ 2 / 24 +
    (t - a) ^ 3 / 12 - (t - a) ^ 4 / 24

private def correctedTrapezoidFifthKernelSecond (a t : ℝ) : ℝ :=
  -(t - a) / 12 + (t - a) ^ 2 / 4 - (t - a) ^ 3 / 6

private def correctedTrapezoidFifthKernelThird (a t : ℝ) : ℝ :=
  -1 / 12 + (t - a) / 2 - (t - a) ^ 2 / 2

private theorem hasDerivAt_correctedTrapezoidFifthKernel (a t : ℝ) :
    HasDerivAt (correctedTrapezoidFifthKernel a)
      (correctedTrapezoidFifthKernelFirst a t) t := by
  unfold correctedTrapezoidFifthKernel correctedTrapezoidFifthKernelFirst
  have hx := (hasDerivAt_id t).sub_const a
  convert (((hx.div_const 720).sub ((hx.pow 3).div_const 72)).add
    ((hx.pow 4).div_const 48)).sub ((hx.pow 5).div_const 120) using 1
  simp only [id_eq]
  ring

private theorem hasDerivAt_correctedTrapezoidFifthKernelFirst (a t : ℝ) :
    HasDerivAt (correctedTrapezoidFifthKernelFirst a)
      (correctedTrapezoidFifthKernelSecond a t) t := by
  unfold correctedTrapezoidFifthKernelFirst correctedTrapezoidFifthKernelSecond
  have hx := (hasDerivAt_id t).sub_const a
  convert ((((hasDerivAt_const t (1 / 720 : ℝ)).sub
    ((hx.pow 2).div_const 24)).add ((hx.pow 3).div_const 12)).sub
      ((hx.pow 4).div_const 24)) using 1
  simp only [id_eq]
  ring

private theorem hasDerivAt_correctedTrapezoidFifthKernelSecond (a t : ℝ) :
    HasDerivAt (correctedTrapezoidFifthKernelSecond a)
      (correctedTrapezoidFifthKernelThird a t) t := by
  unfold correctedTrapezoidFifthKernelSecond correctedTrapezoidFifthKernelThird
  have hx := (hasDerivAt_id t).sub_const a
  convert (((hx.neg.div_const 12).add ((hx.pow 2).div_const 4)).sub
    ((hx.pow 3).div_const 6)) using 1
  simp only [id_eq]
  ring

/--
The exact unit-cell trapezoidal remainder after the first- and third-derivative
Euler--Maclaurin corrections.  The only analytic remainder is an integral of
the supplied fifth derivative against `correctedTrapezoidFifthKernel`.
-/
theorem trapezoidal_error_one_sub_first_add_third_eq_integral_fifth
    {f f1 f2 f3 f4 f5 : ℝ → ℝ} {a : ℝ}
    (hf1 : ∀ t, HasDerivAt f (f1 t) t)
    (hf2 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hf3 : ∀ t, HasDerivAt f2 (f3 t) t)
    (hf4 : ∀ t, HasDerivAt f3 (f4 t) t)
    (hf5 : ∀ t, HasDerivAt f4 (f5 t) t)
    (hf5_int : IntervalIntegrable f5 volume a (a + 1)) :
    trapezoidal_error f 1 a (a + 1) -
          (f1 (a + 1) - f1 a) / 12 +
          (f3 (a + 1) - f3 a) / 720 =
      -(∫ t in a..a + 1, correctedTrapezoidFifthKernel a t * f5 t) := by
  let C : ℝ → ℝ := correctedTrapezoidFifthKernel a
  let C1 : ℝ → ℝ := correctedTrapezoidFifthKernelFirst a
  let C2 : ℝ → ℝ := correctedTrapezoidFifthKernelSecond a
  let C3 : ℝ → ℝ := correctedTrapezoidFifthKernelThird a
  have hf1_cont : Continuous f1 :=
    continuous_iff_continuousAt.mpr fun t ↦ (hf2 t).continuousAt
  have hf2_cont : Continuous f2 :=
    continuous_iff_continuousAt.mpr fun t ↦ (hf3 t).continuousAt
  have hf3_cont : Continuous f3 :=
    continuous_iff_continuousAt.mpr fun t ↦ (hf4 t).continuousAt
  have hf4_cont : Continuous f4 :=
    continuous_iff_continuousAt.mpr fun t ↦ (hf5 t).continuousAt
  have hf1_int : IntervalIntegrable f1 volume a (a + 1) :=
    hf1_cont.intervalIntegrable _ _
  have hf2_int : IntervalIntegrable f2 volume a (a + 1) :=
    hf2_cont.intervalIntegrable _ _
  have hf3_int : IntervalIntegrable f3 volume a (a + 1) :=
    hf3_cont.intervalIntegrable _ _
  have hf4_int : IntervalIntegrable f4 volume a (a + 1) :=
    hf4_cont.intervalIntegrable _ _
  have hC_deriv : ∀ t, HasDerivAt C (C1 t) t := by
    intro t
    exact hasDerivAt_correctedTrapezoidFifthKernel a t
  have hC1_deriv : ∀ t, HasDerivAt C1 (C2 t) t := by
    intro t
    exact hasDerivAt_correctedTrapezoidFifthKernelFirst a t
  have hC2_deriv : ∀ t, HasDerivAt C2 (C3 t) t := by
    intro t
    exact hasDerivAt_correctedTrapezoidFifthKernelSecond a t
  have hC1_cont : Continuous C1 :=
    continuous_iff_continuousAt.mpr fun t ↦ (hC1_deriv t).continuousAt
  have hC2_cont : Continuous C2 :=
    continuous_iff_continuousAt.mpr fun t ↦ (hC2_deriv t).continuousAt
  have hC3_cont : Continuous C3 := by
    change Continuous (fun t : ℝ ↦
      -1 / 12 + (t - a) / 2 - (t - a) ^ 2 / 2)
    fun_prop
  have hC3_int : IntervalIntegrable C3 volume a (a + 1) :=
    hC3_cont.intervalIntegrable _ _
  have hC2_int : IntervalIntegrable C2 volume a (a + 1) :=
    hC2_cont.intervalIntegrable _ _
  have hC1_int : IntervalIntegrable C1 volume a (a + 1) :=
    hC1_cont.intervalIntegrable _ _
  have hbase :=
    TrapezoidalErrorBounds.trapezoidal_error_one_eq_integral_secondDerivKernel
      hf1 hf2 hf1_int hf2_int
  have hderiv1 : deriv f1 = f2 := by
    funext t
    exact (hf2 t).deriv
  have hint2 :
      (∫ t in a..a + 1, f2 t) = f1 (a + 1) - f1 a := by
    exact intervalIntegral.integral_deriv_eq_sub' f1 hderiv1
      (fun t _ht ↦ (hf2 t).differentiableAt) hf2_cont.continuousOn
  have hC3f2_int : IntervalIntegrable (fun t ↦ C3 t * f2 t) volume a (a + 1) :=
    hf2_int.continuousOn_mul (by fun_prop)
  have hconstf2_int :
      IntervalIntegrable (fun t ↦ (1 / 12 : ℝ) * f2 t) volume a (a + 1) :=
    hf2_int.const_mul (1 / 12 : ℝ)
  have hbase_decomp :
      trapezoidal_error f 1 a (a + 1) =
        (f1 (a + 1) - f1 a) / 12 +
          ∫ t in a..a + 1, C3 t * f2 t := by
    rw [hbase]
    rw [show (fun t ↦ ((t - a) * (a + 1 - t) / 2) * f2 t) =
        fun t ↦ (1 / 12 : ℝ) * f2 t + C3 t * f2 t by
      funext t
      dsimp only [C3, correctedTrapezoidFifthKernelThird]
      ring]
    rw [intervalIntegral.integral_add hconstf2_int hC3f2_int,
      intervalIntegral.integral_const_mul, hint2]
    ring
  have hparts2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := C2) (u' := C3) (v := f2) (v' := f3)
    (a := a) (b := a + 1)
    (fun t _ht ↦ hC2_deriv t) (fun t _ht ↦ hf3 t) hC3_int hf3_int
  have hC2_left : C2 a = 0 := by
    simp [C2, correctedTrapezoidFifthKernelSecond]
  have hC2_right : C2 (a + 1) = 0 := by
    simp [C2, correctedTrapezoidFifthKernelSecond]
    ring
  simp only [hC2_left, hC2_right, zero_mul, sub_zero, zero_sub] at hparts2
  have hparts1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := C1) (u' := C2) (v := f3) (v' := f4)
    (a := a) (b := a + 1)
    (fun t _ht ↦ hC1_deriv t) (fun t _ht ↦ hf4 t) hC2_int hf4_int
  have hC1_left : C1 a = 1 / 720 := by
    simp [C1, correctedTrapezoidFifthKernelFirst]
  have hC1_right : C1 (a + 1) = 1 / 720 := by
    simp [C1, correctedTrapezoidFifthKernelFirst]
    ring
  rw [hC1_left, hC1_right] at hparts1
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := C) (u' := C1) (v := f4) (v' := f5)
    (a := a) (b := a + 1)
    (fun t _ht ↦ hC_deriv t) (fun t _ht ↦ hf5 t) hC1_int hf5_int
  have hC_left : C a = 0 := by
    simp [C, correctedTrapezoidFifthKernel]
  have hC_right : C (a + 1) = 0 := by
    simp [C, correctedTrapezoidFifthKernel]
    ring
  simp only [hC_left, hC_right, zero_mul, sub_zero, zero_sub] at hparts
  change trapezoidal_error f 1 a (a + 1) -
      (f1 (a + 1) - f1 a) / 12 +
      (f3 (a + 1) - f3 a) / 720 =
    -(∫ t in a..a + 1, C t * f5 t)
  linarith [hbase_decomp, hparts2, hparts1, hparts]

end ArithmeticHodge.Analysis.CorrectedTrapezoidRemainder
