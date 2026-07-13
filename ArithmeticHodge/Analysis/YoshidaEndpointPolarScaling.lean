import ArithmeticHodge.Analysis.YoshidaEndpointHyperbolicBound

set_option autoImplicit false

open Complex MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaEndpointPolarScaling

open YoshidaEndpointHyperbolicBound

noncomputable section

/-!
# Exact centered scaling of the endpoint polar term

The two real polar moments are the sum and difference of the hyperbolic
rank-two moments.  Their product therefore recovers the endpoint
hyperbolic quadratic exactly.
-/

/-- Scaling `y = a * x` transports a raw production-coordinate exponential
moment on `[-a,a]` to its centered counterpart on `[-1,1]`. -/
theorem integral_exp_mul_rescale
    {a s : ℝ} (ha : a ≠ 0) (w : ℝ → ℝ) :
    (∫ y : ℝ in -a..a, Real.exp (s * y) * w (y / a)) =
      a * ∫ x : ℝ in -1..1, Real.exp (s * (a * x)) * w x := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (f := fun y : ℝ ↦ Real.exp (s * y) * w (y / a))
    (a := (-1 : ℝ)) (b := 1) a
  simpa [ha, smul_eq_mul] using h.symm

/-- Exact centered polar/hyperbolic identity at Yoshida's endpoint scale. -/
theorem two_mul_endpointA_sq_mul_polarMoments_eq
    (w : ℝ → ℝ) (hw : Continuous w) :
    2 * yoshidaEndpointA ^ 2 *
        (∫ x : ℝ in -1..1,
          Real.exp (-yoshidaEndpointA * x / 2) * w x) *
        (∫ x : ℝ in -1..1,
          Real.exp (yoshidaEndpointA * x / 2) * w x) =
      yoshidaEndpointA *
        yoshidaEndpointHyperbolicQuadratic (fun x ↦ (w x : ℂ)) := by
  let C : ℝ := ∫ x : ℝ in -1..1,
    Real.cosh (yoshidaEndpointA * x / 2) * w x
  let S : ℝ := ∫ x : ℝ in -1..1,
    Real.sinh (yoshidaEndpointA * x / 2) * w x
  have hCint : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * w x)
      volume (-1) 1 :=
    Continuous.intervalIntegrable (by fun_prop) (-1) 1
  have hSint : IntervalIntegrable
      (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2) * w x)
      volume (-1) 1 :=
    Continuous.intervalIntegrable (by fun_prop) (-1) 1
  have hminus :
      (∫ x : ℝ in -1..1,
          Real.exp (-yoshidaEndpointA * x / 2) * w x) = C - S := by
    calc
      (∫ x : ℝ in -1..1,
          Real.exp (-yoshidaEndpointA * x / 2) * w x) =
          ∫ x : ℝ in -1..1,
            Real.cosh (yoshidaEndpointA * x / 2) * w x -
              Real.sinh (yoshidaEndpointA * x / 2) * w x := by
        apply intervalIntegral.integral_congr
        intro x _hx
        change Real.exp (-yoshidaEndpointA * x / 2) * w x = _
        rw [show -yoshidaEndpointA * x / 2 =
          -(yoshidaEndpointA * x / 2) by ring,
          ← Real.cosh_sub_sinh]
        ring
      _ = C - S := by
        rw [intervalIntegral.integral_sub hCint hSint]
  have hplus :
      (∫ x : ℝ in -1..1,
          Real.exp (yoshidaEndpointA * x / 2) * w x) = C + S := by
    calc
      (∫ x : ℝ in -1..1,
          Real.exp (yoshidaEndpointA * x / 2) * w x) =
          ∫ x : ℝ in -1..1,
            Real.cosh (yoshidaEndpointA * x / 2) * w x +
              Real.sinh (yoshidaEndpointA * x / 2) * w x := by
        apply intervalIntegral.integral_congr
        intro x _hx
        change Real.exp (yoshidaEndpointA * x / 2) * w x = _
        rw [← Real.cosh_add_sinh]
        ring
      _ = C + S := by
        rw [intervalIntegral.integral_add hCint hSint]
  have hCcomplex :
      (∫ x : ℝ in -1..1,
          (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ)) =
        (C : ℂ) := by
    dsimp only [C]
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    push_cast
    rfl
  have hScomplex :
      (∫ x : ℝ in -1..1,
          (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ)) =
        (S : ℂ) := by
    dsimp only [S]
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    push_cast
    rfl
  rw [hminus, hplus]
  unfold yoshidaEndpointHyperbolicQuadratic
  rw [hCcomplex, hScomplex, Complex.normSq_ofReal,
    Complex.normSq_ofReal]
  ring

/-- The product of the raw production-coordinate polar samples on
`[-yoshidaEndpointA, yoshidaEndpointA]` is the scaled endpoint hyperbolic
quadratic of the centered profile. -/
theorem two_mul_rescaledPolarMoments_eq_endpointHyperbolicQuadratic
    (w : ℝ → ℝ) (hw : Continuous w) :
    2 *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (-y / 2) * w (y / yoshidaEndpointA)) *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (y / 2) * w (y / yoshidaEndpointA)) =
      yoshidaEndpointA *
        yoshidaEndpointHyperbolicQuadratic (fun x ↦ (w x : ℂ)) := by
  have hneg :
      (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (-y / 2) * w (y / yoshidaEndpointA)) =
        yoshidaEndpointA *
          ∫ x : ℝ in -1..1,
            Real.exp (-yoshidaEndpointA * x / 2) * w x := by
    calc
      (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (-y / 2) * w (y / yoshidaEndpointA)) =
          ∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
            Real.exp ((-1 / 2 : ℝ) * y) *
              w (y / yoshidaEndpointA) := by
        apply intervalIntegral.integral_congr
        intro y _hy
        change Real.exp (-y / 2) * w (y / yoshidaEndpointA) = _
        rw [show -y / 2 = (-1 / 2 : ℝ) * y by ring]
      _ = yoshidaEndpointA *
          ∫ x : ℝ in -1..1,
            Real.exp ((-1 / 2 : ℝ) * (yoshidaEndpointA * x)) * w x :=
        integral_exp_mul_rescale yoshidaEndpointA_pos.ne' w
      _ = yoshidaEndpointA *
          ∫ x : ℝ in -1..1,
            Real.exp (-yoshidaEndpointA * x / 2) * w x := by
        apply congrArg (fun z : ℝ ↦ yoshidaEndpointA * z)
        apply intervalIntegral.integral_congr
        intro x _hx
        change Real.exp ((-1 / 2 : ℝ) * (yoshidaEndpointA * x)) * w x = _
        rw [show (-1 / 2 : ℝ) * (yoshidaEndpointA * x) =
          -yoshidaEndpointA * x / 2 by ring]
  have hpos :
      (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (y / 2) * w (y / yoshidaEndpointA)) =
        yoshidaEndpointA *
          ∫ x : ℝ in -1..1,
            Real.exp (yoshidaEndpointA * x / 2) * w x := by
    calc
      (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (y / 2) * w (y / yoshidaEndpointA)) =
          ∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
            Real.exp ((1 / 2 : ℝ) * y) *
              w (y / yoshidaEndpointA) := by
        apply intervalIntegral.integral_congr
        intro y _hy
        change Real.exp (y / 2) * w (y / yoshidaEndpointA) = _
        rw [show y / 2 = (1 / 2 : ℝ) * y by ring]
      _ = yoshidaEndpointA *
          ∫ x : ℝ in -1..1,
            Real.exp ((1 / 2 : ℝ) * (yoshidaEndpointA * x)) * w x :=
        integral_exp_mul_rescale yoshidaEndpointA_pos.ne' w
      _ = yoshidaEndpointA *
          ∫ x : ℝ in -1..1,
            Real.exp (yoshidaEndpointA * x / 2) * w x := by
        apply congrArg (fun z : ℝ ↦ yoshidaEndpointA * z)
        apply intervalIntegral.integral_congr
        intro x _hx
        change Real.exp ((1 / 2 : ℝ) * (yoshidaEndpointA * x)) * w x = _
        rw [show (1 / 2 : ℝ) * (yoshidaEndpointA * x) =
          yoshidaEndpointA * x / 2 by ring]
  rw [hneg, hpos]
  calc
    2 *
          (yoshidaEndpointA *
            ∫ x : ℝ in -1..1,
              Real.exp (-yoshidaEndpointA * x / 2) * w x) *
          (yoshidaEndpointA *
            ∫ x : ℝ in -1..1,
              Real.exp (yoshidaEndpointA * x / 2) * w x) =
        2 * yoshidaEndpointA ^ 2 *
          (∫ x : ℝ in -1..1,
            Real.exp (-yoshidaEndpointA * x / 2) * w x) *
          (∫ x : ℝ in -1..1,
            Real.exp (yoshidaEndpointA * x / 2) * w x) := by ring
    _ = _ := two_mul_endpointA_sq_mul_polarMoments_eq w hw

end

end ArithmeticHodge.Analysis.YoshidaEndpointPolarScaling
