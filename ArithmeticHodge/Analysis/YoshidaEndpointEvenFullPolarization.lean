import ArithmeticHodge.Analysis.YoshidaEndpointEvenExactLowGramPositive

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization

open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointPotentialBound

noncomputable section

/-!
# Exact low/tail polarization in the even endpoint sector

This module keeps the fixed `P₀/P₂` block separate from the genuinely
infinite zero-two tail.  No finite-mode truncation occurs: the only analytic
hypothesis used by the logarithmic term is local Lipschitz regularity of the
whole tail.
-/

/-- The raw logarithmic cross term of the fixed low profile with a
`P₂`-orthogonal tail vanishes exactly.  The constant part cancels
pointwise, so only the structural `P₂` eigenfunction identity remains. -/
theorem centeredRawLogBilinear_fixedEvenLowProfile_tail_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r)
    (htwo : centeredEvenP2Coefficient r = 0)
    (c b : ℝ) :
    centeredRawLogBilinear (fun x ↦
      c * centeredEvenP0 x + b * centeredEvenP2 x) r = 0 := by
  have hpair : (∫ x : ℝ in -1..1, r x * centeredEvenP2 x) = 0 := by
    rw [integral_mul_centeredEvenP2_eq, htwo]
    ring
  have htwoRaw := centeredRawLogBilinear_centeredEvenP2_tail_eq_zero
    r hr hpair
  rw [show centeredRawLogBilinear (fun x ↦
      c * centeredEvenP0 x + b * centeredEvenP2 x) r =
      b * centeredRawLogBilinear centeredEvenP2 r by
    unfold centeredRawLogBilinear centeredEvenP0
    rw [show (fun x : ℝ ↦ ∫ y : ℝ in -1..1,
        (((c * 1 + b * centeredEvenP2 x) -
            (c * 1 + b * centeredEvenP2 y)) * (r x - r y)) /
              |x - y|) =
        fun x ↦ b * ∫ y : ℝ in -1..1,
          ((centeredEvenP2 x - centeredEvenP2 y) *
            (r x - r y)) / |x - y| by
      funext x
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _hy
      ring]
    exact intervalIntegral.integral_const_mul _ _]
  rw [htwoRaw, mul_zero]

/-- The ordinary `L²` cross term of the fixed low profile with a zero-two
tail vanishes exactly. -/
theorem integral_fixedEvenLowProfile_mul_tail_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r)
    (hzero : centeredEvenP0Coefficient r = 0)
    (htwo : centeredEvenP2Coefficient r = 0)
    (c b : ℝ) :
    (∫ x : ℝ in -1..1,
      (c * centeredEvenP0 x + b * centeredEvenP2 x) * r x) = 0 := by
  have h0 : IntervalIntegrable
      (fun x : ℝ ↦ r x * centeredEvenP0 x) volume (-1) 1 :=
    (hr.mul (by unfold centeredEvenP0; fun_prop)).intervalIntegrable (-1) 1
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ r x * centeredEvenP2 x) volume (-1) 1 :=
    (hr.mul (by unfold centeredEvenP2; fun_prop)).intervalIntegrable (-1) 1
  rw [show (fun x : ℝ ↦
      (c * centeredEvenP0 x + b * centeredEvenP2 x) * r x) =
      fun x ↦ c * (r x * centeredEvenP0 x) +
        b * (r x * centeredEvenP2 x) by
    funext x
    ring,
    intervalIntegral.integral_add (h0.const_mul c) (h2.const_mul b),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_mul_centeredEvenP0_eq,
    integral_mul_centeredEvenP2_eq,
    hzero, htwo]
  ring

/-- Exact polarization of the locally integrable endpoint-potential term. -/
theorem integral_endpointPotential_add_sq
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * (u x + v x) ^ 2) =
      (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * u x ^ 2) +
        2 * (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * u x * v x) +
        ∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * v x ^ 2 := by
  have huu := intervalIntegrable_endpointPotential_mul u u hu hu
  have huv := intervalIntegrable_endpointPotential_mul u v hu hv
  have hvv := intervalIntegrable_endpointPotential_mul v v hv hv
  have huu' : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * u x ^ 2)
      volume (-1) 1 := by simpa only [pow_two, mul_assoc] using huu
  have hvv' : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * v x ^ 2)
      volume (-1) 1 := by simpa only [pow_two, mul_assoc] using hvv
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * (u x + v x) ^ 2) =
      fun x ↦ yoshidaEndpointPotential x * u x ^ 2 +
        (2 * (yoshidaEndpointPotential x * u x * v x) +
          yoshidaEndpointPotential x * v x ^ 2) by
    funext x
    ring,
    intervalIntegral.integral_add huu' ((huv.const_mul 2).add hvv'),
    intervalIntegral.integral_add (huv.const_mul 2) hvv',
    intervalIntegral.integral_const_mul]
  ring

/-- Exact polarization of the ordinary mass term. -/
theorem integral_add_sq
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ x : ℝ in -1..1, (u x + v x) ^ 2) =
      (∫ x : ℝ in -1..1, u x ^ 2) +
        2 * (∫ x : ℝ in -1..1, u x * v x) +
        ∫ x : ℝ in -1..1, v x ^ 2 := by
  have huu : IntervalIntegrable (fun x : ℝ ↦ u x ^ 2)
      volume (-1) 1 := (hu.pow 2).intervalIntegrable (-1) 1
  have huv : IntervalIntegrable (fun x : ℝ ↦ u x * v x)
      volume (-1) 1 := (hu.mul hv).intervalIntegrable (-1) 1
  have hvv : IntervalIntegrable (fun x : ℝ ↦ v x ^ 2)
      volume (-1) 1 := (hv.pow 2).intervalIntegrable (-1) 1
  rw [show (fun x : ℝ ↦ (u x + v x) ^ 2) =
      fun x ↦ u x ^ 2 + (2 * (u x * v x) + v x ^ 2) by
    funext x
    ring,
    intervalIntegral.integral_add huu ((huv.const_mul 2).add hvv),
    intervalIntegral.integral_add (huv.const_mul 2) hvv,
    intervalIntegral.integral_const_mul]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
