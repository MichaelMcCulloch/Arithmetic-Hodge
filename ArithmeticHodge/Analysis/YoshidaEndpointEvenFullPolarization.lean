import ArithmeticHodge.Analysis.YoshidaEndpointEvenExactLowGramPositive

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization

open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenP2LogEnergy
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaRegularKernelBound
open YoshidaRegularKernelSchur

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

private theorem integrable_regularComplexPairing
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    Integrable
      (fun z : ℝ × ℝ ↦
        (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
          (u z.2 : ℂ) * star (v z.1 : ℂ))
      ((volume.restrict (Icc (-1) 1)).prod
        (volume.restrict (Icc (-1) 1))) := by
  have hreal : Integrable
      (fun z : ℝ × ℝ ↦
        ((yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) *
          u z.2 * v z.1 : ℝ) : ℂ))
      ((volume.restrict (Icc (-1) 1)).prod
        (volume.restrict (Icc (-1) 1))) :=
    (integrable_regular_pairing u v hu hv).ofReal
  apply hreal.congr
  filter_upwards [] with z
  push_cast
  simp

/-- Exact polarization of the bounded regular-kernel quadratic. -/
theorem yoshidaEndpointRegularQuadratic_add_ofReal
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    yoshidaEndpointRegularQuadratic
        (fun x ↦ ((u x + v x : ℝ) : ℂ)) =
      yoshidaEndpointRegularQuadratic (fun x ↦ (u x : ℂ)) +
        (yoshidaEndpointRegularRealBilinear u v +
          yoshidaEndpointRegularRealBilinear v u) +
        yoshidaEndpointRegularQuadratic (fun x ↦ (v x : ℂ)) := by
  let μ : Measure ℝ := volume.restrict (Icc (-1) 1)
  let G : (ℝ → ℝ) → (ℝ → ℝ) → ℝ × ℝ → ℂ := fun p q z ↦
    (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
      (p z.2 : ℂ) * star (q z.1 : ℂ)
  have huu : Integrable (G u u) (μ.prod μ) := by
    simpa only [G, μ] using integrable_regularComplexPairing u u hu hu
  have huv : Integrable (G u v) (μ.prod μ) := by
    simpa only [G, μ] using integrable_regularComplexPairing u v hu hv
  have hvu : Integrable (G v u) (μ.prod μ) := by
    simpa only [G, μ] using integrable_regularComplexPairing v u hv hu
  have hvv : Integrable (G v v) (μ.prod μ) := by
    simpa only [G, μ] using integrable_regularComplexPairing v v hv hv
  have hvuSplit :
      (∫ z, G v u z + G v v z ∂μ.prod μ) =
        (∫ z, G v u z ∂μ.prod μ) +
          ∫ z, G v v z ∂μ.prod μ := by
    simpa only [Pi.add_apply] using integral_add hvu hvv
  have huvSplit :
      (∫ z, G u v z + (G v u z + G v v z) ∂μ.prod μ) =
        (∫ z, G u v z ∂μ.prod μ) +
          ∫ z, G v u z + G v v z ∂μ.prod μ := by
    simpa only [Pi.add_apply] using integral_add huv (hvu.add hvv)
  change (∫ z, G (fun x ↦ u x + v x) (fun x ↦ u x + v x) z
      ∂μ.prod μ) =
    (∫ z, G u u z ∂μ.prod μ) +
      ((∫ z, G u v z ∂μ.prod μ) +
        ∫ z, G v u z ∂μ.prod μ) +
      ∫ z, G v v z ∂μ.prod μ
  rw [show G (fun x ↦ u x + v x) (fun x ↦ u x + v x) =
      fun z ↦ G u u z + (G u v z + (G v u z + G v v z)) by
    funext z
    dsimp only [G]
    push_cast
    simp
    ring]
  calc
    (∫ z, G u u z + (G u v z + (G v u z + G v v z)) ∂μ.prod μ) =
        (∫ z, G u u z ∂μ.prod μ) +
          ∫ z, G u v z + (G v u z + G v v z) ∂μ.prod μ :=
      integral_add huu (huv.add (hvu.add hvv))
    _ = (∫ z, G u u z ∂μ.prod μ) +
        ((∫ z, G u v z ∂μ.prod μ) +
          ∫ z, G v u z + G v v z ∂μ.prod μ) := by
      rw [huvSplit]
    _ = _ := by
      rw [hvuSplit]
      ring

/-- The hyperbolic correction of a real profile is the difference of its
two real moment squares. -/
theorem yoshidaEndpointHyperbolicQuadratic_ofReal_eq_moments
    (u : ℝ → ℝ) :
    yoshidaEndpointHyperbolicQuadratic (fun x ↦ (u x : ℂ)) =
      2 * yoshidaEndpointA *
        (yoshidaEndpointCoshMoment u ^ 2 -
          yoshidaEndpointSinhMoment u ^ 2) := by
  have hcosh :
      (∫ x : ℝ in -1..1,
        (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * (u x : ℂ)) =
          (yoshidaEndpointCoshMoment u : ℂ) := by
    unfold yoshidaEndpointCoshMoment
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    norm_num
  have hsinh :
      (∫ x : ℝ in -1..1,
        (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * (u x : ℂ)) =
          (yoshidaEndpointSinhMoment u : ℂ) := by
    unfold yoshidaEndpointSinhMoment
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    norm_num
  unfold yoshidaEndpointHyperbolicQuadratic
  rw [hcosh, hsinh, Complex.normSq_ofReal, Complex.normSq_ofReal]
  ring

/-- Exact polarization of the rank-two hyperbolic correction. -/
theorem yoshidaEndpointHyperbolicQuadratic_add_ofReal
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    yoshidaEndpointHyperbolicQuadratic
        (fun x ↦ ((u x + v x : ℝ) : ℂ)) =
      yoshidaEndpointHyperbolicQuadratic (fun x ↦ (u x : ℂ)) +
        yoshidaEndpointHyperbolicQuadratic (fun x ↦ (v x : ℂ)) +
        4 * yoshidaEndpointA *
          (yoshidaEndpointCoshMoment u * yoshidaEndpointCoshMoment v -
            yoshidaEndpointSinhMoment u * yoshidaEndpointSinhMoment v) := by
  have hC : yoshidaEndpointCoshMoment (fun x ↦ u x + v x) =
      yoshidaEndpointCoshMoment u + yoshidaEndpointCoshMoment v := by
    have huC : IntervalIntegrable
        (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * u x)
        volume (-1) 1 := (by fun_prop : Continuous
          (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * u x))
            |>.intervalIntegrable (-1) 1
    have hvC : IntervalIntegrable
        (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * v x)
        volume (-1) 1 := (by fun_prop : Continuous
          (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * v x))
            |>.intervalIntegrable (-1) 1
    unfold yoshidaEndpointCoshMoment
    rw [show (fun x : ℝ ↦
        Real.cosh (yoshidaEndpointA * x / 2) * (u x + v x)) =
        fun x ↦ Real.cosh (yoshidaEndpointA * x / 2) * u x +
          Real.cosh (yoshidaEndpointA * x / 2) * v x by
      funext x
      ring,
      intervalIntegral.integral_add huC hvC]
  have hS : yoshidaEndpointSinhMoment (fun x ↦ u x + v x) =
      yoshidaEndpointSinhMoment u + yoshidaEndpointSinhMoment v := by
    have huS : IntervalIntegrable
        (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2) * u x)
        volume (-1) 1 := (by fun_prop : Continuous
          (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2) * u x))
            |>.intervalIntegrable (-1) 1
    have hvS : IntervalIntegrable
        (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2) * v x)
        volume (-1) 1 := (by fun_prop : Continuous
          (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2) * v x))
            |>.intervalIntegrable (-1) 1
    unfold yoshidaEndpointSinhMoment
    rw [show (fun x : ℝ ↦
        Real.sinh (yoshidaEndpointA * x / 2) * (u x + v x)) =
        fun x ↦ Real.sinh (yoshidaEndpointA * x / 2) * u x +
          Real.sinh (yoshidaEndpointA * x / 2) * v x by
      funext x
      ring,
      intervalIntegral.integral_add huS hvS]
  rw [yoshidaEndpointHyperbolicQuadratic_ofReal_eq_moments,
    yoshidaEndpointHyperbolicQuadratic_ofReal_eq_moments,
    yoshidaEndpointHyperbolicQuadratic_ofReal_eq_moments, hC, hS]
  ring

/-- Exact polarization of the complete clean quadratic between the fixed
two-dimensional low block and an arbitrary locally Lipschitz zero-two tail. -/
theorem yoshidaEndpointOddCleanQuadratic_low_tail
    (r : ℝ → ℝ) (hr : Continuous r)
    (htwo : centeredEvenP2Coefficient r = 0)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (c b : ℝ) :
    yoshidaEndpointOddCleanQuadratic
        (fun x ↦ yoshidaEndpointEvenLowProfile c b x + r x) =
      yoshidaEndpointOddCleanQuadratic (yoshidaEndpointEvenLowProfile c b) +
        2 * yoshidaEndpointEvenCleanBilinear
          (yoshidaEndpointEvenLowProfile c b) r +
        yoshidaEndpointOddCleanQuadratic r := by
  let p : ℝ → ℝ := yoshidaEndpointEvenLowProfile c b
  have hp : Continuous p := continuous_yoshidaEndpointEvenLowProfile c b
  have hpair : (∫ x : ℝ in -1..1, r x * centeredEvenP2 x) = 0 := by
    rw [integral_mul_centeredEvenP2_eq, htwo]
    ring
  have hrawTail := centeredRawLogEnergy_low_tail r hlocal hpair c b
  have hraw : centeredRawLogEnergy (fun x ↦ p x + r x) =
      centeredRawLogEnergy p + centeredRawLogEnergy r := by
    calc
      centeredRawLogEnergy (fun x ↦ p x + r x) =
          centeredRawLogEnergy (fun x ↦
            c * centeredEvenP0 x + b * centeredEvenP2 x + r x) := by
        congr 1
        funext x
        dsimp only [p]
        unfold yoshidaEndpointEvenLowProfile centeredEvenP0
        ring
      _ = b ^ 2 * centeredRawLogEnergy centeredEvenP2 +
          centeredRawLogEnergy r := hrawTail
      _ = centeredRawLogEnergy p + centeredRawLogEnergy r := by
        dsimp only [p]
        rw [centeredRawLogEnergy_yoshidaEndpointEvenLowProfile,
          centeredRawLogEnergy_centeredEvenP2]
        ring
  have hrawCross : centeredRawLogBilinear p r = 0 := by
    rw [show p = fun x ↦
        c * centeredEvenP0 x + b * centeredEvenP2 x by
      funext x
      dsimp only [p]
      unfold yoshidaEndpointEvenLowProfile centeredEvenP0
      ring]
    exact centeredRawLogBilinear_fixedEvenLowProfile_tail_eq_zero
      r hr htwo c b
  have hpotential := integral_endpointPotential_add_sq p r hp hr
  have hmass := integral_add_sq p r hp hr
  have hregular := yoshidaEndpointRegularQuadratic_add_ofReal p r hp hr
  have hhyper := yoshidaEndpointHyperbolicQuadratic_add_ofReal p r hp hr
  change yoshidaEndpointOddCleanQuadratic (fun x ↦ p x + r x) =
    yoshidaEndpointOddCleanQuadratic p +
      2 * yoshidaEndpointEvenCleanBilinear p r +
      yoshidaEndpointOddCleanQuadratic r
  unfold yoshidaEndpointOddCleanQuadratic
    yoshidaEndpointEvenCleanBilinear
  dsimp only
  rw [hraw, hrawCross, hpotential, hmass, hregular, hhyper]
  simp only [zero_div, add_re]
  ring

/-- A continuous low representer pairs integrably with every continuous
tail.  This is a bounded-kernel/Fubini statement, not a mode computation. -/
theorem intervalIntegrable_evenTailRepresenter_mul
    (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r) :
    IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenTailRepresenter p x * r x)
      volume (-1) 1 := by
  have hV := intervalIntegrable_endpointPotential_mul p r hp hr
  have hR := intervalIntegrable_regularRepresenter_mul p r hp hr
  have hC : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * r x)
      volume (-1) 1 := (by fun_prop : Continuous
        (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * r x))
          |>.intervalIntegrable (-1) 1
  apply ((hV.sub (hR.const_mul yoshidaEndpointA)).add
    (hC.const_mul (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment p))).congr
  intro x _hx
  unfold yoshidaEndpointEvenTailRepresenter
  ring

/-- Fubini identifies the continuous tail-representer pairing with its
potential, regular-kernel, and hyperbolic components. -/
theorem integral_evenTailRepresenter_mul_eq
    (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r) :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointEvenTailRepresenter p x * r x) =
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * p x * r x) -
      yoshidaEndpointA *
        (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter p x * r x) +
      2 * yoshidaEndpointA * yoshidaEndpointCoshMoment p *
        yoshidaEndpointCoshMoment r := by
  have hV := intervalIntegrable_endpointPotential_mul p r hp hr
  have hR := intervalIntegrable_regularRepresenter_mul p r hp hr
  have hC : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * r x)
      volume (-1) 1 := (by fun_prop : Continuous
        (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * r x))
          |>.intervalIntegrable (-1) 1
  unfold yoshidaEndpointEvenTailRepresenter
  rw [show (fun x : ℝ ↦
      (yoshidaEndpointPotential x * p x -
          yoshidaEndpointA * yoshidaEndpointEvenRegularRepresenter p x +
        2 * yoshidaEndpointA * yoshidaEndpointCoshMoment p *
          Real.cosh (yoshidaEndpointA * x / 2)) * r x) =
      fun x ↦ yoshidaEndpointPotential x * p x * r x -
        yoshidaEndpointA *
          (yoshidaEndpointEvenRegularRepresenter p x * r x) +
        (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment p) *
          (Real.cosh (yoshidaEndpointA * x / 2) * r x) by
    funext x
    ring,
    intervalIntegral.integral_add
      (hV.sub (hR.const_mul yoshidaEndpointA))
      (hC.const_mul (2 * yoshidaEndpointA * yoshidaEndpointCoshMoment p)),
    intervalIntegral.integral_sub hV (hR.const_mul yoshidaEndpointA),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  unfold yoshidaEndpointCoshMoment
  ring

private theorem yoshidaEndpointRegularRealBilinear_linear_left
    (u v r : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hr : Continuous r) (c b : ℝ) :
    yoshidaEndpointRegularRealBilinear (fun x ↦ c * u x + b * v x) r =
      (c : ℂ) * yoshidaEndpointRegularRealBilinear u r +
        (b : ℂ) * yoshidaEndpointRegularRealBilinear v r := by
  let μ : Measure ℝ := volume.restrict (Icc (-1) 1)
  let G : (ℝ → ℝ) → (ℝ → ℝ) → ℝ × ℝ → ℂ := fun p q z ↦
    (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
      (p z.2 : ℂ) * star (q z.1 : ℂ)
  have hur : Integrable (G u r) (μ.prod μ) := by
    simpa only [G, μ] using integrable_regularComplexPairing u r hu hr
  have hvr : Integrable (G v r) (μ.prod μ) := by
    simpa only [G, μ] using integrable_regularComplexPairing v r hv hr
  have hcu : (∫ z, (c : ℂ) * G u r z ∂μ.prod μ) =
      (c : ℂ) * ∫ z, G u r z ∂μ.prod μ := by
    exact integral_const_mul (c : ℂ) (G u r)
  have hbv : (∫ z, (b : ℂ) * G v r z ∂μ.prod μ) =
      (b : ℂ) * ∫ z, G v r z ∂μ.prod μ := by
    exact integral_const_mul (b : ℂ) (G v r)
  change (∫ z, G (fun x ↦ c * u x + b * v x) r z ∂μ.prod μ) =
    (c : ℂ) * (∫ z, G u r z ∂μ.prod μ) +
      (b : ℂ) * ∫ z, G v r z ∂μ.prod μ
  rw [show G (fun x ↦ c * u x + b * v x) r =
      fun z ↦ (c : ℂ) * G u r z + (b : ℂ) * G v r z by
    funext z
    dsimp only [G]
    push_cast
    ring,
    integral_add (hur.const_mul (c : ℂ)) (hvr.const_mul (b : ℂ)),
    hcu, hbv]

private theorem yoshidaEndpointRegularRealBilinear_linear_right
    (r u v : ℝ → ℝ) (hr : Continuous r) (hu : Continuous u)
    (hv : Continuous v) (c b : ℝ) :
    yoshidaEndpointRegularRealBilinear r (fun x ↦ c * u x + b * v x) =
      (c : ℂ) * yoshidaEndpointRegularRealBilinear r u +
        (b : ℂ) * yoshidaEndpointRegularRealBilinear r v := by
  let μ : Measure ℝ := volume.restrict (Icc (-1) 1)
  let G : (ℝ → ℝ) → (ℝ → ℝ) → ℝ × ℝ → ℂ := fun p q z ↦
    (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
      (p z.2 : ℂ) * star (q z.1 : ℂ)
  have hru : Integrable (G r u) (μ.prod μ) := by
    simpa only [G, μ] using integrable_regularComplexPairing r u hr hu
  have hrv : Integrable (G r v) (μ.prod μ) := by
    simpa only [G, μ] using integrable_regularComplexPairing r v hr hv
  have hcu : (∫ z, (c : ℂ) * G r u z ∂μ.prod μ) =
      (c : ℂ) * ∫ z, G r u z ∂μ.prod μ := by
    exact integral_const_mul (c : ℂ) (G r u)
  have hbv : (∫ z, (b : ℂ) * G r v z ∂μ.prod μ) =
      (b : ℂ) * ∫ z, G r v z ∂μ.prod μ := by
    exact integral_const_mul (b : ℂ) (G r v)
  change (∫ z, G r (fun x ↦ c * u x + b * v x) z ∂μ.prod μ) =
    (c : ℂ) * (∫ z, G r u z ∂μ.prod μ) +
      (b : ℂ) * ∫ z, G r v z ∂μ.prod μ
  rw [show G r (fun x ↦ c * u x + b * v x) =
      fun z ↦ (c : ℂ) * G r u z + (b : ℂ) * G r v z by
    funext z
    dsimp only [G]
    push_cast
    simp
    ring,
    integral_add (hru.const_mul (c : ℂ)) (hrv.const_mul (b : ℂ)),
    hcu, hbv]

private theorem yoshidaEndpointCoshMoment_linear
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (c b : ℝ) :
    yoshidaEndpointCoshMoment (fun x ↦ c * u x + b * v x) =
      c * yoshidaEndpointCoshMoment u + b * yoshidaEndpointCoshMoment v := by
  have hU : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * u x)
      volume (-1) 1 := (by fun_prop : Continuous
        (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * u x))
          |>.intervalIntegrable (-1) 1
  have hV : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * v x)
      volume (-1) 1 := (by fun_prop : Continuous
        (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * v x))
          |>.intervalIntegrable (-1) 1
  unfold yoshidaEndpointCoshMoment
  rw [show (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) *
      (c * u x + b * v x)) =
      fun x ↦ c * (Real.cosh (yoshidaEndpointA * x / 2) * u x) +
        b * (Real.cosh (yoshidaEndpointA * x / 2) * v x) by
    funext x
    ring,
    intervalIntegral.integral_add (hU.const_mul c) (hV.const_mul b),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- The clean low-to-tail bilinear term is exactly the two fixed
representer pairings. -/
theorem yoshidaEndpointEvenCleanBilinear_low_tail_eq_representers
    (r : ℝ → ℝ) (hr : Continuous r) (hre : Function.Even r)
    (hzero : centeredEvenP0Coefficient r = 0)
    (htwo : centeredEvenP2Coefficient r = 0)
    (c b : ℝ) :
    yoshidaEndpointEvenCleanBilinear
        (yoshidaEndpointEvenLowProfile c b) r =
      c * (∫ x : ℝ in -1..1,
        yoshidaEndpointEvenTailRepresenter0 x * r x) +
      b * (∫ x : ℝ in -1..1,
        yoshidaEndpointEvenTailRepresenter2 x * r x) := by
  have hP0 : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have hP2 : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  have hlow : yoshidaEndpointEvenLowProfile c b = fun x ↦
      c * centeredEvenP0 x + b * centeredEvenP2 x := by
    funext x
    unfold yoshidaEndpointEvenLowProfile centeredEvenP0
    ring
  have hpair2 : (∫ x : ℝ in -1..1, r x * centeredEvenP2 x) = 0 := by
    rw [integral_mul_centeredEvenP2_eq, htwo]
    ring
  have hmean : (∫ x : ℝ in -1..1, r x) = 0 := by
    unfold centeredEvenP0Coefficient at hzero
    linarith
  have hraw0 := centeredRawLogBilinear_centeredEvenP0_eq_zero r
  have hraw2 := centeredRawLogBilinear_centeredEvenP2_tail_eq_zero r hr hpair2
  have hrawLow := centeredRawLogBilinear_fixedEvenLowProfile_tail_eq_zero
    r hr htwo c b
  have hmass0 : (∫ x : ℝ in -1..1, centeredEvenP0 x * r x) = 0 := by
    simpa only [centeredEvenP0, one_mul] using hmean
  have hmass2 : (∫ x : ℝ in -1..1, centeredEvenP2 x * r x) = 0 := by
    rw [show (fun x : ℝ ↦ centeredEvenP2 x * r x) =
      fun x ↦ r x * centeredEvenP2 x by funext x; ring, hpair2]
  have hmassLow := integral_fixedEvenLowProfile_mul_tail_eq_zero
    r hr hzero htwo c b
  have hV0 := intervalIntegrable_endpointPotential_mul centeredEvenP0 r hP0 hr
  have hV2 := intervalIntegrable_endpointPotential_mul centeredEvenP2 r hP2 hr
  have hVLow :
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x *
        yoshidaEndpointEvenLowProfile c b x * r x) =
        c * (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * centeredEvenP0 x * r x) +
        b * (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * centeredEvenP2 x * r x) := by
    unfold yoshidaEndpointEvenLowProfile
    rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x *
        (c + b * centeredEvenP2 x) * r x) =
        fun x ↦ c * (yoshidaEndpointPotential x * centeredEvenP0 x * r x) +
          b * (yoshidaEndpointPotential x * centeredEvenP2 x * r x) by
      funext x
      unfold centeredEvenP0
      ring,
      intervalIntegral.integral_add (hV0.const_mul c) (hV2.const_mul b),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hregL := yoshidaEndpointRegularRealBilinear_linear_left
    centeredEvenP0 centeredEvenP2 r hP0 hP2 hr c b
  have hregR := yoshidaEndpointRegularRealBilinear_linear_right
    r centeredEvenP0 centeredEvenP2 hr hP0 hP2 c b
  have hcosh := yoshidaEndpointCoshMoment_linear
    centeredEvenP0 centeredEvenP2 hP0 hP2 c b
  have hsinh := yoshidaEndpointSinhMoment_eq_zero_of_even r hre
  rw [← hlow] at hrawLow
  have hmassLow' : (∫ x : ℝ in -1..1,
      yoshidaEndpointEvenLowProfile c b x * r x) = 0 := by
    rw [hlow]
    exact hmassLow
  have hregL' : yoshidaEndpointRegularRealBilinear
      (yoshidaEndpointEvenLowProfile c b) r =
      (c : ℂ) * yoshidaEndpointRegularRealBilinear centeredEvenP0 r +
        (b : ℂ) * yoshidaEndpointRegularRealBilinear centeredEvenP2 r := by
    rw [hlow]
    exact hregL
  have hregR' : yoshidaEndpointRegularRealBilinear r
      (yoshidaEndpointEvenLowProfile c b) =
      (c : ℂ) * yoshidaEndpointRegularRealBilinear r centeredEvenP0 +
        (b : ℂ) * yoshidaEndpointRegularRealBilinear r centeredEvenP2 := by
    rw [hlow]
    exact hregR
  have hcosh' : yoshidaEndpointCoshMoment
      (yoshidaEndpointEvenLowProfile c b) =
      c * yoshidaEndpointCoshMoment centeredEvenP0 +
        b * yoshidaEndpointCoshMoment centeredEvenP2 := by
    rw [hlow]
    exact hcosh
  have hlinear : yoshidaEndpointEvenCleanBilinear
      (yoshidaEndpointEvenLowProfile c b) r =
      c * yoshidaEndpointEvenCleanBilinear centeredEvenP0 r +
        b * yoshidaEndpointEvenCleanBilinear centeredEvenP2 r := by
    unfold yoshidaEndpointEvenCleanBilinear
    rw [hrawLow,
      hraw0, hraw2,
      hmassLow',
      hmass0, hmass2, hVLow, hregL', hregR', hcosh', hsinh]
    simp only [zero_div, mul_zero, sub_zero, add_re, mul_re, ofReal_re,
      ofReal_im, zero_mul]
    ring
  rw [hlinear,
    yoshidaEndpointEvenLowTailCross_zero r hr hre hmean,
    yoshidaEndpointEvenLowTailCross_two r hr hre hpair2]

/-- The exact form-domain expansion required by the projected Schur
reduction.  The low block is the true clean Gram, and the infinite tail
enters only through its two structural representer pairings. -/
theorem yoshidaEndpointOddCleanQuadratic_fixed_low_tail_expansion
    (r : ℝ → ℝ) (hr : Continuous r) (hre : Function.Even r)
    (hzero : centeredEvenP0Coefficient r = 0)
    (htwo : centeredEvenP2Coefficient r = 0)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (c b : ℝ) :
    yoshidaEndpointOddCleanQuadratic
        (fun x ↦ c * centeredEvenP0 x + b * centeredEvenP2 x + r x) =
      yoshidaEndpointEvenLowGram00 * c ^ 2 +
        2 * yoshidaEndpointEvenLowGram02 * c * b +
        yoshidaEndpointEvenLowGram22 * b ^ 2 +
        2 * c * (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenTailRepresenter0 x * r x) +
        2 * b * (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenTailRepresenter2 x * r x) +
        yoshidaEndpointOddCleanQuadratic r := by
  have hpolar := yoshidaEndpointOddCleanQuadratic_low_tail
    r hr htwo hlocal c b
  have hcross := yoshidaEndpointEvenCleanBilinear_low_tail_eq_representers
    r hr hre hzero htwo c b
  have hlow : yoshidaEndpointOddCleanQuadratic
      (yoshidaEndpointEvenLowProfile c b) =
      yoshidaEndpointEvenLowGram00 * c ^ 2 +
        2 * yoshidaEndpointEvenLowGram02 * c * b +
        yoshidaEndpointEvenLowGram22 * b ^ 2 := by
    rw [show yoshidaEndpointEvenLowProfile c b = fun x ↦
        c * centeredEvenP0 x + b * centeredEvenP2 x by
      funext x
      unfold yoshidaEndpointEvenLowProfile centeredEvenP0
      ring]
    exact yoshidaEndpointEvenLowGram_quadratic_eq_clean c b
  rw [show (fun x ↦ c * centeredEvenP0 x + b * centeredEvenP2 x + r x) =
      fun x ↦ yoshidaEndpointEvenLowProfile c b x + r x by
    funext x
    unfold yoshidaEndpointEvenLowProfile centeredEvenP0
    ring,
    hpolar, hlow, hcross]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
