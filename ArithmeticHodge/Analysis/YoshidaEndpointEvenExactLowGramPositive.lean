import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowPositive
import ArithmeticHodge.Analysis.YoshidaEndpointEvenTailRepresenter

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenExactLowGramPositive

open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenLowPositive
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaRegularKernelBound
open YoshidaRegularKernelSchur

noncomputable section

private theorem centeredRawLogEnergy_const_mul
    (w : ℝ → ℝ) (c : ℝ) :
    centeredRawLogEnergy (fun x ↦ c * w x) =
      c ^ 2 * centeredRawLogEnergy w := by
  have hpoint (x y : ℝ) :
      ((c * w x - c * w y) ^ 2 / |x - y|) =
        c ^ 2 * ((w x - w y) ^ 2 / |x - y|) := by
    ring
  unfold centeredRawLogEnergy
  simp_rw [hpoint]
  rw [show (fun x : ℝ ↦ ∫ y : ℝ in -1..1,
      c ^ 2 * ((w x - w y) ^ 2 / |x - y|)) =
      fun x ↦ c ^ 2 * ∫ y : ℝ in -1..1,
        (w x - w y) ^ 2 / |x - y| by
    funext x
    rw [intervalIntegral.integral_const_mul],
    intervalIntegral.integral_const_mul]

private theorem yoshidaEndpointRegularQuadratic_const_mul
    (w : ℝ → ℝ) (c : ℝ) :
    yoshidaEndpointRegularQuadratic (fun x ↦ ((c * w x : ℝ) : ℂ)) =
      (c : ℂ) ^ 2 *
        yoshidaEndpointRegularQuadratic (fun x ↦ (w x : ℂ)) := by
  unfold yoshidaEndpointRegularQuadratic
  dsimp only
  rw [show (fun p : ℝ × ℝ ↦
      (yoshidaRegularKernel ((Real.log 2 / 2) * |p.1 - p.2|) : ℂ) *
        ((c * w p.2 : ℝ) : ℂ) * star ((c * w p.1 : ℝ) : ℂ)) =
      fun p ↦ (c : ℂ) ^ 2 *
        ((yoshidaRegularKernel ((Real.log 2 / 2) * |p.1 - p.2|) : ℂ) *
          (w p.2 : ℂ) * star (w p.1 : ℂ)) by
    funext p
    push_cast
    simp
    ring]
  exact MeasureTheory.integral_const_mul ((c : ℂ) ^ 2) _

private theorem yoshidaEndpointHyperbolicQuadratic_const_mul
    (w : ℝ → ℝ) (c : ℝ) :
    yoshidaEndpointHyperbolicQuadratic (fun x ↦ ((c * w x : ℝ) : ℂ)) =
      c ^ 2 * yoshidaEndpointHyperbolicQuadratic (fun x ↦ (w x : ℂ)) := by
  have hcosh :
      (∫ x : ℝ in -1..1,
        (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) *
          ((c * w x : ℝ) : ℂ)) =
        (c : ℂ) * ∫ x : ℝ in -1..1,
          (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ) := by
    rw [show (fun x : ℝ ↦
        (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) *
          ((c * w x : ℝ) : ℂ)) =
        fun x ↦ (c : ℂ) *
          ((Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ)) by
      funext x
      push_cast
      ring]
    exact intervalIntegral.integral_const_mul (c : ℂ) _
  have hsinh :
      (∫ x : ℝ in -1..1,
        (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) *
          ((c * w x : ℝ) : ℂ)) =
        (c : ℂ) * ∫ x : ℝ in -1..1,
          (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ) := by
    rw [show (fun x : ℝ ↦
        (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) *
          ((c * w x : ℝ) : ℂ)) =
        fun x ↦ (c : ℂ) *
          ((Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ)) by
      funext x
      push_cast
      ring]
    exact intervalIntegral.integral_const_mul (c : ℂ) _
  unfold yoshidaEndpointHyperbolicQuadratic
  rw [hcosh, hsinh, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal]
  ring_nf

private theorem yoshidaEndpointOddCleanQuadratic_const_mul
    (w : ℝ → ℝ) (c : ℝ) :
    yoshidaEndpointOddCleanQuadratic (fun x ↦ c * w x) =
      c ^ 2 * yoshidaEndpointOddCleanQuadratic w := by
  have hpotential :
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * (c * w x) ^ 2) =
        c ^ 2 * ∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * w x ^ 2 := by
    rw [show (fun x : ℝ ↦
        yoshidaEndpointPotential x * (c * w x) ^ 2) =
        fun x ↦ c ^ 2 * (yoshidaEndpointPotential x * w x ^ 2) by
      funext x
      ring,
      intervalIntegral.integral_const_mul]
  have hmass :
      (∫ x : ℝ in -1..1, (c * w x) ^ 2) =
        c ^ 2 * ∫ x : ℝ in -1..1, w x ^ 2 := by
    rw [show (fun x : ℝ ↦ (c * w x) ^ 2) =
        fun x ↦ c ^ 2 * w x ^ 2 by
      funext x
      ring,
      intervalIntegral.integral_const_mul]
  have hregular := yoshidaEndpointRegularQuadratic_const_mul w c
  have hhyper := yoshidaEndpointHyperbolicQuadratic_const_mul w c
  unfold yoshidaEndpointOddCleanQuadratic
  dsimp only
  rw [centeredRawLogEnergy_const_mul, hpotential, hmass, hregular, hhyper]
  simp [pow_two]
  ring

private theorem yoshidaEndpointRegularRealBilinear_const_mul_right
    (u v : ℝ → ℝ) (c : ℝ) :
    yoshidaEndpointRegularRealBilinear u (fun x ↦ c * v x) =
      (c : ℂ) * yoshidaEndpointRegularRealBilinear u v := by
  unfold yoshidaEndpointRegularRealBilinear
  dsimp only
  rw [show (fun p : ℝ × ℝ ↦
      (yoshidaRegularKernel (yoshidaEndpointA * |p.1 - p.2|) : ℂ) *
        (u p.2 : ℂ) * star ((c * v p.1 : ℝ) : ℂ)) =
      fun p ↦ (c : ℂ) *
        ((yoshidaRegularKernel (yoshidaEndpointA * |p.1 - p.2|) : ℂ) *
          (u p.2 : ℂ) * star (v p.1 : ℂ)) by
    funext p
    push_cast
    simp
    ring]
  exact MeasureTheory.integral_const_mul (c : ℂ) _

private theorem yoshidaEndpointRegularRealBilinear_const_mul_left
    (u v : ℝ → ℝ) (c : ℝ) :
    yoshidaEndpointRegularRealBilinear (fun x ↦ c * u x) v =
      (c : ℂ) * yoshidaEndpointRegularRealBilinear u v := by
  unfold yoshidaEndpointRegularRealBilinear
  dsimp only
  rw [show (fun p : ℝ × ℝ ↦
      (yoshidaRegularKernel (yoshidaEndpointA * |p.1 - p.2|) : ℂ) *
        ((c * u p.2 : ℝ) : ℂ) * star (v p.1 : ℂ)) =
      fun p ↦ (c : ℂ) *
        ((yoshidaRegularKernel (yoshidaEndpointA * |p.1 - p.2|) : ℂ) *
          (u p.2 : ℂ) * star (v p.1 : ℂ)) by
    funext p
    push_cast
    ring]
  exact MeasureTheory.integral_const_mul (c : ℂ) _

private theorem yoshidaEndpointEvenConstantCrossFunctional_const_mul
    (u : ℝ → ℝ) (c : ℝ) :
    yoshidaEndpointEvenConstantCrossFunctional (fun x ↦ c * u x) =
      c * yoshidaEndpointEvenConstantCrossFunctional u := by
  have hpotential :
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * (c * u x)) =
        c * ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x := by
    rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x * (c * u x)) =
        fun x ↦ c * (yoshidaEndpointPotential x * u x) by
      funext x
      ring,
      intervalIntegral.integral_const_mul]
  have hmass :
      (∫ x : ℝ in -1..1, c * u x) =
        c * ∫ x : ℝ in -1..1, u x := by
    exact intervalIntegral.integral_const_mul c u
  have hregularLeft :=
    yoshidaEndpointRegularRealBilinear_const_mul_left
      u (fun _ ↦ 1) c
  have hregularRight :=
    yoshidaEndpointRegularRealBilinear_const_mul_right
      (fun _ ↦ 1) u c
  have hcosh :
      yoshidaEndpointCoshMoment (fun x ↦ c * u x) =
        c * yoshidaEndpointCoshMoment u := by
    unfold yoshidaEndpointCoshMoment
    rw [show (fun x : ℝ ↦
        Real.cosh (yoshidaEndpointA * x / 2) * (c * u x)) =
        fun x ↦ c *
          (Real.cosh (yoshidaEndpointA * x / 2) * u x) by
      funext x
      ring,
      intervalIntegral.integral_const_mul]
  unfold yoshidaEndpointEvenConstantCrossFunctional
    yoshidaEndpointRegularConstantCross
  rw [hpotential, hmass, hregularLeft, hregularRight, hcosh]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  ring

private theorem yoshidaEndpointEvenConstantCrossFunctional_centeredEvenP2_eq :
    yoshidaEndpointEvenConstantCrossFunctional centeredEvenP2 =
      yoshidaEndpointEvenLowGram02 := by
  have hsinh0 : yoshidaEndpointSinhMoment (fun _ : ℝ ↦ 1) = 0 := by
    simpa only [centeredEvenP0] using
      yoshidaEndpointSinhMoment_eq_zero_of_even centeredEvenP0
        (by intro x; rfl)
  change yoshidaEndpointEvenConstantCrossFunctional centeredEvenP2 =
    yoshidaEndpointEvenCleanBilinear (fun _ : ℝ ↦ 1) centeredEvenP2
  unfold yoshidaEndpointEvenCleanBilinear centeredRawLogBilinear
    yoshidaEndpointEvenConstantCrossFunctional
    yoshidaEndpointRegularConstantCross
  simp only [sub_self, zero_mul, zero_div, intervalIntegral.integral_zero,
    hsinh0, one_mul, sub_zero]
  ring_nf

/-- Exact polarization of the complete clean quadratic on the fixed
`P₀/P₂` block. -/
theorem yoshidaEndpointEvenLowGram_quadratic_eq_clean (c b : ℝ) :
    yoshidaEndpointOddCleanQuadratic
        (fun x ↦ c * centeredEvenP0 x + b * centeredEvenP2 x) =
      yoshidaEndpointEvenLowGram00 * c ^ 2 +
        2 * yoshidaEndpointEvenLowGram02 * c * b +
        yoshidaEndpointEvenLowGram22 * b ^ 2 := by
  have hadd := yoshidaEndpointOddCleanQuadratic_add_constant
    (fun x ↦ b * centeredEvenP2 x)
    (by unfold centeredEvenP2; fun_prop) c
  have hscaleQ := yoshidaEndpointOddCleanQuadratic_const_mul centeredEvenP2 b
  have hscaleCross :=
    yoshidaEndpointEvenConstantCrossFunctional_const_mul centeredEvenP2 b
  have h00 := yoshidaEndpointEvenLowGram00_eq
  have h22 := yoshidaEndpointEvenLowGram22_eq
  have h02 := yoshidaEndpointEvenConstantCrossFunctional_centeredEvenP2_eq
  rw [show (fun x : ℝ ↦ c * centeredEvenP0 x + b * centeredEvenP2 x) =
      fun x ↦ c + b * centeredEvenP2 x by
    funext x
    unfold centeredEvenP0
    ring,
    hadd, hscaleQ, hscaleCross, h02]
  have h00' : yoshidaEndpointOddCleanQuadratic (fun _ : ℝ ↦ 1) =
      yoshidaEndpointEvenLowGram00 := by
    simpa only [centeredEvenP0] using h00.symm
  rw [h00', ← h22]
  ring

/-- The exact constant entry is strictly positive because the structural
lower Gram is positive and is dominated by the complete clean quadratic. -/
theorem yoshidaEndpointEvenLowGram00_pos :
    0 < yoshidaEndpointEvenLowGram00 := by
  have hlower00 : 0 < yoshidaEndpointEvenLow00 :=
    (by norm_num : (0 : ℝ) < 3563 / 10000).trans
      yoshidaEndpointEvenLow_matrix_bounds.1
  have hdom := yoshidaEndpointEvenLow_quadratic_le_clean 1 0
  have hprofile : yoshidaEndpointEvenLowProfile 1 0 =
      fun x ↦ 1 * centeredEvenP0 x + 0 * centeredEvenP2 x := by
    funext x
    unfold yoshidaEndpointEvenLowProfile centeredEvenP0
    ring
  rw [hprofile, yoshidaEndpointEvenLowGram_quadratic_eq_clean] at hdom
  norm_num at hdom
  exact hlower00.trans_le hdom

private theorem yoshidaEndpointEvenLow_quadratic_pos_of_b_ne_zero
    (c b : ℝ) (hb : b ≠ 0) :
    0 < yoshidaEndpointEvenLow00 * c ^ 2 +
      2 * yoshidaEndpointEvenLow02 * c * b +
      yoshidaEndpointEvenLow22 * b ^ 2 := by
  have hbounds := yoshidaEndpointEvenLow_matrix_bounds
  have h00 : 0 < yoshidaEndpointEvenLow00 :=
    (by norm_num : (0 : ℝ) < 3563 / 10000).trans hbounds.1
  have hdet : 0 < yoshidaEndpointEvenLow00 * yoshidaEndpointEvenLow22 -
      yoshidaEndpointEvenLow02 ^ 2 := hbounds.2.2.2.2
  have hid :
      yoshidaEndpointEvenLow00 *
          (yoshidaEndpointEvenLow00 * c ^ 2 +
            2 * yoshidaEndpointEvenLow02 * c * b +
            yoshidaEndpointEvenLow22 * b ^ 2) =
        (yoshidaEndpointEvenLow00 * c +
            yoshidaEndpointEvenLow02 * b) ^ 2 +
          (yoshidaEndpointEvenLow00 * yoshidaEndpointEvenLow22 -
            yoshidaEndpointEvenLow02 ^ 2) * b ^ 2 := by
    ring
  have hscaled :
      0 < yoshidaEndpointEvenLow00 *
        (yoshidaEndpointEvenLow00 * c ^ 2 +
          2 * yoshidaEndpointEvenLow02 * c * b +
          yoshidaEndpointEvenLow22 * b ^ 2) := by
    rw [hid]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _)
      (mul_pos hdet (sq_pos_of_ne_zero hb))
  exact pos_of_mul_pos_right hscaled h00.le

/-- The exact `P₀/P₂` Gram determinant is strictly positive.  The proof tests
the domination inequality on the adjugate direction of the exact Gram; no
entry evaluation or finite certificate is used. -/
theorem yoshidaEndpointEvenLowGram_det_pos :
    0 < yoshidaEndpointEvenLowGram00 * yoshidaEndpointEvenLowGram22 -
      yoshidaEndpointEvenLowGram02 ^ 2 := by
  have hq00 := yoshidaEndpointEvenLowGram00_pos
  have hlowerPos := yoshidaEndpointEvenLow_quadratic_pos_of_b_ne_zero
    (-yoshidaEndpointEvenLowGram02) yoshidaEndpointEvenLowGram00 hq00.ne'
  have hdom := yoshidaEndpointEvenLow_quadratic_le_clean
    (-yoshidaEndpointEvenLowGram02) yoshidaEndpointEvenLowGram00
  have hprofile :
      yoshidaEndpointEvenLowProfile
          (-yoshidaEndpointEvenLowGram02) yoshidaEndpointEvenLowGram00 =
        fun x ↦
          (-yoshidaEndpointEvenLowGram02) * centeredEvenP0 x +
            yoshidaEndpointEvenLowGram00 * centeredEvenP2 x := by
    funext x
    unfold yoshidaEndpointEvenLowProfile centeredEvenP0
    ring
  rw [hprofile, yoshidaEndpointEvenLowGram_quadratic_eq_clean] at hdom
  have hexactPos := hlowerPos.trans_le hdom
  have hid :
      yoshidaEndpointEvenLowGram00 *
            (-yoshidaEndpointEvenLowGram02) ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 *
            (-yoshidaEndpointEvenLowGram02) *
              yoshidaEndpointEvenLowGram00 +
          yoshidaEndpointEvenLowGram22 *
            yoshidaEndpointEvenLowGram00 ^ 2 =
        yoshidaEndpointEvenLowGram00 *
          (yoshidaEndpointEvenLowGram00 * yoshidaEndpointEvenLowGram22 -
            yoshidaEndpointEvenLowGram02 ^ 2) := by
    ring
  rw [hid] at hexactPos
  exact pos_of_mul_pos_right hexactPos hq00.le

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenExactLowGramPositive
