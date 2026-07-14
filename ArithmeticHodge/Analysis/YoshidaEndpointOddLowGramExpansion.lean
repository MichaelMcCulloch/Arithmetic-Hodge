import ArithmeticHodge.Analysis.YoshidaEndpointOddFullPolarization

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointOddLowGramExpansion

open CenteredOddOneThreeEnergy
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddFullPolarization
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOcticTwoModeSchurData
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoPhaseFullProfile
open YoshidaRegularKernelBound

noncomputable section

/-!
# Exact clean Gram expansion on the intrinsic odd low block

The clean quadratic is polarized structurally on the two intrinsic odd
Legendre modes.  Scalar laws are proved from the exact clean bilinear form;
the only raw-log fact used in the two-mode addition is the exact `P₁/P₃`
shifted-Legendre orthogonality.
-/

private theorem centeredRawLogBilinear_const_mul_left
    (u v : ℝ → ℝ) (c : ℝ) :
    centeredRawLogBilinear (fun x ↦ c * u x) v =
      c * centeredRawLogBilinear u v := by
  unfold centeredRawLogBilinear
  rw [show (fun x : ℝ ↦ ∫ y : ℝ in -1..1,
      ((c * u x - c * u y) * (v x - v y)) / |x - y|) =
      fun x ↦ c * ∫ y : ℝ in -1..1,
        ((u x - u y) * (v x - v y)) / |x - y| by
    funext x
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _hy
    ring_nf,
    intervalIntegral.integral_const_mul]

private theorem centeredRawLogBilinear_symm
    (u v : ℝ → ℝ) :
    centeredRawLogBilinear u v = centeredRawLogBilinear v u := by
  unfold centeredRawLogBilinear
  apply intervalIntegral.integral_congr
  intro x _hx
  apply intervalIntegral.integral_congr
  intro y _hy
  ring_nf

private theorem centeredRawLogBilinear_const_mul_right
    (u v : ℝ → ℝ) (c : ℝ) :
    centeredRawLogBilinear u (fun x ↦ c * v x) =
      c * centeredRawLogBilinear u v := by
  rw [centeredRawLogBilinear_symm,
    centeredRawLogBilinear_const_mul_left,
    centeredRawLogBilinear_symm]

private theorem yoshidaEndpointRegularRealBilinear_const_mul_left
    (u v : ℝ → ℝ) (c : ℝ) :
    yoshidaEndpointRegularRealBilinear (fun x ↦ c * u x) v =
      (c : ℂ) * yoshidaEndpointRegularRealBilinear u v := by
  unfold yoshidaEndpointRegularRealBilinear
  dsimp only
  rw [show (fun z : ℝ × ℝ ↦
      (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
        ((c * u z.2 : ℝ) : ℂ) * star (v z.1 : ℂ)) =
      fun z ↦ (c : ℂ) *
        ((yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
          (u z.2 : ℂ) * star (v z.1 : ℂ)) by
    funext z
    push_cast
    ring_nf]
  exact integral_const_mul (c : ℂ) _

private theorem yoshidaEndpointRegularRealBilinear_const_mul_right
    (u v : ℝ → ℝ) (c : ℝ) :
    yoshidaEndpointRegularRealBilinear u (fun x ↦ c * v x) =
      (c : ℂ) * yoshidaEndpointRegularRealBilinear u v := by
  unfold yoshidaEndpointRegularRealBilinear
  dsimp only
  rw [show (fun z : ℝ × ℝ ↦
      (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
        (u z.2 : ℂ) * star ((c * v z.1 : ℝ) : ℂ)) =
      fun z ↦ (c : ℂ) *
        ((yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
          (u z.2 : ℂ) * star (v z.1 : ℂ)) by
    funext z
    push_cast
    simp
    ring_nf]
  exact integral_const_mul (c : ℂ) _

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

private theorem yoshidaEndpointRegularRealBilinear_add_left
    (u v r : ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hr : Continuous r) :
    yoshidaEndpointRegularRealBilinear (fun x ↦ u x + v x) r =
      yoshidaEndpointRegularRealBilinear u r +
        yoshidaEndpointRegularRealBilinear v r := by
  have huInt := integrable_regularComplexPairing u r hu hr
  have hvInt := integrable_regularComplexPairing v r hv hr
  unfold yoshidaEndpointRegularRealBilinear
  dsimp only
  rw [show (fun z : ℝ × ℝ ↦
      (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
        ((u z.2 + v z.2 : ℝ) : ℂ) * star (r z.1 : ℂ)) =
      fun z ↦
        (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
            (u z.2 : ℂ) * star (r z.1 : ℂ) +
          (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
            (v z.2 : ℂ) * star (r z.1 : ℂ) by
    funext z
    push_cast
    ring_nf,
    integral_add huInt hvInt]

private theorem yoshidaEndpointRegularRealBilinear_add_right
    (r u v : ℝ → ℝ)
    (hr : Continuous r) (hu : Continuous u) (hv : Continuous v) :
    yoshidaEndpointRegularRealBilinear r (fun x ↦ u x + v x) =
      yoshidaEndpointRegularRealBilinear r u +
        yoshidaEndpointRegularRealBilinear r v := by
  have huInt := integrable_regularComplexPairing r u hr hu
  have hvInt := integrable_regularComplexPairing r v hr hv
  unfold yoshidaEndpointRegularRealBilinear
  dsimp only
  rw [show (fun z : ℝ × ℝ ↦
      (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
        (r z.2 : ℂ) * star ((u z.1 + v z.1 : ℝ) : ℂ)) =
      fun z ↦
        (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
            (r z.2 : ℂ) * star (u z.1 : ℂ) +
          (yoshidaRegularKernel (yoshidaEndpointA * |z.1 - z.2|) : ℂ) *
            (r z.2 : ℂ) * star (v z.1 : ℂ) by
    funext z
    push_cast
    simp
    ring_nf,
    integral_add huInt hvInt]

private theorem yoshidaEndpointCoshMoment_const_mul
    (u : ℝ → ℝ) (c : ℝ) :
    yoshidaEndpointCoshMoment (fun x ↦ c * u x) =
      c * yoshidaEndpointCoshMoment u := by
  unfold yoshidaEndpointCoshMoment
  rw [show (fun x : ℝ ↦
      Real.cosh (yoshidaEndpointA * x / 2) * (c * u x)) =
      fun x ↦ c *
        (Real.cosh (yoshidaEndpointA * x / 2) * u x) by
    funext x
    ring_nf,
    intervalIntegral.integral_const_mul]

private theorem yoshidaEndpointSinhMoment_const_mul
    (u : ℝ → ℝ) (c : ℝ) :
    yoshidaEndpointSinhMoment (fun x ↦ c * u x) =
      c * yoshidaEndpointSinhMoment u := by
  unfold yoshidaEndpointSinhMoment
  rw [show (fun x : ℝ ↦
      Real.sinh (yoshidaEndpointA * x / 2) * (c * u x)) =
      fun x ↦ c *
        (Real.sinh (yoshidaEndpointA * x / 2) * u x) by
    funext x
    ring_nf,
    intervalIntegral.integral_const_mul]

/-- Real scalar linearity of the complete clean bilinear form in its first
argument. -/
theorem yoshidaEndpointEvenCleanBilinear_const_mul_left
    (u v : ℝ → ℝ) (c : ℝ) :
    yoshidaEndpointEvenCleanBilinear (fun x ↦ c * u x) v =
      c * yoshidaEndpointEvenCleanBilinear u v := by
  have hpotential :
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * (c * u x) * v x) =
      c * ∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * u x * v x := by
    rw [show (fun x : ℝ ↦
        yoshidaEndpointPotential x * (c * u x) * v x) =
        fun x ↦ c * (yoshidaEndpointPotential x * u x * v x) by
      funext x
      ring_nf,
      intervalIntegral.integral_const_mul]
  have hmass : (∫ x : ℝ in -1..1, (c * u x) * v x) =
      c * ∫ x : ℝ in -1..1, u x * v x := by
    rw [show (fun x : ℝ ↦ (c * u x) * v x) =
        fun x ↦ c * (u x * v x) by
      funext x
      ring_nf,
      intervalIntegral.integral_const_mul]
  unfold yoshidaEndpointEvenCleanBilinear
  rw [centeredRawLogBilinear_const_mul_left,
    hpotential, hmass,
    yoshidaEndpointRegularRealBilinear_const_mul_left,
    yoshidaEndpointRegularRealBilinear_const_mul_right,
    yoshidaEndpointCoshMoment_const_mul,
    yoshidaEndpointSinhMoment_const_mul]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  ring_nf

/-- Symmetry of the complete clean bilinear form. -/
theorem yoshidaEndpointEvenCleanBilinear_symm
    (u v : ℝ → ℝ) :
    yoshidaEndpointEvenCleanBilinear u v =
      yoshidaEndpointEvenCleanBilinear v u := by
  have hpotential :
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * u x * v x) =
      ∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * v x * u x := by
    apply intervalIntegral.integral_congr
    intro x _hx
    ring_nf
  have hmass : (∫ x : ℝ in -1..1, u x * v x) =
      ∫ x : ℝ in -1..1, v x * u x := by
    apply intervalIntegral.integral_congr
    intro x _hx
    ring_nf
  unfold yoshidaEndpointEvenCleanBilinear
  rw [centeredRawLogBilinear_symm, hpotential, hmass]
  ring_nf

/-- Real scalar linearity of the complete clean bilinear form in its second
argument. -/
theorem yoshidaEndpointEvenCleanBilinear_const_mul_right
    (u v : ℝ → ℝ) (c : ℝ) :
    yoshidaEndpointEvenCleanBilinear u (fun x ↦ c * v x) =
      c * yoshidaEndpointEvenCleanBilinear u v := by
  rw [yoshidaEndpointEvenCleanBilinear_symm,
    yoshidaEndpointEvenCleanBilinear_const_mul_left,
    yoshidaEndpointEvenCleanBilinear_symm]

/-- Two-sided real homogeneity of the complete clean bilinear form. -/
theorem yoshidaEndpointEvenCleanBilinear_const_mul_const_mul
    (u v : ℝ → ℝ) (c d : ℝ) :
    yoshidaEndpointEvenCleanBilinear
        (fun x ↦ c * u x) (fun x ↦ d * v x) =
      c * d * yoshidaEndpointEvenCleanBilinear u v := by
  rw [yoshidaEndpointEvenCleanBilinear_const_mul_left,
    yoshidaEndpointEvenCleanBilinear_const_mul_right]
  ring_nf

/-- Real quadratic homogeneity of the complete clean endpoint form. -/
theorem yoshidaEndpointOddCleanQuadratic_const_mul
    (u : ℝ → ℝ) (c : ℝ) :
    yoshidaEndpointOddCleanQuadratic (fun x ↦ c * u x) =
      c ^ 2 * yoshidaEndpointOddCleanQuadratic u := by
  rw [← yoshidaEndpointEvenCleanBilinear_self,
    yoshidaEndpointEvenCleanBilinear_const_mul_const_mul,
    yoshidaEndpointEvenCleanBilinear_self]
  ring_nf

private theorem centeredOddP1Coefficient_centeredP3_eq_zero :
    centeredOddP1Coefficient centeredP3 = 0 := by
  unfold centeredOddP1Coefficient
  rw [show (∫ x : ℝ in -1..1, centeredP3 x * centeredP1 x) =
      ∫ x : ℝ in -1..1, centeredP1 x * centeredP3 x by
    apply intervalIntegral.integral_congr
    intro x _hx
    ring_nf,
    integral_centeredP1_mul_p3]
  ring_nf

private theorem centeredRawLogBilinear_centeredP1_centeredP3_eq_zero :
    centeredRawLogBilinear centeredP1 centeredP3 = 0 := by
  exact centeredRawLogBilinear_centeredP1_tail_eq_zero
    centeredP3 (by unfold centeredP3; fun_prop)
      centeredOddP1Coefficient_centeredP3_eq_zero

/-- Exact clean polarization of arbitrary scalar multiples of the intrinsic
odd degree-one and degree-three modes. -/
theorem yoshidaEndpointOddCleanQuadratic_one_three_add_eq_bilinear
    (c d : ℝ) :
    yoshidaEndpointOddCleanQuadratic (fun x ↦
        c * centeredP1 x + d * centeredP3 x) =
      yoshidaEndpointOddCleanQuadratic (fun x ↦ c * centeredP1 x) +
        2 * yoshidaEndpointEvenCleanBilinear
          (fun x ↦ c * centeredP1 x) (fun x ↦ d * centeredP3 x) +
        yoshidaEndpointOddCleanQuadratic (fun x ↦ d * centeredP3 x) := by
  let p : ℝ → ℝ := fun x ↦ c * centeredP1 x
  let q : ℝ → ℝ := fun x ↦ d * centeredP3 x
  have hp : Continuous p := by
    dsimp only [p]
    unfold centeredP1
    fun_prop
  have hq : Continuous q := by
    dsimp only [q]
    unfold centeredP3
    fun_prop
  have hraw : centeredRawLogEnergy (fun x ↦ p x + q x) =
      centeredRawLogEnergy p + centeredRawLogEnergy q := by
    rw [show (fun x ↦ p x + q x) =
        factorTwoOddStructuralLowProfile c d by
      funext x
      dsimp only [p, q]
      unfold factorTwoOddStructuralLowProfile
      rfl,
      centeredRawLogEnergy_factorTwoOddStructuralLowProfile,
      show centeredRawLogEnergy p =
          c ^ 2 * centeredRawLogEnergy centeredP1 by
        simpa only [p] using centeredRawLogEnergy_const_mul c centeredP1,
      show centeredRawLogEnergy q =
          d ^ 2 * centeredRawLogEnergy centeredP3 by
        simpa only [q] using centeredRawLogEnergy_const_mul d centeredP3,
      centeredRawLogEnergy_centeredP1,
      centeredRawLogEnergy_centeredP3]
    ring
  have hrawCross : centeredRawLogBilinear p q = 0 := by
    dsimp only [p, q]
    rw [centeredRawLogBilinear_const_mul_left,
      centeredRawLogBilinear_const_mul_right,
      centeredRawLogBilinear_centeredP1_centeredP3_eq_zero]
    ring
  have hpotential := integral_endpointPotential_add_sq p q hp hq
  have hmass := integral_add_sq p q hp hq
  have hregular := yoshidaEndpointRegularQuadratic_add_ofReal p q hp hq
  have hhyper := yoshidaEndpointHyperbolicQuadratic_add_ofReal p q hp hq
  change yoshidaEndpointOddCleanQuadratic (fun x ↦ p x + q x) =
    yoshidaEndpointOddCleanQuadratic p +
      2 * yoshidaEndpointEvenCleanBilinear p q +
      yoshidaEndpointOddCleanQuadratic q
  unfold yoshidaEndpointOddCleanQuadratic
    yoshidaEndpointEvenCleanBilinear
  dsimp only
  rw [hraw, hrawCross, hpotential, hmass, hregular, hhyper]
  simp only [zero_div, add_re]
  ring

/-- On the two intrinsic odd modes, the generic clean polarization is the
concrete clean bilinear form, including arbitrary real scalars. -/
theorem factorTwoCenteredCleanPolarization_one_three
    (c d : ℝ) :
    factorTwoCenteredCleanPolarization
        (fun x ↦ c * centeredP1 x) (fun x ↦ d * centeredP3 x) =
      c * d * yoshidaEndpointEvenCleanBilinear centeredP1 centeredP3 := by
  unfold factorTwoCenteredCleanPolarization
  rw [show yoshidaEndpointOddCleanQuadratic
      ((fun x ↦ c * centeredP1 x) + (fun x ↦ d * centeredP3 x)) =
      yoshidaEndpointOddCleanQuadratic (fun x ↦
        c * centeredP1 x + d * centeredP3 x) by rfl,
    yoshidaEndpointOddCleanQuadratic_one_three_add_eq_bilinear]
  rw [yoshidaEndpointEvenCleanBilinear_const_mul_const_mul]
  ring

/-- The generic `P₁,P₃` polarization entry is the exact clean bilinear
entry. -/
theorem yoshidaEndpointOddLowGram13_eq_bilinear :
    yoshidaEndpointOddLowGram13 =
      yoshidaEndpointEvenCleanBilinear centeredP1 centeredP3 := by
  unfold yoshidaEndpointOddLowGram13
  simpa only [one_mul] using factorTwoCenteredCleanPolarization_one_three 1 1

/-- Exact linearization of the clean odd low block against an arbitrary
second argument.  No finite-mode approximation enters this identity. -/
theorem yoshidaEndpointEvenCleanBilinear_oddStructuralLow
    (c d : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0) :
    yoshidaEndpointEvenCleanBilinear
        (factorTwoOddStructuralLowProfile c d) r =
      c * yoshidaEndpointEvenCleanBilinear centeredP1 r +
        d * yoshidaEndpointEvenCleanBilinear centeredP3 r := by
  have h1 : Continuous centeredP1 := by
    unfold centeredP1
    fun_prop
  have h3 : Continuous centeredP3 := by
    unfold centeredP3
    fun_prop
  have hrawLow : centeredRawLogBilinear
      (factorTwoOddStructuralLowProfile c d) r = 0 :=
    centeredRawLogBilinear_fixedOddLowProfile_tail_eq_zero
      r hr hone hthree c d
  have hraw1 : centeredRawLogBilinear centeredP1 r = 0 :=
    centeredRawLogBilinear_centeredP1_tail_eq_zero r hr hone
  have hraw3 : centeredRawLogBilinear centeredP3 r = 0 :=
    centeredRawLogBilinear_centeredP3_tail_eq_zero r hr hthree
  have hpotential1 := intervalIntegrable_endpointPotential_mul
    centeredP1 r h1 hr
  have hpotential3 := intervalIntegrable_endpointPotential_mul
    centeredP3 r h3 hr
  have hpotential :
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x *
          factorTwoOddStructuralLowProfile c d x * r x) =
      c * (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * centeredP1 x * r x) +
        d * (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * centeredP3 x * r x) := by
    rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x *
        factorTwoOddStructuralLowProfile c d x * r x) =
        fun x ↦ c *
            (yoshidaEndpointPotential x * centeredP1 x * r x) +
          d * (yoshidaEndpointPotential x * centeredP3 x * r x) by
      funext x
      unfold factorTwoOddStructuralLowProfile
      ring,
      intervalIntegral.integral_add
        (hpotential1.const_mul c) (hpotential3.const_mul d),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hmass1 : IntervalIntegrable
      (fun x : ℝ ↦ centeredP1 x * r x) volume (-1) 1 :=
    (h1.mul hr).intervalIntegrable (-1) 1
  have hmass3 : IntervalIntegrable
      (fun x : ℝ ↦ centeredP3 x * r x) volume (-1) 1 :=
    (h3.mul hr).intervalIntegrable (-1) 1
  have hmass :
      (∫ x : ℝ in -1..1,
        factorTwoOddStructuralLowProfile c d x * r x) =
      c * (∫ x : ℝ in -1..1, centeredP1 x * r x) +
        d * (∫ x : ℝ in -1..1, centeredP3 x * r x) := by
    rw [show (fun x : ℝ ↦
        factorTwoOddStructuralLowProfile c d x * r x) =
        fun x ↦ c * (centeredP1 x * r x) +
          d * (centeredP3 x * r x) by
      funext x
      unfold factorTwoOddStructuralLowProfile
      ring,
      intervalIntegral.integral_add
        (hmass1.const_mul c) (hmass3.const_mul d),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hregularLeft : yoshidaEndpointRegularRealBilinear
      (factorTwoOddStructuralLowProfile c d) r =
      (c : ℂ) * yoshidaEndpointRegularRealBilinear centeredP1 r +
        (d : ℂ) * yoshidaEndpointRegularRealBilinear centeredP3 r := by
    rw [show factorTwoOddStructuralLowProfile c d =
        fun x ↦ c * centeredP1 x + d * centeredP3 x by rfl,
      yoshidaEndpointRegularRealBilinear_add_left
        (fun x ↦ c * centeredP1 x) (fun x ↦ d * centeredP3 x) r
        (h1.const_mul c) (h3.const_mul d) hr,
      yoshidaEndpointRegularRealBilinear_const_mul_left,
      yoshidaEndpointRegularRealBilinear_const_mul_left]
  have hregularRight : yoshidaEndpointRegularRealBilinear r
      (factorTwoOddStructuralLowProfile c d) =
      (c : ℂ) * yoshidaEndpointRegularRealBilinear r centeredP1 +
        (d : ℂ) * yoshidaEndpointRegularRealBilinear r centeredP3 := by
    rw [show factorTwoOddStructuralLowProfile c d =
        fun x ↦ c * centeredP1 x + d * centeredP3 x by rfl,
      yoshidaEndpointRegularRealBilinear_add_right r
        (fun x ↦ c * centeredP1 x) (fun x ↦ d * centeredP3 x)
        hr (h1.const_mul c) (h3.const_mul d),
      yoshidaEndpointRegularRealBilinear_const_mul_right,
      yoshidaEndpointRegularRealBilinear_const_mul_right]
  have hcosh : yoshidaEndpointCoshMoment
      (factorTwoOddStructuralLowProfile c d) =
      c * yoshidaEndpointCoshMoment centeredP1 +
        d * yoshidaEndpointCoshMoment centeredP3 := by
    unfold yoshidaEndpointCoshMoment factorTwoOddStructuralLowProfile
    rw [show (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) *
        (c * centeredP1 x + d * centeredP3 x)) =
        fun x ↦ c *
            (Real.cosh (yoshidaEndpointA * x / 2) * centeredP1 x) +
          d * (Real.cosh (yoshidaEndpointA * x / 2) * centeredP3 x) by
      funext x
      ring,
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) (-1) 1 |>.const_mul c)
        (Continuous.intervalIntegrable (by fun_prop) (-1) 1 |>.const_mul d),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hsinh : yoshidaEndpointSinhMoment
      (factorTwoOddStructuralLowProfile c d) =
      c * yoshidaEndpointSinhMoment centeredP1 +
        d * yoshidaEndpointSinhMoment centeredP3 := by
    unfold yoshidaEndpointSinhMoment factorTwoOddStructuralLowProfile
    rw [show (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2) *
        (c * centeredP1 x + d * centeredP3 x)) =
        fun x ↦ c *
            (Real.sinh (yoshidaEndpointA * x / 2) * centeredP1 x) +
          d * (Real.sinh (yoshidaEndpointA * x / 2) * centeredP3 x) by
      funext x
      ring,
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) (-1) 1 |>.const_mul c)
        (Continuous.intervalIntegrable (by fun_prop) (-1) 1 |>.const_mul d),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  unfold yoshidaEndpointEvenCleanBilinear
  rw [hrawLow, hraw1, hraw3, hpotential, hmass,
    hregularLeft, hregularRight, hcosh, hsinh]
  simp only [zero_div, add_re, mul_re, ofReal_re, ofReal_im,
    zero_mul, sub_zero]
  ring

/-- Exact two-mode Gram identity for the intrinsic odd clean block. -/
theorem yoshidaEndpointOddLowGram_quadratic
    (c d : ℝ) :
    yoshidaEndpointOddCleanQuadratic
        (factorTwoOddStructuralLowProfile c d) =
      yoshidaEndpointOddLowGram11 * c ^ 2 +
        2 * yoshidaEndpointOddLowGram13 * c * d +
        yoshidaEndpointOddLowGram33 * d ^ 2 := by
  rw [show factorTwoOddStructuralLowProfile c d =
      fun x ↦ c * centeredP1 x + d * centeredP3 x by
    rfl,
    yoshidaEndpointOddCleanQuadratic_one_three_add_eq_bilinear,
    yoshidaEndpointOddCleanQuadratic_const_mul,
    yoshidaEndpointOddCleanQuadratic_const_mul,
    yoshidaEndpointEvenCleanBilinear_const_mul_const_mul,
    ← yoshidaEndpointOddLowGram13_eq_bilinear]
  unfold yoshidaEndpointOddLowGram11 yoshidaEndpointOddLowGram33
  ring

end


end ArithmeticHodge.Analysis.YoshidaEndpointOddLowGramExpansion
