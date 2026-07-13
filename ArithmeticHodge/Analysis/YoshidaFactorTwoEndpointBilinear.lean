import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointClean

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointBilinear

noncomputable section

open CenteredEndpointCorrelation
open MultiplicativeWeil
open MultiplicativeWeilRestrictedSupportEndpointPositive
open YoshidaBombieriCrossDistribution
open YoshidaCauchyPairing
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoDiagonalPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoParityDeterminant
open YoshidaFactorTwoParityRealification
open YoshidaRenormalizedGeometricKernel
open YoshidaStructuralKernelIntegrability

/-!
# Bilinear form of the centered factor-two perturbation

The factor-two endpoint perturbation is kept as one symmetric polarization.
In particular, its smooth correlation kernel and both retained prime atoms are
never estimated separately in the identities below.  Bilinearity is not
claimed until the singular folded integral has been justified explicitly.
-/

/-- The ordered centered cross-correlation on the endpoint interval. -/
def factorTwoCenteredCrossCorrelation
    (u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ in -1..1 - t, u (t + x) * v x

/-- The symmetric polarization of centered endpoint correlation. -/
def factorTwoCenteredCorrelationBilinear
    (u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  (factorTwoCenteredCrossCorrelation u v t +
      factorTwoCenteredCrossCorrelation v u t) / 2

theorem factorTwoCenteredCrossCorrelation_self
    (w : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredCrossCorrelation w w t =
      centeredEndpointCorrelation w t := by
  rfl

/-- The symmetric cross-correlation specializes exactly to the existing
centered autocorrelation on the diagonal. -/
theorem factorTwoCenteredCorrelationBilinear_self
    (w : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredCorrelationBilinear w w t =
      centeredEndpointCorrelation w t := by
  unfold factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation centeredEndpointCorrelation
  ring

/-- The adjacent smooth kernel is continuous away from its sole polar point. -/
theorem continuousAt_factorTwoAdjacentSmoothKernel_of_ne_zero
    {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt factorTwoAdjacentSmoothKernel t := by
  have hden : Real.exp t - Real.exp (-t) ≠ 0 := by
    intro hzero
    have hexp : Real.exp t = Real.exp (-t) := sub_eq_zero.mp hzero
    have htneg : t = -t := Real.exp_injective hexp
    exact ht (by linarith)
  have hodd : ContinuousAt oddKernel t := by
    unfold oddKernel
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact hden
  unfold factorTwoAdjacentSmoothKernel
  exact (by fun_prop : ContinuousAt (fun u : ℝ ↦
      2 * Real.cosh (u / 2)) t).sub (hodd.div_const 2)

/-- The symmetric polarization of the complete centered perturbation.  The
smooth archimedean kernel and both prime atoms remain coupled in every term
of this definition. -/
def factorTwoCenteredSymmetricPerturbationPolarization
    (u v : ℝ → ℝ) : ℝ :=
  (factorTwoCenteredSymmetricPerturbation (u + v) -
      factorTwoCenteredSymmetricPerturbation u -
      factorTwoCenteredSymmetricPerturbation v) / 2

/-- The perturbation polarization has the original quadratic perturbation as its
diagonal. -/
theorem factorTwoCenteredSymmetricPerturbationPolarization_self
    (w : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationPolarization w w =
      factorTwoCenteredSymmetricPerturbation w := by
  have hcorr (t : ℝ) : centeredEndpointCorrelation (w + w) t =
      4 * centeredEndpointCorrelation w t := by
    unfold centeredEndpointCorrelation
    rw [show (fun x : ℝ ↦ (w + w) (t + x) * (w + w) x) =
        fun x ↦ 4 * (w (t + x) * w x) by
      funext x
      simp only [Pi.add_apply]
      ring,
      intervalIntegral.integral_const_mul]
  unfold factorTwoCenteredSymmetricPerturbationPolarization
    factorTwoCenteredSymmetricPerturbation
  simp_rw [hcorr]
  rw [show (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
      (4 * centeredEndpointCorrelation w t)) =
      fun t ↦ 4 * (factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        centeredEndpointCorrelation w t) by
    funext t
    ring,
    intervalIntegral.integral_const_mul]
  ring

/-- Symmetry is exact and does not use any analytic estimate. -/
theorem factorTwoCenteredCorrelationBilinear_comm
    (u v : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredCorrelationBilinear u v t =
      factorTwoCenteredCorrelationBilinear v u t := by
  unfold factorTwoCenteredCorrelationBilinear
  ring

theorem factorTwoCenteredSymmetricPerturbationPolarization_comm
    (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationPolarization u v =
      factorTwoCenteredSymmetricPerturbationPolarization v u := by
  unfold factorTwoCenteredSymmetricPerturbationPolarization
  rw [add_comm]
  ring

/-- Ordered cross-correlation is additive in its left input for continuous
profiles. -/
theorem factorTwoCenteredCrossCorrelation_add_left
    (u v w : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) (t : ℝ) :
    factorTwoCenteredCrossCorrelation (u + v) w t =
      factorTwoCenteredCrossCorrelation u w t +
        factorTwoCenteredCrossCorrelation v w t := by
  have huInt : IntervalIntegrable (fun x : ℝ ↦ u (t + x) * w x)
      volume (-1) (1 - t) :=
    ((hu.comp (continuous_const.add continuous_id)).mul hw).intervalIntegrable _ _
  have hvInt : IntervalIntegrable (fun x : ℝ ↦ v (t + x) * w x)
      volume (-1) (1 - t) :=
    ((hv.comp (continuous_const.add continuous_id)).mul hw).intervalIntegrable _ _
  unfold factorTwoCenteredCrossCorrelation
  rw [show (fun x : ℝ ↦ (u + v) (t + x) * w x) =
      fun x ↦ u (t + x) * w x + v (t + x) * w x by
    funext x
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add huInt hvInt]

/-- Ordered cross-correlation is additive in its right input for continuous
profiles. -/
theorem factorTwoCenteredCrossCorrelation_add_right
    (u v w : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) (t : ℝ) :
    factorTwoCenteredCrossCorrelation u (v + w) t =
      factorTwoCenteredCrossCorrelation u v t +
        factorTwoCenteredCrossCorrelation u w t := by
  have hvInt : IntervalIntegrable (fun x : ℝ ↦ u (t + x) * v x)
      volume (-1) (1 - t) :=
    ((hu.comp (continuous_const.add continuous_id)).mul hv).intervalIntegrable _ _
  have hwInt : IntervalIntegrable (fun x : ℝ ↦ u (t + x) * w x)
      volume (-1) (1 - t) :=
    ((hu.comp (continuous_const.add continuous_id)).mul hw).intervalIntegrable _ _
  unfold factorTwoCenteredCrossCorrelation
  rw [show (fun x : ℝ ↦ u (t + x) * (v + w) x) =
      fun x ↦ u (t + x) * v x + u (t + x) * w x by
    funext x
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add hvInt hwInt]

/-- Ordered cross-correlation is homogeneous in its left input. -/
theorem factorTwoCenteredCrossCorrelation_smul_left
    (c : ℝ) (u v : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredCrossCorrelation (c • u) v t =
      c * factorTwoCenteredCrossCorrelation u v t := by
  unfold factorTwoCenteredCrossCorrelation
  rw [show (fun x : ℝ ↦ (c • u) (t + x) * v x) =
      fun x ↦ c * (u (t + x) * v x) by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring,
    intervalIntegral.integral_const_mul]

/-- Ordered cross-correlation is homogeneous in its right input. -/
theorem factorTwoCenteredCrossCorrelation_smul_right
    (c : ℝ) (u v : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredCrossCorrelation u (c • v) t =
      c * factorTwoCenteredCrossCorrelation u v t := by
  unfold factorTwoCenteredCrossCorrelation
  rw [show (fun x : ℝ ↦ u (t + x) * (c • v) x) =
      fun x ↦ c * (u (t + x) * v x) by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring,
    intervalIntegral.integral_const_mul]

/-- The fixed-unit affine quotient of an ordered centered cross-correlation
at the shrinking overlap endpoint. -/
def factorTwoCenteredCrossEndpointQuotient
    (u v : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ y : ℝ in 0..1,
    u (1 - r + r * y) * v (-1 + r * y)

/-- The endpoint quotient varies continuously for continuous profiles. -/
theorem continuous_factorTwoCenteredCrossEndpointQuotient
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    Continuous (factorTwoCenteredCrossEndpointQuotient u v) := by
  let phi : ℝ → ℝ → ℝ := fun r y ↦
    u (1 - r + r * y) * v (-1 + r * y)
  have hphi : Continuous phi.uncurry := by
    dsimp only [phi, Function.uncurry]
    fun_prop
  have hset : Continuous (fun r : ℝ ↦
      ∫ y : ℝ in Set.Icc (0 : ℝ) 1, phi r y) :=
    continuous_parametric_integral_of_continuous
      (μ := volume) hphi isCompact_Icc
  have heq : factorTwoCenteredCrossEndpointQuotient u v =
      fun r : ℝ ↦ ∫ y : ℝ in Set.Icc (0 : ℝ) 1, phi r y := by
    funext r
    unfold factorTwoCenteredCrossEndpointQuotient
    rw [intervalIntegral.integral_of_le (by norm_num),
      ← integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact hset

/-- The ordered cross-correlation vanishes by exactly the shrinking overlap
length at the reflected endpoint. -/
theorem factorTwoCenteredCrossCorrelation_two_sub_eq_mul_quotient
    (u v : ℝ → ℝ) (r : ℝ) :
    factorTwoCenteredCrossCorrelation u v (2 - r) =
      r * factorTwoCenteredCrossEndpointQuotient u v r := by
  let p : ℝ → ℝ := fun x ↦ u (2 - r + x) * v x
  have hsubst := intervalIntegral.smul_integral_comp_mul_add
    (a := (0 : ℝ)) (b := 1) p r (-1)
  have htransport :
      r * factorTwoCenteredCrossEndpointQuotient u v r =
        ∫ x : ℝ in -1..-1 + r, p x := by
    calc
      r * factorTwoCenteredCrossEndpointQuotient u v r =
          r * ∫ y : ℝ in 0..1, p (r * y + -1) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro y _hy
        dsimp only [p]
        congr 2 <;> ring
      _ = ∫ x : ℝ in r * 0 + -1..r * 1 + -1, p x := by
        simpa only [smul_eq_mul] using hsubst
      _ = ∫ x : ℝ in -1..-1 + r, p x := by
        simp only [mul_zero, zero_add, mul_one]
        congr 1
        ring
  unfold factorTwoCenteredCrossCorrelation
  rw [show 1 - (2 - r) = -1 + r by ring]
  change (∫ x : ℝ in -1..-1 + r, p x) = _
  exact htransport.symm

/-- Ordered centered cross-correlation is continuous in the shift for
continuous profiles. -/
theorem continuous_factorTwoCenteredCrossCorrelation
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    Continuous (factorTwoCenteredCrossCorrelation u v) := by
  have hquotient : Continuous (fun t : ℝ ↦
      factorTwoCenteredCrossEndpointQuotient u v (2 - t)) :=
    (continuous_factorTwoCenteredCrossEndpointQuotient u v hu hv).comp
      (continuous_const.sub continuous_id)
  have heq : factorTwoCenteredCrossCorrelation u v = fun t : ℝ ↦
      (2 - t) * factorTwoCenteredCrossEndpointQuotient u v (2 - t) := by
    funext t
    have hfactor :=
      factorTwoCenteredCrossCorrelation_two_sub_eq_mul_quotient
        u v (2 - t)
    simpa only [show 2 - (2 - t) = t by ring] using hfactor
  rw [heq]
  exact (continuous_const.sub continuous_id).mul hquotient

/-- Every ordered continuous cross-correlation divided by the shrinking
endpoint length is interval-integrable. -/
theorem intervalIntegrable_factorTwoCenteredCrossCorrelation_div_two_sub
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    IntervalIntegrable
      (fun t : ℝ ↦ factorTwoCenteredCrossCorrelation u v t / (2 - t))
      volume 0 2 := by
  have hquotient : Continuous (fun t : ℝ ↦
      factorTwoCenteredCrossEndpointQuotient u v (2 - t)) :=
    (continuous_factorTwoCenteredCrossEndpointQuotient u v hu hv).comp
      (continuous_const.sub continuous_id)
  apply (hquotient.intervalIntegrable 0 2).congr_ae
  refine ae_restrict_of_ae ?_
  filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 2 by
    simp [ae_iff, measure_singleton]] with t ht
  have hfactor :=
    factorTwoCenteredCrossCorrelation_two_sub_eq_mul_quotient
      u v (2 - t)
  rw [show 2 - (2 - t) = t by ring] at hfactor
  rw [hfactor]
  field_simp [sub_ne_zero.mpr (Ne.symm ht)]

/-- For every continuous profile pair, the complete singular alternating
kernel is interval-integrable.  The shrinking overlap supplies the zero that
cancels the reflected adjacent-kernel pole. -/
theorem intervalIntegrable_factorTwoCenteredAlternatingKernel
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    IntervalIntegrable
      (fun t : ℝ ↦
        factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
          (factorTwoCenteredCrossCorrelation v u t -
            factorTwoCenteredCrossCorrelation u v t))
      volume 0 2 := by
  let d : ℝ → ℝ := fun t ↦
    factorTwoCenteredCrossCorrelation v u t -
      factorTwoCenteredCrossCorrelation u v t
  let D : ℝ → ℝ := fun r ↦
    factorTwoCenteredCrossEndpointQuotient v u r -
      factorTwoCenteredCrossEndpointQuotient u v r
  have hd : Continuous d :=
    (continuous_factorTwoCenteredCrossCorrelation v u hv hu).sub
      (continuous_factorTwoCenteredCrossCorrelation u v hu hv)
  have hD : Continuous D :=
    (continuous_factorTwoCenteredCrossEndpointQuotient v u hv hu).sub
      (continuous_factorTwoCenteredCrossEndpointQuotient u v hu hv)
  have hdEndpoint (r : ℝ) : d (2 - r) = r * D r := by
    dsimp only [d, D]
    rw [factorTwoCenteredCrossCorrelation_two_sub_eq_mul_quotient,
      factorTwoCenteredCrossCorrelation_two_sub_eq_mul_quotient]
    ring
  have hregular : IntervalIntegrable
      (fun t : ℝ ↦
        factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + t)) * d t)
      volume 0 2 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have harg : yoshidaEndpointA * (2 + t) ≠ 0 := by
      exact mul_ne_zero yoshidaEndpointA_pos.ne'
        (by nlinarith [ht.1] : 2 + t ≠ 0)
    have hkernelMul : ContinuousAt (fun z : ℝ ↦
        factorTwoAdjacentSmoothKernel (yoshidaEndpointA * z)) (2 + t) :=
      (continuousAt_factorTwoAdjacentSmoothKernel_of_ne_zero harg).comp'
        (continuousAt_const.mul continuousAt_id)
    have hkernel : ContinuousAt (fun x : ℝ ↦
        factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + x))) t :=
      hkernelMul.comp' (continuousAt_const.add continuousAt_id)
    exact (hkernel.mul hd.continuousAt).continuousWithinAt
  let E : ℝ → ℝ := fun z ↦ D (z / yoshidaEndpointA) / yoshidaEndpointA
  have hE : Continuous E := by
    dsimp only [E]
    exact (hD.comp (continuous_id.div_const yoshidaEndpointA)).div_const
      yoshidaEndpointA
  have hoddBase := oddKernel_mul_u_intervalIntegrable hE
    (2 * yoshidaEndpointA)
  have hoddScaled := hoddBase.comp_mul_left (c := yoshidaEndpointA)
  have hoddScaled' : IntervalIntegrable
      (fun r : ℝ ↦
        oddKernel (yoshidaEndpointA * r) *
          (yoshidaEndpointA * r * E (yoshidaEndpointA * r)))
      volume 0 2 := by
    have hright : 2 * yoshidaEndpointA / yoshidaEndpointA = 2 := by
      field_simp [yoshidaEndpointA_pos.ne']
    simpa only [zero_div, hright] using hoddScaled
  have hodd : IntervalIntegrable
      (fun r : ℝ ↦
        oddKernel (yoshidaEndpointA * r) * (r * D r))
      volume 0 2 := by
    apply hoddScaled'.congr
    intro r _hr
    dsimp only [E]
    have hdiv : yoshidaEndpointA * r / yoshidaEndpointA = r := by
      field_simp [yoshidaEndpointA_pos.ne']
    rw [hdiv]
    field_simp [yoshidaEndpointA_pos.ne']
  have hcosh : IntervalIntegrable
      (fun r : ℝ ↦
        2 * Real.cosh (yoshidaEndpointA * r / 2) * (r * D r))
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.mul
      (Real.continuous_cosh.comp
        ((continuous_const.mul continuous_id).div_const 2))).mul
      (continuous_id.mul hD)
  have hreflectedKernel : IntervalIntegrable
      (fun r : ℝ ↦
        factorTwoAdjacentSmoothKernel (yoshidaEndpointA * r) *
          (r * D r))
      volume 0 2 := by
    have hsplit := hcosh.sub (hodd.const_mul (1 / 2 : ℝ))
    apply hsplit.congr
    intro r _hr
    unfold factorTwoAdjacentSmoothKernel
    ring
  have hreflected := hreflectedKernel.comp_sub_left 2
  have hreflected' : IntervalIntegrable
      (fun t : ℝ ↦
        factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 - t)) *
          ((2 - t) * D (2 - t)))
      volume 0 2 := by
    simpa only [sub_zero, sub_self] using hreflected.symm
  have hsingular : IntervalIntegrable
      (fun t : ℝ ↦
        factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 - t)) * d t)
      volume 0 2 := by
    apply hreflected'.congr
    intro t _ht
    have hfactor := hdEndpoint (2 - t)
    rw [show 2 - (2 - t) = t by ring] at hfactor
    change factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 - t)) *
        ((2 - t) * D (2 - t)) =
      factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 - t)) * d t
    rw [hfactor]
  have hsplit := hregular.sub hsingular
  apply hsplit.congr
  intro t _ht
  dsimp only [d]
  unfold factorTwoAntisymmetricWeight
  rw [factorTwoLogLength_eq_two_mul_yoshidaEndpointA]
  ring_nf

/-- Exact quadratic polarization of centered endpoint correlation. -/
theorem centeredEndpointCorrelation_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (t : ℝ) :
    centeredEndpointCorrelation (u + v) t =
      centeredEndpointCorrelation u t +
        2 * factorTwoCenteredCorrelationBilinear u v t +
      centeredEndpointCorrelation v t := by
  rw [← factorTwoCenteredCorrelationBilinear_self (u + v) t]
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_add_left u v (u + v) hu hv
      (hu.add hv) t,
    factorTwoCenteredCrossCorrelation_add_right u u v hu hu hv t,
    factorTwoCenteredCrossCorrelation_add_right v u v hv hu hv t,
    factorTwoCenteredCrossCorrelation_self u t,
    factorTwoCenteredCrossCorrelation_self v t]
  ring

/-- Exact quadratic polarization of the complete perturbation.  This is the
mixed term required by a cancellation-preserving low/tail Schur argument. -/
theorem factorTwoCenteredSymmetricPerturbation_add
    (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbation (u + v) =
      factorTwoCenteredSymmetricPerturbation u +
        2 * factorTwoCenteredSymmetricPerturbationPolarization u v +
      factorTwoCenteredSymmetricPerturbation v := by
  unfold factorTwoCenteredSymmetricPerturbationPolarization
  ring

/-! ## The alternating centered channel -/

/-- Two real supported critical pullbacks reduce their whole-line ordered
cross-correlation to the exact overlap interval. -/
theorem crossCorrelation_re_eq_interval_of_supported_real
    {a s : ℝ} (F G : SchwartzMap ℝ ℂ)
    (hFsupport : ∀ x ∉ Set.Icc (-a) a, F x = 0)
    (hGsupport : ∀ x ∉ Set.Icc (-a) a, G x = 0)
    (hFreal : ∀ x : ℝ, (F x).im = 0)
    (hGreal : ∀ x : ℝ, (G x).im = 0)
    (hs : s ≤ 2 * a) :
    (crossCorrelation (F : ℝ → ℂ) (G : ℝ → ℂ) s).re =
      ∫ x : ℝ in -a..a - s, (G (s + x)).re * (F x).re := by
  have hFreal' (x : ℝ) : F x = ((F x).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hFreal x
  have hGreal' (x : ℝ) : G x = ((G x).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hGreal x
  rw [crossCorrelation_apply]
  have hle : -a ≤ a - s := by linarith
  have hrestrict :
      (∫ x : ℝ, star (F x) * G (s + x)) =
        ∫ x : ℝ in -a..a - s, star (F x) * G (s + x) := by
    rw [intervalIntegral.integral_of_le hle,
      ← integral_Icc_eq_integral_Ioc]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      by_cases hxf : x ∈ Icc (-a) a
      · have hxgt : a - s < x := by
          by_contra hnot
          exact hx ⟨hxf.1, le_of_not_gt hnot⟩
        have hsx : s + x ∉ Icc (-a) a := by
          intro hmem
          linarith [hmem.2]
        rw [hGsupport (s + x) hsx, mul_zero]
      · rw [hFsupport x hxf, star_zero, zero_mul])).symm
  rw [hrestrict]
  have hrealIntegral :
      (∫ x : ℝ in -a..a - s, star (F x) * G (s + x)) =
        ((∫ x : ℝ in -a..a - s,
          (G (s + x)).re * (F x).re : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    change star (F x) * G (s + x) =
      (((G (s + x)).re * (F x).re : ℝ) : ℂ)
    rw [hFreal' x, hGreal' (s + x)]
    simp
    ring
  rw [hrealIntegral]
  rfl

/-- After endpoint rescaling, an ordered Bombieri critical correlation is the
centered ordered correlation with the exact Jacobian `yoshidaEndpointA`. -/
theorem bombieriCriticalCrossCorrelation_re_eq_endpoint_mul_centeredCross
    (u v : BombieriTest)
    (huSupport : YoshidaCriticalPullbackSupported yoshidaEndpointA u)
    (hvSupport : YoshidaCriticalPullbackSupported yoshidaEndpointA v)
    (huReal : ∀ x : ℝ,
      (u.logarithmicPullbackSchwartz (1 / 2) x).im = 0)
    (hvReal : ∀ x : ℝ,
      (v.logarithmicPullbackSchwartz (1 / 2) x).im = 0)
    {s : ℝ} (hs2 : s ≤ 2 * yoshidaEndpointA) :
    (bombieriCriticalCrossCorrelation u v s).re =
      yoshidaEndpointA *
        factorTwoCenteredCrossCorrelation
          (factorTwoCenteredProfile v) (factorTwoCenteredProfile u)
          (s / yoshidaEndpointA) := by
  let F : SchwartzMap ℝ ℂ :=
    u.logarithmicPullbackSchwartz (1 / 2)
  let G : SchwartzMap ℝ ℂ :=
    v.logarithmicPullbackSchwartz (1 / 2)
  let p : ℝ → ℝ := fun x ↦ (G (s + x)).re * (F x).re
  have hinterval := crossCorrelation_re_eq_interval_of_supported_real
    F G huSupport hvSupport huReal hvReal hs2
  change (bombieriCriticalCrossCorrelation u v s).re = _
  change (crossCorrelation (F : ℝ → ℂ) (G : ℝ → ℂ) s).re = _
  rw [hinterval]
  have hsubst := intervalIntegral.smul_integral_comp_mul_add
    (a := (-1 : ℝ)) (b := 1 - s / yoshidaEndpointA)
    p yoshidaEndpointA 0
  have htransport :
      (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA - s, p x) =
        yoshidaEndpointA *
          ∫ y : ℝ in -1..1 - s / yoshidaEndpointA,
            p (yoshidaEndpointA * y) := by
    calc
      (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA - s, p x) =
          ∫ x : ℝ in yoshidaEndpointA * (-1) + 0..
              yoshidaEndpointA * (1 - s / yoshidaEndpointA) + 0, p x := by
        congr 1 <;> field_simp [yoshidaEndpointA_pos.ne'] <;> ring
      _ = _ := by
        simpa only [smul_eq_mul, add_zero] using hsubst.symm
  change (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA - s, p x) = _
  rw [htransport]
  congr 1
  unfold factorTwoCenteredCrossCorrelation factorTwoCenteredProfile
  apply intervalIntegral.integral_congr
  intro y _hy
  dsimp only [p, F, G]
  congr 2
  field_simp [yoshidaEndpointA_pos.ne']

/-- The exact centered alternating channel.  Its ordered correlation
difference is the profile-level form of `factorTwoMixedParityCoupling`. -/
def factorTwoCenteredAlternatingCoupling (u v : ℝ → ℝ) : ℝ :=
  yoshidaEndpointA *
      (∫ t : ℝ in 0..2,
        factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
          (factorTwoCenteredCrossCorrelation v u t -
            factorTwoCenteredCrossCorrelation u v t)) -
    (Real.log 3 / Real.sqrt 3) *
      (factorTwoCenteredCrossCorrelation v u
          (factorTwoPrimeShift / yoshidaEndpointA) -
        factorTwoCenteredCrossCorrelation u v
          (factorTwoPrimeShift / yoshidaEndpointA))

/-- The centered alternating channel vanishes on the diagonal. -/
theorem factorTwoCenteredAlternatingCoupling_self (u : ℝ → ℝ) :
    factorTwoCenteredAlternatingCoupling u u = 0 := by
  unfold factorTwoCenteredAlternatingCoupling
  simp

/-- The centered alternating channel changes sign when its arguments are
exchanged. -/
theorem factorTwoCenteredAlternatingCoupling_comm
    (u v : ℝ → ℝ) :
    factorTwoCenteredAlternatingCoupling v u =
      -factorTwoCenteredAlternatingCoupling u v := by
  unfold factorTwoCenteredAlternatingCoupling
  rw [show (fun t : ℝ ↦
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation u v t -
          factorTwoCenteredCrossCorrelation v u t)) =
      fun t ↦ -(factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation v u t -
          factorTwoCenteredCrossCorrelation u v t)) by
    funext t
    ring,
    intervalIntegral.integral_neg]
  ring

/-- On continuous profiles, the complete alternating channel is additive in
its left input.  The singular integral is split only after both summands have
been placed in the interval-integrable form domain. -/
theorem factorTwoCenteredAlternatingCoupling_add_left
    (u₁ u₂ v : ℝ → ℝ)
    (hu₁ : Continuous u₁) (hu₂ : Continuous u₂) (hv : Continuous v) :
    factorTwoCenteredAlternatingCoupling (u₁ + u₂) v =
      factorTwoCenteredAlternatingCoupling u₁ v +
        factorTwoCenteredAlternatingCoupling u₂ v := by
  have h₁ := intervalIntegrable_factorTwoCenteredAlternatingKernel
    u₁ v hu₁ hv
  have h₂ := intervalIntegrable_factorTwoCenteredAlternatingKernel
    u₂ v hu₂ hv
  unfold factorTwoCenteredAlternatingCoupling
  rw [show (fun t : ℝ ↦
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation v (u₁ + u₂) t -
          factorTwoCenteredCrossCorrelation (u₁ + u₂) v t)) =
      fun t ↦
        factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            (factorTwoCenteredCrossCorrelation v u₁ t -
              factorTwoCenteredCrossCorrelation u₁ v t) +
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            (factorTwoCenteredCrossCorrelation v u₂ t -
              factorTwoCenteredCrossCorrelation u₂ v t) by
    funext t
    rw [factorTwoCenteredCrossCorrelation_add_right
        v u₁ u₂ hv hu₁ hu₂ t,
      factorTwoCenteredCrossCorrelation_add_left
        u₁ u₂ v hu₁ hu₂ hv t]
    ring,
    intervalIntegral.integral_add h₁ h₂,
    factorTwoCenteredCrossCorrelation_add_right
      v u₁ u₂ hv hu₁ hu₂,
    factorTwoCenteredCrossCorrelation_add_left
      u₁ u₂ v hu₁ hu₂ hv]
  ring

/-- On continuous profiles, the complete alternating channel is additive in
its right input. -/
theorem factorTwoCenteredAlternatingCoupling_add_right
    (u v₁ v₂ : ℝ → ℝ)
    (hu : Continuous u) (hv₁ : Continuous v₁) (hv₂ : Continuous v₂) :
    factorTwoCenteredAlternatingCoupling u (v₁ + v₂) =
      factorTwoCenteredAlternatingCoupling u v₁ +
        factorTwoCenteredAlternatingCoupling u v₂ := by
  calc
    factorTwoCenteredAlternatingCoupling u (v₁ + v₂) =
        -factorTwoCenteredAlternatingCoupling (v₁ + v₂) u :=
      factorTwoCenteredAlternatingCoupling_comm (v₁ + v₂) u
    _ = -(factorTwoCenteredAlternatingCoupling v₁ u +
          factorTwoCenteredAlternatingCoupling v₂ u) := by
      rw [factorTwoCenteredAlternatingCoupling_add_left
        v₁ v₂ u hv₁ hv₂ hu]
    _ = factorTwoCenteredAlternatingCoupling u v₁ +
        factorTwoCenteredAlternatingCoupling u v₂ := by
      rw [factorTwoCenteredAlternatingCoupling_comm u v₁,
        factorTwoCenteredAlternatingCoupling_comm u v₂]
      ring

/-- The complete alternating channel is homogeneous in its left input. -/
theorem factorTwoCenteredAlternatingCoupling_smul_left
    (c : ℝ) (u v : ℝ → ℝ) :
    factorTwoCenteredAlternatingCoupling (c • u) v =
      c * factorTwoCenteredAlternatingCoupling u v := by
  unfold factorTwoCenteredAlternatingCoupling
  rw [show (fun t : ℝ ↦
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation v (c • u) t -
          factorTwoCenteredCrossCorrelation (c • u) v t)) =
      fun t ↦ c *
        (factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
          (factorTwoCenteredCrossCorrelation v u t -
            factorTwoCenteredCrossCorrelation u v t)) by
    funext t
    rw [factorTwoCenteredCrossCorrelation_smul_right,
      factorTwoCenteredCrossCorrelation_smul_left]
    ring,
    intervalIntegral.integral_const_mul,
    factorTwoCenteredCrossCorrelation_smul_right,
    factorTwoCenteredCrossCorrelation_smul_left]
  ring

/-- The complete alternating channel is homogeneous in its right input. -/
theorem factorTwoCenteredAlternatingCoupling_smul_right
    (c : ℝ) (u v : ℝ → ℝ) :
    factorTwoCenteredAlternatingCoupling u (c • v) =
      c * factorTwoCenteredAlternatingCoupling u v := by
  calc
    factorTwoCenteredAlternatingCoupling u (c • v) =
        -factorTwoCenteredAlternatingCoupling (c • v) u :=
      factorTwoCenteredAlternatingCoupling_comm (c • v) u
    _ = -(c * factorTwoCenteredAlternatingCoupling v u) := by
      rw [factorTwoCenteredAlternatingCoupling_smul_left]
    _ = c * factorTwoCenteredAlternatingCoupling u v := by
      rw [factorTwoCenteredAlternatingCoupling_comm u v]
      ring

/-- For two real critical pullbacks on the endpoint interval, the production
alternating mixed coordinate is exactly the endpoint scale times the centered
alternating channel. -/
theorem factorTwoMixedParityCoupling_eq_endpoint_mul_centeredAlternating
    (u v : BombieriTest)
    (huSupport : YoshidaCriticalPullbackSupported yoshidaEndpointA u)
    (hvSupport : YoshidaCriticalPullbackSupported yoshidaEndpointA v)
    (huReal : ∀ x : ℝ,
      (u.logarithmicPullbackSchwartz (1 / 2) x).im = 0)
    (hvReal : ∀ x : ℝ,
      (v.logarithmicPullbackSchwartz (1 / 2) x).im = 0) :
    factorTwoMixedParityCoupling u v =
      yoshidaEndpointA *
        factorTwoCenteredAlternatingCoupling
          (factorTwoCenteredProfile u) (factorTwoCenteredProfile v) := by
  let q : ℝ → ℝ := fun s ↦
    factorTwoAntisymmetricWeight s *
      ((bombieriCriticalCrossCorrelation u v s).re -
        (bombieriCriticalCrossCorrelation v u s).re)
  have huv {s : ℝ} (hs : s ≤ 2 * yoshidaEndpointA) :=
    bombieriCriticalCrossCorrelation_re_eq_endpoint_mul_centeredCross
      u v huSupport hvSupport huReal hvReal hs
  have hvu {s : ℝ} (hs : s ≤ 2 * yoshidaEndpointA) :=
    bombieriCriticalCrossCorrelation_re_eq_endpoint_mul_centeredCross
      v u hvSupport huSupport hvReal huReal hs
  have hsubst := intervalIntegral.smul_integral_comp_mul_add
    (a := (0 : ℝ)) (b := 2) q yoshidaEndpointA 0
  have hchange :
      (∫ s : ℝ in 0..2 * yoshidaEndpointA, q s) =
        yoshidaEndpointA *
          ∫ t : ℝ in 0..2, q (yoshidaEndpointA * t) := by
    simpa only [smul_eq_mul, mul_zero, zero_add, add_zero, mul_comm]
      using hsubst.symm
  have hintegral :
      (∫ s : ℝ in 0..2 * yoshidaEndpointA, q s) =
        yoshidaEndpointA ^ 2 *
          ∫ t : ℝ in 0..2,
            factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
              (factorTwoCenteredCrossCorrelation
                  (factorTwoCenteredProfile v)
                  (factorTwoCenteredProfile u) t -
                factorTwoCenteredCrossCorrelation
                  (factorTwoCenteredProfile u)
                  (factorTwoCenteredProfile v) t) := by
    rw [hchange]
    have hinner :
        (∫ t : ℝ in 0..2, q (yoshidaEndpointA * t)) =
          ∫ t : ℝ in 0..2,
            yoshidaEndpointA *
              (factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
                (factorTwoCenteredCrossCorrelation
                    (factorTwoCenteredProfile v)
                    (factorTwoCenteredProfile u) t -
                  factorTwoCenteredCrossCorrelation
                    (factorTwoCenteredProfile u)
                    (factorTwoCenteredProfile v) t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
      have hst : yoshidaEndpointA * t ≤ 2 * yoshidaEndpointA := by
        nlinarith [ht.2, yoshidaEndpointA_pos]
      dsimp only [q]
      rw [huv hst, hvu hst]
      have hdiv : yoshidaEndpointA * t / yoshidaEndpointA = t := by
        field_simp [yoshidaEndpointA_pos.ne']
      rw [hdiv]
      ring
    rw [hinner, intervalIntegral.integral_const_mul]
    ring
  have hprimeUV := huv factorTwoPrimeShift_mem_endpointInterval.2
  have hprimeVU := hvu factorTwoPrimeShift_mem_endpointInterval.2
  unfold factorTwoMixedParityCoupling
    factorTwoCenteredAlternatingCoupling
  rw [factorTwoLogLength_eq_two_mul_yoshidaEndpointA]
  change (∫ s : ℝ in 0..2 * yoshidaEndpointA, q s) - _ = _
  rw [hintegral, hprimeUV, hprimeVU]
  ring

/-- The two signed centered endpoint energies. -/
def factorTwoCenteredEndpointPlus (w : ℝ → ℝ) : ℝ :=
  yoshidaEndpointOddCleanQuadratic w +
    factorTwoCenteredSymmetricPerturbation w

def factorTwoCenteredEndpointMinus (w : ℝ → ℝ) : ℝ :=
  yoshidaEndpointOddCleanQuadratic w -
    factorTwoCenteredSymmetricPerturbation w

/-! ## The exact scalar pencil -/

/-- A real binary quadratic pencil is nonnegative in every scalar direction
exactly when both diagonal coefficients are nonnegative and its determinant
is nonnegative. -/
theorem real_quadratic_pencil_nonneg_iff (A B C : ℝ) :
    (∀ r s : ℝ, 0 ≤ A * r ^ 2 + 2 * C * r * s + B * s ^ 2) ↔
      0 ≤ A ∧ 0 ≤ B ∧ C ^ 2 ≤ A * B := by
  constructor
  · intro h
    have hA : 0 ≤ A := by simpa using h 1 0
    have hB : 0 ≤ B := by simpa using h 0 1
    refine ⟨hA, hB, ?_⟩
    by_cases hB0 : B = 0
    · subst B
      by_cases hA0 : A = 0
      · subst A
        have hp := h 1 1
        have hm := h 1 (-1)
        have hC : C = 0 := by
          norm_num at hp hm
          linarith
        simp [hC]
      · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
        have hz : 0 ≤ A * (A * 0 - C ^ 2) := by
          convert h C (-A) using 1
          ring
        by_contra hn
        have hneg : A * 0 - C ^ 2 < 0 := by linarith
        exact (not_lt_of_ge hz) (mul_neg_of_pos_of_neg hApos hneg)
    · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
      have hz : 0 ≤ B * (A * B - C ^ 2) := by
        convert h B (-C) using 1
        ring
      by_contra hn
      have hneg : A * B - C ^ 2 < 0 := by linarith
      exact (not_lt_of_ge hz) (mul_neg_of_pos_of_neg hBpos hneg)
  · rintro ⟨hA, hB, hdet⟩ r s
    by_cases hA0 : A = 0
    · subst A
      have hC : C = 0 := by nlinarith [sq_nonneg C]
      subst C
      simpa using mul_nonneg hB (sq_nonneg s)
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
      have hgap : 0 ≤ A * B - C ^ 2 := by linarith
      have hscaled :
          0 ≤ A * (A * r ^ 2 + 2 * C * r * s + B * s ^ 2) := by
        rw [show A * (A * r ^ 2 + 2 * C * r * s + B * s ^ 2) =
            (A * r + C * s) ^ 2 + (A * B - C ^ 2) * s ^ 2 by ring]
        exact add_nonneg (sq_nonneg _)
          (mul_nonneg hgap (sq_nonneg s))
      exact nonneg_of_mul_nonneg_left
        (by simpa [mul_comm] using hscaled) hApos

/-- For fixed centered profiles with nonnegative signed endpoint energies,
the sharp product bound is exactly positivity of the scalar mixed pencil.
The mixed coefficient is `2 * r * s * J`. -/
theorem factorTwoCenteredAlternating_sq_le_product_iff_scalarPencil
    (u v : ℝ → ℝ)
    (hplus : 0 ≤ factorTwoCenteredEndpointPlus u +
      factorTwoCenteredEndpointPlus v)
    (hminus : 0 ≤ factorTwoCenteredEndpointMinus u +
      factorTwoCenteredEndpointMinus v) :
    factorTwoCenteredAlternatingCoupling u v ^ 2 ≤
        (factorTwoCenteredEndpointPlus u +
          factorTwoCenteredEndpointPlus v) *
        (factorTwoCenteredEndpointMinus u +
          factorTwoCenteredEndpointMinus v) ↔
      ∀ r s : ℝ,
        0 ≤ (factorTwoCenteredEndpointPlus u +
              factorTwoCenteredEndpointPlus v) * r ^ 2 +
            2 * factorTwoCenteredAlternatingCoupling u v * r * s +
            (factorTwoCenteredEndpointMinus u +
              factorTwoCenteredEndpointMinus v) * s ^ 2 := by
  let A := factorTwoCenteredEndpointPlus u +
    factorTwoCenteredEndpointPlus v
  let B := factorTwoCenteredEndpointMinus u +
    factorTwoCenteredEndpointMinus v
  let C := factorTwoCenteredAlternatingCoupling u v
  have hpencil := real_quadratic_pencil_nonneg_iff A B C
  change C ^ 2 ≤ A * B ↔ ∀ r s : ℝ,
    0 ≤ A * r ^ 2 + 2 * C * r * s + B * s ^ 2
  constructor
  · intro hdet
    exact hpencil.mpr ⟨hplus, hminus, hdet⟩
  · intro hp
    exact (hpencil.mp hp).2.2

/-- The antisymmetric folded coordinate is invariant under normalized
multiplicative dilation. -/
theorem factorTwoAntisymmetricCoordinate_normalizedDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    factorTwoAntisymmetricCoordinate
        (normalizedDilation lambda hlambda g) =
      factorTwoAntisymmetricCoordinate g := by
  unfold factorTwoAntisymmetricCoordinate
  simp_rw [factorTwoSelfCorrelation_normalizedDilation lambda hlambda g]

/-- Canonical logarithmic centering puts the full alternating production
coordinate into the same two real profile coordinates as the signed endpoint
energies. -/
theorem factorTwoAntisymmetricCoordinate_eq_logCentered_profiles
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    let gc := normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g
    factorTwoAntisymmetricCoordinate g =
      yoshidaEndpointA *
        factorTwoCenteredAlternatingCoupling
          (factorTwoCenteredProfile (bombieriRealPartTest gc))
          (factorTwoCenteredProfile (bombieriImagPartTest gc)) := by
  let lambda : ℝ := logarithmicCenter a b
  have hlambda : 0 < lambda := logarithmicCenter_pos a b
  let gc : BombieriTest := normalizedDilation lambda hlambda g
  have hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA gc := by
    simpa only [gc, lambda, hlambda] using
      logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaEndpointA
        g ha hab hsupport hratio
  have huCritical := bombieriRealPartTest_criticalPullbackSupported
    gc hcritical
  have hvCritical := bombieriImagPartTest_criticalPullbackSupported
    gc hcritical
  have hcentered :=
    factorTwoMixedParityCoupling_eq_endpoint_mul_centeredAlternating
      (bombieriRealPartTest gc) (bombieriImagPartTest gc)
      huCritical hvCritical
      (bombieriRealPartTest_criticalPullback_im_eq_zero gc)
      (bombieriImagPartTest_criticalPullback_im_eq_zero gc)
  calc
    factorTwoAntisymmetricCoordinate g =
        factorTwoAntisymmetricCoordinate gc := by
      simpa only [gc] using
        (factorTwoAntisymmetricCoordinate_normalizedDilation
          lambda hlambda g).symm
    _ = factorTwoMixedParityCoupling
          (bombieriRealPartTest gc) (bombieriImagPartTest gc) :=
      factorTwoAntisymmetricCoordinate_eq_realImag gc
    _ = _ := hcentered

/-- On a canonical ratio-two profile pair, the sharp alternating product
bound forces both signed endpoint-energy sums to be nonnegative.  This uses
the already structural restricted-support positivity of the diagonal. -/
theorem factorTwoCenteredEndpoint_sums_nonneg_of_alternating_sq_le_product
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    let gc := normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g
    let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
    let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
    factorTwoCenteredAlternatingCoupling u v ^ 2 ≤
        (factorTwoCenteredEndpointPlus u +
          factorTwoCenteredEndpointPlus v) *
        (factorTwoCenteredEndpointMinus u +
          factorTwoCenteredEndpointMinus v) →
      0 ≤ factorTwoCenteredEndpointPlus u +
          factorTwoCenteredEndpointPlus v ∧
        0 ≤ factorTwoCenteredEndpointMinus u +
          factorTwoCenteredEndpointMinus v := by
  let lambda : ℝ := logarithmicCenter a b
  have hlambda : 0 < lambda := logarithmicCenter_pos a b
  let gc : BombieriTest := normalizedDilation lambda hlambda g
  let u : ℝ → ℝ := factorTwoCenteredProfile (bombieriRealPartTest gc)
  let v : ℝ → ℝ := factorTwoCenteredProfile (bombieriImagPartTest gc)
  let Eplus : ℝ := factorTwoCenteredEndpointPlus u +
    factorTwoCenteredEndpointPlus v
  let Eminus : ℝ := factorTwoCenteredEndpointMinus u +
    factorTwoCenteredEndpointMinus v
  let J : ℝ := factorTwoCenteredAlternatingCoupling u v
  have hplus0 := factorTwoDiagonal_add_symmetric_eq_logCentered_two_profiles
    g ha hab hsupport hratio
  have hminus0 := factorTwoDiagonal_sub_symmetric_eq_logCentered_two_profiles
    g ha hab hsupport hratio
  have hplus : factorTwoDiagonalCoordinate g +
      factorTwoSymmetricCoordinate g = yoshidaEndpointA * Eplus := by
    simpa only [gc, lambda, hlambda, u, v, Eplus,
      factorTwoCenteredEndpointPlus] using hplus0
  have hminus : factorTwoDiagonalCoordinate g -
      factorTwoSymmetricCoordinate g = yoshidaEndpointA * Eminus := by
    simpa only [gc, lambda, hlambda, u, v, Eminus,
      factorTwoCenteredEndpointMinus] using hminus0
  have hDiagonalFunctional :=
    bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
      g ha hab hsupport hratio
  change (bombieriFunctional (bombieriQuadraticTest g)).re =
    factorTwoDiagonalCoordinate g at hDiagonalFunctional
  have hD : 0 ≤ factorTwoDiagonalCoordinate g := by
    rw [← hDiagonalFunctional]
    exact bombieriFunctional_quadratic_re_nonneg_of_ratio_le_two
      g ha hab hsupport hratio
  have hsumEq : yoshidaEndpointA * (Eplus + Eminus) =
      2 * factorTwoDiagonalCoordinate g := by
    calc
      yoshidaEndpointA * (Eplus + Eminus) =
          yoshidaEndpointA * Eplus + yoshidaEndpointA * Eminus := by ring
      _ = (factorTwoDiagonalCoordinate g +
            factorTwoSymmetricCoordinate g) +
          (factorTwoDiagonalCoordinate g -
            factorTwoSymmetricCoordinate g) := by rw [← hplus, ← hminus]
      _ = 2 * factorTwoDiagonalCoordinate g := by ring
  have hsumScaled : 0 ≤ yoshidaEndpointA * (Eplus + Eminus) := by
    rw [hsumEq]
    positivity
  have hsum : 0 ≤ Eplus + Eminus :=
    nonneg_of_mul_nonneg_left
      (by simpa [mul_comm] using hsumScaled) yoshidaEndpointA_pos
  dsimp only
  change J ^ 2 ≤ Eplus * Eminus → 0 ≤ Eplus ∧ 0 ≤ Eminus
  intro hdet
  have hprod : 0 ≤ Eplus * Eminus := (sq_nonneg J).trans hdet
  constructor
  · by_contra hnot
    have hEplusNeg : Eplus < 0 := lt_of_not_ge hnot
    have hEminusPos : 0 < Eminus := by linarith
    exact (not_lt_of_ge hprod)
      (mul_neg_of_neg_of_pos hEplusNeg hEminusPos)
  · by_contra hnot
    have hEminusNeg : Eminus < 0 := lt_of_not_ge hnot
    have hEplusPos : 0 < Eplus := by linarith
    exact (not_lt_of_ge hprod)
      (mul_neg_of_pos_of_neg hEplusPos hEminusNeg)

/-- On the canonical centered profile pair, the singular alternating kernel
is genuinely interval-integrable.  This is the analytic form-domain fact
needed before the centered channel may be used as a bilinear Schur form. -/
theorem intervalIntegrable_centeredAlternatingKernel_logCentered_profiles
    (g : BombieriTest) (a b : ℝ) :
    let gc := normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g
    let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
    let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
    IntervalIntegrable
      (fun t : ℝ ↦
        factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
          (factorTwoCenteredCrossCorrelation v u t -
            factorTwoCenteredCrossCorrelation u v t))
      volume 0 2 := by
  dsimp only
  apply intervalIntegrable_factorTwoCenteredAlternatingKernel
  · unfold factorTwoCenteredProfile
    fun_prop
  · unfold factorTwoCenteredProfile
    fun_prop

/-- The exact folded determinant inequality is equivalent, after cancelling
the positive endpoint-scale square, to the product of the two signed centered
endpoint energies dominating the centered alternating square. -/
theorem factorTwo_folded_determinant_iff_logCentered_profiles
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    let gc := normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g
    let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
    let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
    factorTwoSymmetricCoordinate g ^ 2 +
          factorTwoAntisymmetricCoordinate g ^ 2 ≤
        factorTwoDiagonalCoordinate g ^ 2 ↔
      factorTwoCenteredAlternatingCoupling u v ^ 2 ≤
        (factorTwoCenteredEndpointPlus u +
          factorTwoCenteredEndpointPlus v) *
        (factorTwoCenteredEndpointMinus u +
          factorTwoCenteredEndpointMinus v) := by
  let lambda : ℝ := logarithmicCenter a b
  have hlambda : 0 < lambda := logarithmicCenter_pos a b
  let gc : BombieriTest := normalizedDilation lambda hlambda g
  let u : ℝ → ℝ := factorTwoCenteredProfile (bombieriRealPartTest gc)
  let v : ℝ → ℝ := factorTwoCenteredProfile (bombieriImagPartTest gc)
  let Eplus : ℝ := factorTwoCenteredEndpointPlus u +
    factorTwoCenteredEndpointPlus v
  let Eminus : ℝ := factorTwoCenteredEndpointMinus u +
    factorTwoCenteredEndpointMinus v
  let J : ℝ := factorTwoCenteredAlternatingCoupling u v
  have hplus0 := factorTwoDiagonal_add_symmetric_eq_logCentered_two_profiles
    g ha hab hsupport hratio
  have hminus0 := factorTwoDiagonal_sub_symmetric_eq_logCentered_two_profiles
    g ha hab hsupport hratio
  have hJ0 := factorTwoAntisymmetricCoordinate_eq_logCentered_profiles
    g ha hab hsupport hratio
  have hplus : factorTwoDiagonalCoordinate g +
      factorTwoSymmetricCoordinate g = yoshidaEndpointA * Eplus := by
    simpa only [gc, lambda, hlambda, u, v, Eplus,
      factorTwoCenteredEndpointPlus] using hplus0
  have hminus : factorTwoDiagonalCoordinate g -
      factorTwoSymmetricCoordinate g = yoshidaEndpointA * Eminus := by
    simpa only [gc, lambda, hlambda, u, v, Eminus,
      factorTwoCenteredEndpointMinus] using hminus0
  have hJ : factorTwoAntisymmetricCoordinate g =
      yoshidaEndpointA * J := by
    simpa only [gc, lambda, hlambda, u, v, J] using hJ0
  have hAsq : 0 < yoshidaEndpointA ^ 2 := sq_pos_of_pos yoshidaEndpointA_pos
  dsimp only
  change factorTwoSymmetricCoordinate g ^ 2 +
        factorTwoAntisymmetricCoordinate g ^ 2 ≤
      factorTwoDiagonalCoordinate g ^ 2 ↔ J ^ 2 ≤ Eplus * Eminus
  constructor
  · intro hdet
    have hprod : factorTwoAntisymmetricCoordinate g ^ 2 ≤
        (factorTwoDiagonalCoordinate g + factorTwoSymmetricCoordinate g) *
          (factorTwoDiagonalCoordinate g -
            factorTwoSymmetricCoordinate g) := by
      nlinarith
    rw [hJ, hplus, hminus] at hprod
    have hscaled : yoshidaEndpointA ^ 2 * J ^ 2 ≤
        yoshidaEndpointA ^ 2 * (Eplus * Eminus) := by
      calc
        yoshidaEndpointA ^ 2 * J ^ 2 =
            (yoshidaEndpointA * J) ^ 2 := by ring
        _ ≤ (yoshidaEndpointA * Eplus) *
            (yoshidaEndpointA * Eminus) := hprod
        _ = yoshidaEndpointA ^ 2 * (Eplus * Eminus) := by ring
    exact le_of_mul_le_mul_left hscaled hAsq
  · intro hcentered
    have hscaled : yoshidaEndpointA ^ 2 * J ^ 2 ≤
        yoshidaEndpointA ^ 2 * (Eplus * Eminus) :=
      mul_le_mul_of_nonneg_left hcentered hAsq.le
    have hprod : factorTwoAntisymmetricCoordinate g ^ 2 ≤
        (factorTwoDiagonalCoordinate g + factorTwoSymmetricCoordinate g) *
          (factorTwoDiagonalCoordinate g -
            factorTwoSymmetricCoordinate g) := by
      rw [hJ, hplus, hminus]
      calc
        (yoshidaEndpointA * J) ^ 2 =
            yoshidaEndpointA ^ 2 * J ^ 2 := by ring
        _ ≤ yoshidaEndpointA ^ 2 * (Eplus * Eminus) := hscaled
        _ = (yoshidaEndpointA * Eplus) *
            (yoshidaEndpointA * Eminus) := by ring
    nlinarith

/-- The strict reverse of the folded determinant is the strict reverse of the
single centered profile-product inequality. -/
theorem factorTwo_folded_determinant_strict_iff_logCentered_profiles
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    let gc := normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g
    let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
    let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
    factorTwoDiagonalCoordinate g ^ 2 <
        factorTwoSymmetricCoordinate g ^ 2 +
          factorTwoAntisymmetricCoordinate g ^ 2 ↔
      (factorTwoCenteredEndpointPlus u +
          factorTwoCenteredEndpointPlus v) *
        (factorTwoCenteredEndpointMinus u +
          factorTwoCenteredEndpointMinus v) <
        factorTwoCenteredAlternatingCoupling u v ^ 2 := by
  have hdet := factorTwo_folded_determinant_iff_logCentered_profiles
    g ha hab hsupport hratio
  dsimp only at hdet ⊢
  constructor
  · intro hstrict
    rw [← not_le]
    intro hcentered
    exact (not_le.mpr hstrict) (hdet.mpr hcentered)
  · intro hstrict
    rw [← not_le]
    intro hfolded
    exact (not_le.mpr hstrict) (hdet.mp hfolded)

/-- Universal same-seed factor-two Bombieri positivity is now exactly one
inequality between the two complete signed endpoint energies and the complete
alternating centered channel. -/
theorem bombieriFunctional_twoBump_nonneg_iff_logCentered_profiles
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re) ↔
      let gc := normalizedDilation (logarithmicCenter a b)
        (logarithmicCenter_pos a b) g
      let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
      let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
      factorTwoCenteredAlternatingCoupling u v ^ 2 ≤
        (factorTwoCenteredEndpointPlus u +
          factorTwoCenteredEndpointPlus v) *
        (factorTwoCenteredEndpointMinus u +
          factorTwoCenteredEndpointMinus v) := by
  have hfold := bombieriFunctional_twoBump_nonneg_iff_foldedParity
    g ha hab hsupport hratio
  change
    (∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re) ↔
      factorTwoSymmetricCoordinate g ^ 2 +
          factorTwoAntisymmetricCoordinate g ^ 2 ≤
        factorTwoDiagonalCoordinate g ^ 2 at hfold
  exact hfold.trans
    (factorTwo_folded_determinant_iff_logCentered_profiles
      g ha hab hsupport hratio)

/-- Universal same-seed factor-two positivity is equivalently positivity of
one sharp real scalar pencil on the fixed canonical profile pair.  This is the
exact mixed-channel analytic obligation; it is weaker than a row contraction
quantified over independent profile pairs. -/
theorem bombieriFunctional_twoBump_nonneg_iff_logCentered_scalarPencil
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re) ↔
      let gc := normalizedDilation (logarithmicCenter a b)
        (logarithmicCenter_pos a b) g
      let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
      let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
      ∀ r s : ℝ,
        0 ≤ (factorTwoCenteredEndpointPlus u +
              factorTwoCenteredEndpointPlus v) * r ^ 2 +
            2 * factorTwoCenteredAlternatingCoupling u v * r * s +
            (factorTwoCenteredEndpointMinus u +
              factorTwoCenteredEndpointMinus v) * s ^ 2 := by
  let gc := normalizedDilation (logarithmicCenter a b)
    (logarithmicCenter_pos a b) g
  let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
  let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
  let A := factorTwoCenteredEndpointPlus u +
    factorTwoCenteredEndpointPlus v
  let B := factorTwoCenteredEndpointMinus u +
    factorTwoCenteredEndpointMinus v
  let C := factorTwoCenteredAlternatingCoupling u v
  have hproduct0 :=
    bombieriFunctional_twoBump_nonneg_iff_logCentered_profiles
      g ha hab hsupport hratio
  have hproduct :
      (∀ c : ℂ,
        0 ≤ (bombieriFunctional
          (bombieriQuadraticTest
            (g + c • normalizedDilation 2 (by norm_num) g))).re) ↔
        C ^ 2 ≤ A * B := by
    simpa only [gc, u, v, A, B, C] using hproduct0
  have hnonneg0 :=
    factorTwoCenteredEndpoint_sums_nonneg_of_alternating_sq_le_product
      g ha hab hsupport hratio
  have hnonneg : C ^ 2 ≤ A * B → 0 ≤ A ∧ 0 ≤ B := by
    simpa only [gc, u, v, A, B, C] using hnonneg0
  have hpencil := real_quadratic_pencil_nonneg_iff A B C
  dsimp only
  change
    (∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re) ↔
      ∀ r s : ℝ,
        0 ≤ A * r ^ 2 + 2 * C * r * s + B * s ^ 2
  constructor
  · intro hfamily
    have hdet := hproduct.mp hfamily
    have hsign := hnonneg hdet
    exact hpencil.mpr ⟨hsign.1, hsign.2, hdet⟩
  · intro hp
    exact hproduct.mpr (hpencil.mp hp).2.2

/-- A strict reverse of the centered profile-product inequality is exactly the
existence of a negative member of the production two-bump family. -/
theorem exists_bombieriFunctional_twoBump_neg_iff_logCentered_profiles
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∃ c : ℂ,
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re < 0) ↔
      let gc := normalizedDilation (logarithmicCenter a b)
        (logarithmicCenter_pos a b) g
      let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
      let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
      (factorTwoCenteredEndpointPlus u +
          factorTwoCenteredEndpointPlus v) *
        (factorTwoCenteredEndpointMinus u +
          factorTwoCenteredEndpointMinus v) <
        factorTwoCenteredAlternatingCoupling u v ^ 2 := by
  have hfold := exists_bombieriFunctional_twoBump_neg_iff_foldedParity
    g ha hab hsupport hratio
  change
    (∃ c : ℂ,
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re < 0) ↔
      factorTwoDiagonalCoordinate g ^ 2 <
        factorTwoSymmetricCoordinate g ^ 2 +
          factorTwoAntisymmetricCoordinate g ^ 2 at hfold
  exact hfold.trans
    (factorTwo_folded_determinant_strict_iff_logCentered_profiles
      g ha hab hsupport hratio)

/-- A negative production member exists exactly when the sharp centered
scalar pencil has a negative real direction. -/
theorem exists_bombieriFunctional_twoBump_neg_iff_logCentered_scalarPencil
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∃ c : ℂ,
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re < 0) ↔
      let gc := normalizedDilation (logarithmicCenter a b)
        (logarithmicCenter_pos a b) g
      let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
      let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
      ∃ r s : ℝ,
        (factorTwoCenteredEndpointPlus u +
              factorTwoCenteredEndpointPlus v) * r ^ 2 +
            2 * factorTwoCenteredAlternatingCoupling u v * r * s +
            (factorTwoCenteredEndpointMinus u +
              factorTwoCenteredEndpointMinus v) * s ^ 2 < 0 := by
  have hnonneg :=
    bombieriFunctional_twoBump_nonneg_iff_logCentered_scalarPencil
      g ha hab hsupport hratio
  dsimp only at hnonneg ⊢
  constructor
  · rintro ⟨c, hc⟩
    by_contra hnoDirection
    push_neg at hnoDirection
    have hfamily := hnonneg.mpr hnoDirection
    exact (not_le_of_gt hc) (hfamily c)
  · rintro ⟨r, s, hrs⟩
    by_contra hnoMember
    push_neg at hnoMember
    have hpencil := hnonneg.mp hnoMember
    exact (not_le_of_gt hrs) (hpencil r s)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointBilinear
