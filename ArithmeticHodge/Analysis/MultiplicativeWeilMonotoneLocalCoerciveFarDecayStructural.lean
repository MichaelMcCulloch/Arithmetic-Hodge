import ArithmeticHodge.Analysis.MultiplicativeWeilSeparatedCellCrossStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilRestrictedSupportEndpointPositive
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedQuantitativeCoercivity
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailCoercivity

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneLocalCoerciveFarDecayStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilDirectedCorrelationSmoothStructural
open MultiplicativeWeilSeparatedCellCrossStructural
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointScaledCorrelation
open YoshidaOddHomogeneousCoercivity
open YoshidaEndpointEvenBoundaryProductionBridge
open YoshidaEndpointEvenBoundaryResidual
open YoshidaEndpointEvenProjectedQuantitativeCoercivity
open YoshidaEndpointOddCleanPositive
open YoshidaPointwiseParityCore
open YoshidaSectionSixAnalytic
open YoshidaClippedEndpointContinuous

/-!
# Local coercivity versus far arithmetic decay

Restricted-support positivity supplies the sign of each quarter-lattice
diagonal, but absorbing the far row needs two quantitative upgrades: a
uniform diagonal gap and a summable bound for the complete global cross.

The archimedean remainder in a separated cross already has quadratic decay.
This file records what the unconditional Chebyshev estimate gives for the
remaining arithmetic term.  Its scale is linear before the critical
`sqrt r` normalization, hence it permits growth like `sqrt r`; it is not a
far-decay estimate.  Thus a local coercivity constant alone cannot close the
row with the currently available arithmetic bound.
-/

/-! ## The latent endpoint coercivity constant -/

/-- A real clipped profile's physical `L²` energy is exactly the endpoint
scale times the energy of its centered rescaling.  Unlike the older tail
lemma, this statement does not require a Fourier-tail hypothesis. -/
theorem clippedIntervalEnergy_eq_endpoint_mul_centeredRescale_real
    (f : YoshidaClippedSmooth yoshidaEndpointA)
    (hreal : ∀ x : ℝ, (f x).im = 0) :
    clippedIntervalEnergy f =
      yoshidaEndpointA *
        ∫ x : ℝ in -1..1,
          centeredRescale yoshidaEndpointA (fun y ↦ (f y).re) x ^ 2 := by
  let q : ℝ → ℝ := fun x ↦ (f x).re ^ 2
  have hsubst := intervalIntegral.smul_integral_comp_mul_add
    (a := (-1 : ℝ)) (b := 1) q yoshidaEndpointA 0
  have hscale :
      (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA, q x) =
        yoshidaEndpointA * ∫ x : ℝ in -1..1,
          q (yoshidaEndpointA * x) := by
    simpa only [smul_eq_mul, mul_neg, mul_one, add_zero, mul_zero,
      zero_add] using hsubst.symm
  rw [clippedIntervalEnergy]
  calc
    (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
        ‖(f : ℝ → ℂ) x‖ ^ 2) =
        ∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA, q x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      change ‖f x‖ ^ 2 = (f x).re ^ 2
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hreal x]
      ring
    _ = yoshidaEndpointA * ∫ x : ℝ in -1..1,
        q (yoshidaEndpointA * x) := hscale
    _ = _ := by rfl

/-- The quantitative clean-even theorem transports through the endpoint
boundary decomposition.  Thus the actual real-even production diagonal has
the same explicit `1 / 12000` physical `L²` gap. -/
theorem realEven_clippedCriticalForm_coercive
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaEndpointA)
    (hf_real : ∀ x : ℝ,
      ((((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) x).im = 0) :
    (1 / 12000 : ℝ) * clippedIntervalEnergy
        ((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
          YoshidaClippedSmooth yoshidaEndpointA) ≤
      (yoshidaClippedLocalCriticalForm yoshidaEndpointA
        yoshidaEndpointA_pos
        (f.1 : YoshidaClippedSmooth yoshidaEndpointA)
        (f.1 : YoshidaClippedSmooth yoshidaEndpointA)).re := by
  let fs : YoshidaClippedSmooth yoshidaEndpointA :=
    ((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
      YoshidaClippedSmooth yoshidaEndpointA)
  let c : ℝ := (fs yoshidaEndpointA).re
  let r : YoshidaClippedPeriodicCore yoshidaEndpointA :=
    evenBoundaryResidual f
  let rs : YoshidaClippedSmooth yoshidaEndpointA :=
    (r : YoshidaClippedSmooth yoshidaEndpointA)
  let g : ℝ → ℝ := fun x ↦ (rs x).re
  let w : ℝ → ℝ := centeredRescale yoshidaEndpointA g
  let u : ℝ → ℝ := fun x ↦ c + w x
  have hbridge := clippedCriticalFormValue_even_eq_clean_add_boundary f hf_real
  change clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos fs =
      yoshidaEndpointA * yoshidaEndpointOddCleanQuadratic u at hbridge
  have hends : rs (-yoshidaEndpointA) = 0 ∧
      rs yoshidaEndpointA = 0 := by
    simpa only [rs, r] using
      evenBoundaryResidual_endpoints_zero yoshidaEndpointA_pos f
  have hrcont : Continuous (rs : ℝ → ℂ) :=
    continuous_yoshidaClippedSmooth_of_endpoints_zero
      yoshidaEndpointA_pos rs hends.1 hends.2
  have hgcont : Continuous g := Complex.continuous_re.comp hrcont
  have hgeven : Function.Even g := by
    intro x
    have heven := evenBoundaryResidual_pointwise_even f x
    exact congrArg Complex.re heven
  have hwcont : Continuous w := by
    dsimp only [w, centeredRescale]
    exact hgcont.comp (continuous_const.mul continuous_id)
  have hweven : Function.Even w := by
    intro x
    dsimp only [w, centeredRescale]
    rw [show yoshidaEndpointA * -x = -(yoshidaEndpointA * x) by ring,
      hgeven]
  have hucont : Continuous u := continuous_const.add hwcont
  have hueven : Function.Even u := by
    intro x
    dsimp only [u]
    rw [hweven]
  have hprofile : ContDiffOn ℝ 1 g
      (Icc (-yoshidaEndpointA) yoshidaEndpointA) := by
    exact Complex.reCLM.contDiff.comp_contDiffOn
      (rs.property.1.of_le (by simp))
  have hscale : ContDiffOn ℝ 1
      (fun x : ℝ ↦ yoshidaEndpointA * x) (Icc (-1) 1) := by
    fun_prop
  have hmaps : MapsTo (fun x : ℝ ↦ yoshidaEndpointA * x)
      (Icc (-1) 1) (Icc (-yoshidaEndpointA) yoshidaEndpointA) := by
    intro x hx
    constructor <;> nlinarith [hx.1, hx.2, yoshidaEndpointA_pos]
  have hulocal : LocallyLipschitzOn (Icc (-1) 1) u := by
    have hsumProfile : ContDiffOn ℝ 1 (fun x ↦ c + g x)
        (Icc (-yoshidaEndpointA) yoshidaEndpointA) :=
      contDiffOn_const.add hprofile
    have hcomp := hsumProfile.comp hscale hmaps
    simpa only [u, w, centeredRescale, Function.comp_apply] using
      hcomp.locallyLipschitzOn (convex_Icc (-1) 1)
  have hclean := one_over_twelve_thousand_energy_le_even_clean
    u hucont hueven hulocal
  have hu_eq (x : ℝ) (hx : x ∈ Set.uIcc (-1 : ℝ) 1) :
      u x = centeredRescale yoshidaEndpointA
        (fun y ↦ (fs y).re) x := by
    have hx' : x ∈ Icc (-1 : ℝ) 1 := by simpa using hx
    have hAx : yoshidaEndpointA * x ∈
        Icc (-yoshidaEndpointA) yoshidaEndpointA := by
      constructor <;> nlinarith [hx'.1, hx'.2, yoshidaEndpointA_pos]
    dsimp only [u, w, g, centeredRescale]
    change c + (rs (yoshidaEndpointA * x)).re =
      (fs (yoshidaEndpointA * x)).re
    dsimp only [rs, r, evenBoundaryResidual, evenBoundaryConstantPart]
    simp only [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [periodicCoreOne_apply_of_mem hAx]
    dsimp only [c, fs]
    simp
  have hmass : (∫ x : ℝ in -1..1, u x ^ 2) =
      ∫ x : ℝ in -1..1,
        centeredRescale yoshidaEndpointA (fun y ↦ (fs y).re) x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    change u x ^ 2 =
      centeredRescale yoshidaEndpointA (fun y ↦ (fs y).re) x ^ 2
    rw [hu_eq x hx]
  rw [hmass] at hclean
  have henergy :=
    clippedIntervalEnergy_eq_endpoint_mul_centeredRescale_real fs
      (by simpa only [fs] using hf_real)
  change (1 / 12000 : ℝ) * clippedIntervalEnergy fs ≤
    clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos fs
  rw [hbridge, henergy]
  have hscaled :=
    mul_le_mul_of_nonneg_left hclean yoshidaEndpointA_pos.le
  nlinarith

/-- First derivative moment of the compactly supported physical correlation.
It is the exact profile seminorm produced by taking absolute values in the
Chebyshev-error pairing. -/
def separatedCorrelationDerivativeMoment
    (f g : BombieriTest) : ℝ :=
  ∫ x : ℝ in Set.Ioi 0, x *
    ‖deriv (fun y : ℝ ↦
      starRingEnd ℂ (bombieriDirectedCorrelation f g y)) x‖

theorem separatedCorrelationDerivativeMoment_integrable
    (f g : BombieriTest) :
    IntegrableOn (fun x : ℝ ↦ x *
      ‖deriv (fun y : ℝ ↦
        starRingEnd ℂ (bombieriDirectedCorrelation f g y)) x‖)
      (Set.Ioi 0) := by
  let H : ℝ → ℂ := fun y ↦
    starRingEnd ℂ (bombieriDirectedCorrelation f g y)
  have hdcont : Continuous (deriv H) :=
    (star_bombieriDirectedCorrelation_contDiff f g).continuous_deriv (by simp)
  have hdcompact : HasCompactSupport (deriv H) :=
    (star_bombieriDirectedCorrelation_hasCompactSupport f g).deriv
  have hcompact : HasCompactSupport (fun x : ℝ ↦ x * ‖deriv H x‖) :=
    hdcompact.norm.mul_left
  exact (continuous_id.mul hdcont.norm).integrable_of_hasCompactSupport
    hcompact |>.integrableOn

theorem separatedCorrelationDerivativeMoment_nonneg
    (f g : BombieriTest) :
    0 ≤ separatedCorrelationDerivativeMoment f g := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg hx.le (norm_nonneg _)

/-- The strongest elementary estimate available from Mathlib's Chebyshev
upper bound, stated symmetrically for the discrepancy. -/
theorem abs_chebyshevPsi_sub_self_le_linear
    {x : ℝ} (hx : 0 ≤ x) :
    |Chebyshev.psi x - x| ≤ (Real.log 4 + 5) * x := by
  have hpsi0 : 0 ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
  have hpsi : Chebyshev.psi x ≤ (Real.log 4 + 4) * x :=
    Chebyshev.psi_le_const_mul_self hx
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- After a positive dilation, the elementary discrepancy estimate is
linear in the dilation parameter. -/
theorem abs_chebyshevPsi_scaled_sub_scaled_le
    {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) :
    |Chebyshev.psi (r * x) - r * x| ≤
      (Real.log 4 + 5) * r * x := by
  have h := abs_chebyshevPsi_sub_self_le_linear
    (mul_nonneg hr hx)
  simpa only [mul_assoc] using h

/-- The elementary Chebyshev estimate bounds the arithmetic pairing by a
linear factor in `r` times the derivative moment.  This is quantitative but
has the wrong scale for far-cell absorption. -/
theorem norm_separatedChebyshevErrorPairing_le_linear
    (f g : BombieriTest) {r : ℝ} (hr : 0 < r) :
    ‖separatedChebyshevErrorPairing f g r‖ ≤
      (Real.log 4 + 5) * r *
        separatedCorrelationDerivativeMoment f g := by
  let H : ℝ → ℂ := fun y ↦
    starRingEnd ℂ (bombieriDirectedCorrelation f g y)
  let C : ℝ := Real.log 4 + 5
  let E : ℝ → ℂ := fun x ↦
    ((Chebyshev.psi (r * x) - r * x : ℝ) : ℂ) * deriv H x
  let D : ℝ → ℝ := fun x ↦ C * r * (x * ‖deriv H x‖)
  have hmoment : IntegrableOn (fun x : ℝ ↦ x * ‖deriv H x‖)
      (Set.Ioi 0) := by
    simpa only [H] using separatedCorrelationDerivativeMoment_integrable f g
  have hD : IntegrableOn D (Set.Ioi 0) := by
    dsimp only [D]
    exact hmoment.const_mul (C * r)
  have hEmeas : AEStronglyMeasurable E
      (volume.restrict (Set.Ioi 0)) := by
    have harg : Measurable (fun x : ℝ ↦ r * x) :=
      measurable_const_mul r
    have hpsi : Measurable (fun x : ℝ ↦ Chebyshev.psi (r * x)) :=
      Chebyshev.psi_mono.measurable.comp harg
    have herr : Measurable (fun x : ℝ ↦
        Chebyshev.psi (r * x) - r * x) :=
      hpsi.sub harg
    have herrC : AEStronglyMeasurable (fun x : ℝ ↦
        ((Chebyshev.psi (r * x) - r * x : ℝ) : ℂ))
        (volume.restrict (Set.Ioi 0)) :=
      (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
        herr.aestronglyMeasurable).mono_measure Measure.restrict_le_self
    have hd : AEStronglyMeasurable (deriv H)
        (volume.restrict (Set.Ioi 0)) :=
      ((star_bombieriDirectedCorrelation_contDiff f g).continuous_deriv
        (by simp)).aestronglyMeasurable.mono_measure Measure.restrict_le_self
    exact herrC.mul hd
  have hpoint : ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioi 0)),
      ‖E x‖ ≤ D x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have herr := abs_chebyshevPsi_scaled_sub_scaled_le hr.le hx.le
    dsimp only [E, D, C]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg (deriv H x)]
  have hE : IntegrableOn E (Set.Ioi 0) := by
    exact hD.mono' hEmeas hpoint
  calc
    ‖separatedChebyshevErrorPairing f g r‖ =
        ‖∫ x : ℝ in Set.Ioi 0, E x‖ := by rfl
    _ ≤ ∫ x : ℝ in Set.Ioi 0, ‖E x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ in Set.Ioi 0, D x := by
      exact integral_mono_ae hE.norm hD hpoint
    _ = C * r * ∫ x : ℝ in Set.Ioi 0, x * ‖deriv H x‖ := by
      dsimp only [D]
      rw [MeasureTheory.integral_const_mul]
    _ = (Real.log 4 + 5) * r *
        separatedCorrelationDerivativeMoment f g := by rfl

/-- Complete quantitative consequence for a separated global cross.  The
archimedean term has the already-proved inverse-quadratic coefficient, while
the unconditional arithmetic term is linear in `r` after multiplication by
`sqrt r`. -/
theorem norm_sqrt_mul_separatedGlobalCross_le_linear_add_decay
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) :
    ‖((Real.sqrt r : ℝ) : ℂ) *
        bombieriTwoBlockGlobalCrossSymbol f
          (normalizedDilation r hr g)‖ ≤
      (Real.log 4 + 5) * r *
          separatedCorrelationDerivativeMoment f g +
        (af / bg * ((r * (af / bg)) ^ 2 - 1))⁻¹ *
          separatedCorrelationNormMass f g := by
  rw [sqrt_mul_globalCross_eq_chebyshevError_sub_archimedeanKernel
    f g hr haf hag hbg hf hg hsep]
  calc
    ‖separatedChebyshevErrorPairing f g r -
        separatedArchimedeanKernel f g r‖ ≤
        ‖separatedChebyshevErrorPairing f g r‖ +
          ‖separatedArchimedeanKernel f g r‖ := norm_sub_le _ _
    _ ≤ (Real.log 4 + 5) * r *
          separatedCorrelationDerivativeMoment f g +
        (af / bg * ((r * (af / bg)) ^ 2 - 1))⁻¹ *
          separatedCorrelationNormMass f g :=
      add_le_add (norm_separatedChebyshevErrorPairing_le_linear f g hr)
        (norm_separatedArchimedeanKernel_le
          f g hr haf hag hbg hf hg hsep)

/-! ## Exact coercive absorption threshold -/

/-- A diagonal coercivity constant `kappa` absorbs a cross controlled by the
same two masses precisely when the cross coefficient is at most `kappa`.
This is the quantitative Young inequality needed by any local-coercivity
route. -/
theorem twoMass_cross_absorbed_of_coercivity
    {head tail cross kappa coefficient headMass tailMass : ℝ}
    (hkappa : 0 ≤ kappa) (hheadMass : 0 ≤ headMass)
    (htailMass : 0 ≤ tailMass)
    (hhead : kappa * headMass ^ 2 ≤ head)
    (htail : kappa * tailMass ^ 2 ≤ tail)
    (hcross : -cross ≤ coefficient * headMass * tailMass)
    (hcoefficient : coefficient ≤ kappa) :
    -2 * cross ≤ head + tail := by
  have hyoung : 2 * headMass * tailMass ≤
      headMass ^ 2 + tailMass ^ 2 := by
    nlinarith [sq_nonneg (headMass - tailMass)]
  have hscale : 2 * coefficient * headMass * tailMass ≤
      kappa * (headMass ^ 2 + tailMass ^ 2) := by
    have hcoefMass : coefficient * (2 * headMass * tailMass) ≤
        kappa * (2 * headMass * tailMass) := by
      exact mul_le_mul_of_nonneg_right hcoefficient
        (mul_nonneg (mul_nonneg (by norm_num) hheadMass) htailMass)
    have hkYoung : kappa * (2 * headMass * tailMass) ≤
        kappa * (headMass ^ 2 + tailMass ^ 2) :=
      mul_le_mul_of_nonneg_left hyoung hkappa
    nlinarith
  nlinarith

/-- The coefficient threshold above is sharp: demanding the scalar Young
bound for all nonnegative masses is equivalent to `coefficient ≤ kappa`.
In particular, strict positivity without a numerical gap supplies no budget
for a far row. -/
theorem universal_twoMass_absorption_iff
    {kappa coefficient : ℝ} (hkappa : 0 ≤ kappa) :
    (∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      2 * coefficient * a * b ≤
        kappa * a ^ 2 + kappa * b ^ 2) ↔
      coefficient ≤ kappa := by
  constructor
  · intro h
    have hunit := h 1 1 (by norm_num) (by norm_num)
    nlinarith
  · intro hcoef a b ha hb
    have hab : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
      nlinarith [sq_nonneg (a - b)]
    have hcoefab : coefficient * (2 * a * b) ≤
        kappa * (2 * a * b) := by
      exact mul_le_mul_of_nonneg_right hcoef
        (mul_nonneg (mul_nonneg (by norm_num) ha) hb)
    have hkab : kappa * (2 * a * b) ≤
        kappa * (a ^ 2 + b ^ 2) :=
      mul_le_mul_of_nonneg_left hab hkappa
    nlinarith

/-! ## Why strict positivity is not itself a coercivity theorem -/

/-- A scalar model of an infinite family of strictly positive diagonal
directions whose normalized energies tend to zero. -/
def nearNullStrictPositiveFamily (n : ℕ) (x : ℝ) : ℝ :=
  x ^ 2 / (n + 1 : ℝ)

theorem nearNullStrictPositiveFamily_pos
    (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    0 < nearNullStrictPositiveFamily n x := by
  exact div_pos (sq_pos_of_ne_zero hx) (by positivity)

/-- Every member of the preceding family is positive definite, but there is
no positive constant coercing all of them by the common squared norm.  This
is the exact logical obstruction to extracting a uniform quarter-cell gap
from a theorem asserting only strict positivity of every nonzero test. -/
theorem nearNullStrictPositiveFamily_not_uniformly_coercive :
    ¬ ∃ kappa : ℝ, 0 < kappa ∧
      ∀ (n : ℕ) (x : ℝ),
        kappa * x ^ 2 ≤ nearNullStrictPositiveFamily n x := by
  rintro ⟨kappa, hkappa, hcoercive⟩
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (1 / kappa)
  have hn' : 1 < (n : ℝ) * kappa := by
    rw [div_lt_iff₀ hkappa] at hn
    simpa only [one_mul] using hn
  have hunit := hcoercive n 1
  have hnplus : 0 < (n + 1 : ℝ) := by positivity
  have hupper : kappa * (n + 1 : ℝ) ≤ 1 := by
    apply (le_div_iff₀ hnplus).mp
    simpa only [nearNullStrictPositiveFamily, one_pow, mul_one] using hunit
  push_cast at hupper
  nlinarith

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneLocalCoerciveFarDecayStructural
