import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneLocalCoerciveFarDecayStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilRealCutPhaseReductionStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneLocalFullCoercivityStructural

noncomputable section

open MultiplicativeWeilMonotoneLocalCoerciveFarDecayStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealCutPhaseReductionStructural
open MultiplicativeWeil
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanLipschitz
open YoshidaEndpointOddProductionPositive
open YoshidaEndpointPhysicalRealQuadratic
open YoshidaEndpointScaledCorrelation
open YoshidaOddHomogeneousCoercivity
open YoshidaPointwiseOddPeriodicCore
open YoshidaPointwiseOddRealImag
open YoshidaPointwiseParityCore
open YoshidaSectionSixAnalytic

/-!
# Full local coercivity on the restricted endpoint core

The endpoint clean estimates contain explicit gaps on both reflection
parities.  This module transports the odd gap to the actual production form
and then recombines the two parity components without losing `L²` mass.
-/

/-- The rational odd clean reserve transports through the exact physical
endpoint bridge. -/
theorem realOdd_clippedCriticalForm_coercive
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule yoshidaEndpointA)
    (hf_real : ∀ x : ℝ,
      ((((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) x).im = 0) :
    (1 / 100 : ℝ) * clippedIntervalEnergy
        ((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
          YoshidaClippedSmooth yoshidaEndpointA) ≤
      (yoshidaClippedLocalCriticalForm yoshidaEndpointA
        yoshidaEndpointA_pos
        (f.1 : YoshidaClippedSmooth yoshidaEndpointA)
        (f.1 : YoshidaClippedSmooth yoshidaEndpointA)).re := by
  let fs : YoshidaClippedSmooth yoshidaEndpointA :=
    ((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
      YoshidaClippedSmooth yoshidaEndpointA)
  let g : ℝ → ℝ := pointwiseOddPeriodicCoreRealProfile f
  let w : ℝ → ℝ := centeredRescale yoshidaEndpointA g
  have hgcont : Continuous g :=
    continuous_pointwiseOddPeriodicCoreRealProfile yoshidaEndpointA_pos f
  have hgodd : Function.Odd g :=
    pointwiseOddPeriodicCoreRealProfile_odd f
  have hwcont : Continuous w := by
    dsimp only [w, centeredRescale]
    exact hgcont.comp (continuous_const.mul continuous_id)
  have hwodd : Function.Odd w := by
    intro x
    dsimp only [w, centeredRescale]
    rw [show yoshidaEndpointA * -x = -(yoshidaEndpointA * x) by ring,
      hgodd]
  have hwlocal : LocallyLipschitzOn (Icc (-1) 1) w := by
    simpa only [w, centeredRescale] using
      locallyLipschitzOn_centered_pointwiseOddPeriodicCoreRealProfile
        yoshidaEndpointA_pos f
  have hclean :=
    one_hundredth_energy_le_yoshidaEndpointOddCleanQuadratic_of_locallyLipschitzOn
      w hwcont hwodd hwlocal
  have hphysical :=
    yoshidaEndpointPhysicalRealQuadratic_eq_clean g hgcont hwlocal
  have hform :=
    yoshidaClippedLocalCriticalForm_re_eq_physicalRealQuadratic f hf_real
  have henergy :=
    clippedIntervalEnergy_eq_endpoint_mul_centeredRescale_real fs
      (by simpa only [fs] using hf_real)
  have hw_eq : w = centeredRescale yoshidaEndpointA
      (fun y ↦ (fs y).re) := by
    rfl
  rw [← hw_eq] at henergy
  change (1 / 100 : ℝ) * clippedIntervalEnergy fs ≤
    (yoshidaClippedLocalCriticalForm yoshidaEndpointA
      yoshidaEndpointA_pos fs fs).re
  rw [hform, hphysical, henergy]
  have hscaled :=
    mul_le_mul_of_nonneg_left hclean yoshidaEndpointA_pos.le
  nlinarith

private theorem endpointClippedNormSq_intervalIntegrable
    (f : YoshidaClippedSmooth yoshidaEndpointA) :
    IntervalIntegrable (fun x : ℝ ↦ ‖f x‖ ^ 2) volume
      (-yoshidaEndpointA) yoshidaEndpointA := by
  exact (f.property.1.continuousOn.norm.pow 2).intervalIntegrable_of_Icc
    (by linarith [yoshidaEndpointA_pos])

/-- Reflection parity is an exact orthogonal decomposition for the physical
clipped `L²` energy. -/
theorem clippedIntervalEnergy_eq_evenPart_add_oddPart
    (f : YoshidaClippedPeriodicCore yoshidaEndpointA) :
    clippedIntervalEnergy (f : YoshidaClippedSmooth yoshidaEndpointA) =
      clippedIntervalEnergy
          ((periodicCoreEvenPart f : YoshidaClippedPeriodicCore
            yoshidaEndpointA) : YoshidaClippedSmooth yoshidaEndpointA) +
        clippedIntervalEnergy
          ((periodicCoreOddPart f : YoshidaClippedPeriodicCore
            yoshidaEndpointA) : YoshidaClippedSmooth yoshidaEndpointA) := by
  let fs : YoshidaClippedSmooth yoshidaEndpointA :=
    (f : YoshidaClippedSmooth yoshidaEndpointA)
  let e : YoshidaClippedSmooth yoshidaEndpointA :=
    ((periodicCoreEvenPart f : YoshidaClippedPeriodicCore
      yoshidaEndpointA) : YoshidaClippedSmooth yoshidaEndpointA)
  let o : YoshidaClippedSmooth yoshidaEndpointA :=
    ((periodicCoreOddPart f : YoshidaClippedPeriodicCore
      yoshidaEndpointA) : YoshidaClippedSmooth yoshidaEndpointA)
  let F : ℝ → ℝ := fun x ↦ ‖fs x‖ ^ 2
  let E : ℝ → ℝ := fun x ↦ ‖e x‖ ^ 2
  let O : ℝ → ℝ := fun x ↦ ‖o x‖ ^ 2
  have hFint : IntervalIntegrable F volume
      (-yoshidaEndpointA) yoshidaEndpointA := by
    simpa only [F, fs] using endpointClippedNormSq_intervalIntegrable fs
  have hEint : IntervalIntegrable E volume
      (-yoshidaEndpointA) yoshidaEndpointA := by
    simpa only [E, e] using endpointClippedNormSq_intervalIntegrable e
  have hOint : IntervalIntegrable O volume
      (-yoshidaEndpointA) yoshidaEndpointA := by
    simpa only [O, o] using endpointClippedNormSq_intervalIntegrable o
  have hFnegInt : IntervalIntegrable (fun x : ℝ ↦ F (-x)) volume
      (-yoshidaEndpointA) yoshidaEndpointA := by
    let fr : YoshidaClippedSmooth yoshidaEndpointA := clippedReflection fs
    have h := endpointClippedNormSq_intervalIntegrable fr
    simpa only [fr, clippedReflection, F] using h
  have hpoint (x : ℝ) :
      E x + O x = (1 / 2 : ℝ) * (F x + F (-x)) := by
    dsimp only [E, O, F, e, o, fs]
    simp only [periodicCoreEvenPart_apply, periodicCoreOddPart_apply]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.inv_re, Complex.inv_im]
    norm_num
    ring
  have hreflect :
      (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA, F (-x)) =
        ∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA, F x := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg
        (f := F) (a := -yoshidaEndpointA) (b := yoshidaEndpointA))
  have hsum :
      (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA, E x) +
          ∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA, O x =
        ∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA, F x := by
    rw [← intervalIntegral.integral_add hEint hOint]
    calc
      (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          (E x + O x)) =
          ∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
            (1 / 2 : ℝ) * (F x + F (-x)) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        exact hpoint x
      _ = (1 / 2 : ℝ) *
          ((∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA, F x) +
            ∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
              F (-x)) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add hFint hFnegInt]
      _ = ∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA, F x := by
        rw [hreflect]
        ring
  unfold clippedIntervalEnergy
  change (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA, F x) =
    (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA, E x) +
      ∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA, O x
  exact hsum.symm

private theorem clippedIntervalEnergy_nonneg
    (f : YoshidaClippedSmooth yoshidaEndpointA) :
    0 ≤ clippedIntervalEnergy f := by
  unfold clippedIntervalEnergy
  exact intervalIntegral.integral_nonneg
    (by linarith [yoshidaEndpointA_pos])
      (fun _x _hx ↦ sq_nonneg _)

/-- The two quantitative parity gaps recombine into an unconditional uniform
gap for every conjugation-fixed periodic source.  The even constant
`1 / 12000` is the limiting one; the odd component retains the stronger
`1 / 100` reserve. -/
theorem realPeriodicCore_clippedCriticalForm_coercive
    (f : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (hf_real : ∀ x : ℝ,
      ((((f : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) x).im = 0) :
    (1 / 12000 : ℝ) * clippedIntervalEnergy
        (f : YoshidaClippedSmooth yoshidaEndpointA) ≤
      (yoshidaClippedLocalCriticalForm yoshidaEndpointA
        yoshidaEndpointA_pos
        (f : YoshidaClippedSmooth yoshidaEndpointA)
        (f : YoshidaClippedSmooth yoshidaEndpointA)).re := by
  let e : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaEndpointA :=
    pointwiseEvenPart f
  let o : yoshidaPointwiseOddPeriodicCoreSubmodule yoshidaEndpointA :=
    pointwiseOddPart f
  let es : YoshidaClippedSmooth yoshidaEndpointA :=
    ((e.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
      YoshidaClippedSmooth yoshidaEndpointA)
  let os : YoshidaClippedSmooth yoshidaEndpointA :=
    ((o.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
      YoshidaClippedSmooth yoshidaEndpointA)
  have he_real : ∀ x : ℝ, (es x).im = 0 := by
    intro x
    dsimp only [es, e, pointwiseEvenPart]
    rw [periodicCoreEvenPart_apply]
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.inv_re, Complex.inv_im, hf_real]
    norm_num
  have ho_real : ∀ x : ℝ, (os x).im = 0 := by
    intro x
    dsimp only [os, o, pointwiseOddPart]
    rw [periodicCoreOddPart_apply]
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.inv_re, Complex.inv_im, hf_real]
    norm_num
  have he := realEven_clippedCriticalForm_coercive e he_real
  have ho := realOdd_clippedCriticalForm_coercive o ho_real
  have hoEnergy : 0 ≤ clippedIntervalEnergy os :=
    clippedIntervalEnergy_nonneg os
  have hoWeak : (1 / 12000 : ℝ) * clippedIntervalEnergy os ≤
      (yoshidaClippedLocalCriticalForm yoshidaEndpointA
        yoshidaEndpointA_pos os os).re := by
    nlinarith
  have hform :=
    yoshidaClippedLocalCriticalForm_self_eq_even_add_odd
      yoshidaEndpointA_pos f
  have hformRe := congrArg Complex.re hform
  rw [Complex.add_re] at hformRe
  have henergy := clippedIntervalEnergy_eq_evenPart_add_oddPart f
  change (1 / 12000 : ℝ) *
      clippedIntervalEnergy (f : YoshidaClippedSmooth yoshidaEndpointA) ≤
    (yoshidaClippedLocalCriticalForm yoshidaEndpointA
      yoshidaEndpointA_pos
      (f : YoshidaClippedSmooth yoshidaEndpointA)
      (f : YoshidaClippedSmooth yoshidaEndpointA)).re
  change clippedIntervalEnergy
      (f : YoshidaClippedSmooth yoshidaEndpointA) =
    clippedIntervalEnergy es + clippedIntervalEnergy os at henergy
  change (yoshidaClippedLocalCriticalForm yoshidaEndpointA
      yoshidaEndpointA_pos
      (f : YoshidaClippedSmooth yoshidaEndpointA)
      (f : YoshidaClippedSmooth yoshidaEndpointA)).re =
    (yoshidaClippedLocalCriticalForm yoshidaEndpointA
      yoshidaEndpointA_pos es es).re +
    (yoshidaClippedLocalCriticalForm yoshidaEndpointA
      yoshidaEndpointA_pos os os).re at hformRe
  rw [henergy, hformRe]
  nlinarith

/-! ## Quantitative transport to real ratio-two Bombieri tests -/

/-- Concrete local norm of a Bombieri test after logarithmic centering and
endpoint clipping.  Dilation covariance makes this the natural norm exposed
by the existing restricted-support bridge. -/
def bombieriCenteredCropEnergy
    (g : BombieriTest) (l r : ℝ) : ℝ :=
  clippedIntervalEnergy
    (yoshidaCriticalPullbackCropLinear yoshidaEndpointA
      (normalizedDilation (logarithmicCenter l r)
        (logarithmicCenter_pos l r) g))

private theorem apply_im_eq_zero_of_conjugate_fixed
    (g : BombieriTest) (hg : bombieriConjugateTest g = g) (x : ℝ) :
    (g x).im = 0 := by
  have hx := congrArg (fun q : BombieriTest ↦ q x) hg
  have him := congrArg Complex.im hx
  change -(g x).im = (g x).im at him
  linarith

/-- Quantitative restricted-support theorem on the real slice.  It upgrades
the public ratio-two sign theorem to an explicit `1 / 12000` lower bound by
the centered crop energy, without certificates or a nonzero hypothesis. -/
theorem bombieriFunctional_quadratic_re_ge_centeredCropEnergy_of_ratio_le_two
    (g : BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2)
    (hreal : bombieriConjugateTest g = g) :
    (1 / 12000 : ℝ) * bombieriCenteredCropEnergy g l r ≤
      (bombieriFunctional (bombieriQuadraticTest g)).re := by
  let lambda : ℝ := logarithmicCenter l r
  have hlambda : 0 < lambda := logarithmicCenter_pos l r
  let g' : BombieriTest := normalizedDilation lambda hlambda g
  have hsupported : YoshidaCriticalPullbackSupported yoshidaEndpointA g' := by
    exact
      logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaEndpointA
        g hl hlr hsupport hratio
  have hmem : yoshidaCriticalPullbackCropLinear yoshidaEndpointA g' ∈
      yoshidaClippedPeriodicCoreSubmodule yoshidaEndpointA := by
    exact logCenteredNormalizedDilation_crop_mem_yoshidaEndpointPeriodicCore
      g hl hlr hsupport hratio
  let core : YoshidaClippedPeriodicCore yoshidaEndpointA :=
    ⟨yoshidaCriticalPullbackCropLinear yoshidaEndpointA g', hmem⟩
  have hg'Real (x : ℝ) : (g' x).im = 0 := by
    dsimp only [g']
    rw [normalizedDilation_apply]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    rw [apply_im_eq_zero_of_conjugate_fixed g hreal]
    ring
  have hcoreReal (x : ℝ) :
      (((core : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) x).im = 0 := by
    dsimp only [core]
    by_cases hx : x ∈ Set.Icc (-yoshidaEndpointA) yoshidaEndpointA
    · rw [yoshidaCriticalPullbackCropLinear_apply_of_mem g' hx,
        BombieriTest.logarithmicPullbackSchwartz_apply]
      unfold BombieriTest.logarithmicPullback
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, hg'Real, mul_zero]
    · rw [yoshidaCriticalPullbackCropLinear_apply_of_not_mem g' hx]
      rfl
  have hcoercive :=
    realPeriodicCore_clippedCriticalForm_coercive core hcoreReal
  have hlocal :
      (1 / 12000 : ℝ) * clippedIntervalEnergy
          (yoshidaCriticalPullbackCropLinear yoshidaEndpointA g') ≤
        (bombieriLocalCriticalForm g' g').re := by
    rw [← yoshidaClippedLocalCriticalForm_crop_eq_bombieriLocalCriticalForm
      yoshidaEndpointA_pos g' g' hsupported hsupported]
    simpa only [core] using hcoercive
  have hsupport' : tsupport g' ⊆
      Set.Icc (l / lambda) (r / lambda) := by
    exact normalizedDilation_tsupport_subset_Icc
      lambda hlambda g hsupport
  have hl' : 0 < l / lambda := div_pos hl hlambda
  have hlr' : l / lambda ≤ r / lambda :=
    div_le_div_of_nonneg_right hlr hlambda.le
  have hratio' : (r / lambda) / (l / lambda) ≤ 2 := by
    rw [div_div_div_cancel_right₀ hlambda.ne' r l]
    exact hratio
  have hfunctional' :=
    bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
      g' hl' hlr' hsupport' hratio'
  have hinvariant :=
    bombieriFunctional_quadratic_normalizedDilation lambda hlambda g
  change (1 / 12000 : ℝ) * clippedIntervalEnergy
      (yoshidaCriticalPullbackCropLinear yoshidaEndpointA g') ≤
    (bombieriFunctional (bombieriQuadraticTest g)).re
  calc
    (1 / 12000 : ℝ) * clippedIntervalEnergy
        (yoshidaCriticalPullbackCropLinear yoshidaEndpointA g') ≤
        (bombieriLocalCriticalForm g' g').re := hlocal
    _ = (bombieriFunctional (bombieriQuadraticTest g')).re := by
      rw [hfunctional']
    _ = (bombieriFunctional (bombieriQuadraticTest g)).re := by
      rw [hinvariant]

/-- Every canonical monotone quarter cell cut from a real parent inherits the
uniform local gap.  This is the quantitative diagonal estimate required before
controlling interactions between distinct logarithmic cells. -/
theorem monotoneQuarterCell_quadratic_re_ge_centeredCropEnergy
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) :
    (1 / 12000 : ℝ) *
        bombieriCenteredCropEnergy
          (monotoneQuarterCell parent k)
          (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 2)) ≤
      (bombieriFunctional
        (bombieriQuadraticTest (monotoneQuarterCell parent k))).re := by
  apply bombieriFunctional_quadratic_re_ge_centeredCropEnergy_of_ratio_le_two
  · exact quarterLogLatticePoint_pos k
  · exact quarterLogLatticePoint_mono (by omega)
  · exact monotoneQuarterCell_tsupport_subset parent k
  · rw [quarterLogLatticePoint_add_two,
      mul_div_cancel_right₀ _ (quarterLogLatticePoint_pos k).ne']
    calc
      quarterLogLatticePoint 2 ≤ quarterLogLatticePoint 4 :=
        quarterLogLatticePoint_mono (by omega)
      _ = 2 := quarterLogLatticePoint_four
  · exact bombieriConjugateTest_monotoneQuarterCell parent hparent k

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneLocalFullCoercivityStructural
