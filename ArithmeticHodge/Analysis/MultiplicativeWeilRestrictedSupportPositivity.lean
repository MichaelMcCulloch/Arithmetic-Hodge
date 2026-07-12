import ArithmeticHodge.Analysis.YoshidaEvenInfiniteSchur
import ArithmeticHodge.Analysis.YoshidaRestrictedCoreBridge

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilRestrictedSupportPositivity

noncomputable section

open ArithmeticHodge.Analysis
open MultiplicativeWeil
open YoshidaCoercivityNumerics
open YoshidaEvenInfiniteSchur
open YoshidaEvenMomentTargets
open YoshidaWeightedTailBounds

/-- A supported critical pullback cannot vanish after clipping unless the
original Bombieri test vanishes. -/
theorem yoshidaCriticalPullbackCrop_ne_zero
    {a : ℝ} {f : BombieriTest}
    (hsupported : YoshidaCriticalPullbackSupported a f)
    (hf : f ≠ 0) :
    yoshidaCriticalPullbackCropLinear a f ≠ 0 := by
  intro hcrop
  apply hf
  ext x
  by_cases hx : 0 < x
  · let u : ℝ := -Real.log x
    have hfun := yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz
      hsupported
    have hzero :
        f.logarithmicPullbackSchwartz (1 / 2) u = 0 := by
      rw [← hfun]
      have h := congrArg
        (fun g : YoshidaClippedSmooth a ↦ g u) hcrop
      simpa using h
    rw [BombieriTest.logarithmicPullbackSchwartz_apply] at hzero
    unfold BombieriTest.logarithmicPullback at hzero
    have harg : Real.exp (-u) = x := by
      dsimp only [u]
      rw [neg_neg, Real.exp_log hx]
    rw [harg] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  · exact BombieriTest.apply_eq_zero_of_nonpos f hx

/-- The exact finite certificates imply strict Bombieri positivity for every
nonzero test whose multiplicative support ratio is at most two. -/
theorem bombieriFunctional_quadratic_re_pos_of_ratio_le_two_of_certificates
    (hS : YoshidaEvenSineTargetEnclosures)
    (hD : YoshidaEvenDiagonalTargetEnclosures)
    (hP : YoshidaEvenFullTargetPivots)
    (g : BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2) (hg : g ≠ 0) :
    0 < (bombieriFunctional (bombieriQuadraticTest g)).re := by
  let lambda : ℝ := logarithmicCenter l r
  have hlambda : 0 < lambda := logarithmicCenter_pos l r
  let g' : BombieriTest := normalizedDilation lambda hlambda g
  have hg' : g' ≠ 0 :=
    (normalizedDilation_ne_zero_iff lambda hlambda g).mpr hg
  have hsupported : YoshidaCriticalPullbackSupported yoshidaA g' := by
    exact logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaA
      g hl hlr hsupport hratio
  have hmem : yoshidaCriticalPullbackCropLinear yoshidaA g' ∈
      yoshidaClippedPeriodicCoreSubmodule yoshidaA := by
    exact logCenteredNormalizedDilation_crop_mem_yoshidaPeriodicCore
      g hl hlr hsupport hratio
  let core : YoshidaClippedPeriodicCore yoshidaA :=
    ⟨yoshidaCriticalPullbackCropLinear yoshidaA g', hmem⟩
  have hcore : core ≠ 0 := by
    intro hzero
    apply yoshidaCriticalPullbackCrop_ne_zero hsupported hg'
    exact congrArg Subtype.val hzero
  have hclipped :
      0 < (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (yoshidaCriticalPullbackCropLinear yoshidaA g')
        (yoshidaCriticalPullbackCropLinear yoshidaA g')).re := by
    simpa only [core] using
      periodicCore_clippedCriticalForm_re_pos_of_certificates
        hS hD hP core hcore
  have hlocal :
      0 < (bombieriLocalCriticalForm g' g').re := by
    rw [← yoshidaClippedLocalCriticalForm_crop_eq_bombieriLocalCriticalForm
      yoshidaA_pos g' g' hsupported hsupported]
    exact hclipped
  have hsupport' : tsupport g' ⊆
      Set.Icc (l / lambda) (r / lambda) := by
    exact normalizedDilation_tsupport_subset_Icc
      lambda hlambda g hsupport
  have hl' : 0 < l / lambda := div_pos hl hlambda
  have hr' : 0 < r := hl.trans_le hlr
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
  calc
    0 < (bombieriLocalCriticalForm g' g').re := hlocal
    _ = (bombieriFunctional (bombieriQuadraticTest g')).re := by
      rw [hfunctional']
    _ = (bombieriFunctional (bombieriQuadraticTest g)).re := by
      rw [hinvariant]

/-- Real-valued strict positivity in the exact shape used by the production
Bombieri criterion. -/
theorem bombieriFunctional_quadratic_strictPos_of_ratio_le_two_of_certificates
    (hS : YoshidaEvenSineTargetEnclosures)
    (hD : YoshidaEvenDiagonalTargetEnclosures)
    (hP : YoshidaEvenFullTargetPivots)
    (g : BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2) (hg : g ≠ 0) :
    (bombieriFunctional (bombieriQuadraticTest g)).im = 0 ∧
      0 < (bombieriFunctional (bombieriQuadraticTest g)).re := by
  exact ⟨bombieriFunctional_bombieriQuadraticTest_im_eq_zero g,
    bombieriFunctional_quadratic_re_pos_of_ratio_le_two_of_certificates
      hS hD hP g hl hlr hsupport hratio hg⟩

end

end ArithmeticHodge.Analysis.MultiplicativeWeilRestrictedSupportPositivity
