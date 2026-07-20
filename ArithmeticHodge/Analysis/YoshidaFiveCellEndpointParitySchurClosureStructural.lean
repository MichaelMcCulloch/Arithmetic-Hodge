import ArithmeticHodge.Analysis.YoshidaFiveCellEndpointOperatorParitySplitStructural
import ArithmeticHodge.Analysis.YoshidaFiveCellLowModeClosureStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCenteredP9Structural

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ContDiff

namespace ArithmeticHodge.Analysis.YoshidaFiveCellEndpointParitySchurClosureStructural

noncomputable section

open YoshidaFactorTwoEndpointParityPencil
open MultiplicativeWeilFiveCellSingleProfileStructural
open MultiplicativeWeilFiveCellResidualFactorTwoStructural
open ShiftedLegendreBasis
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreCenteredParity
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineCanonicalProjectionStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaClippedEndpointContinuous
open YoshidaFiveCellCanonicalLowTailSchurStructural
open YoshidaFiveCellEndpointAdaptedIntrinsicLowStructural
open YoshidaFiveCellEndpointAdaptedLowTailStructural
open YoshidaFiveCellEndpointOperatorParitySplitStructural
open YoshidaFiveCellEndpointOperatorProbeStructural
open YoshidaFiveCellHighTailCoercivityStructural
open YoshidaFiveCellLowModeClosureStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaSectionSixAnalytic

/-!
# Same-parity ray closure for the endpoint-adapted five-cell split

For a genuine quadratic form, the low diagonal and its mixed Schur
determinant are not two independent obligations.  They are exactly
nonnegativity on every affine ray `low + s • tail`.  This file establishes
that formulation for the concrete five-cell endpoint operator and transports
it to the five-even/four-odd intrinsic low coordinates.
-/

private theorem locallyLipschitzOn_congr_Icc
    {u v : ℝ → ℝ}
    (huv : ∀ x ∈ Icc (-1 : ℝ) 1, u x = v x)
    (hu : LocallyLipschitzOn (Icc (-1 : ℝ) 1) u) :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) v := by
  intro x hx
  obtain ⟨K, t, ht, hLip⟩ := hu hx
  refine ⟨K, t ∩ Icc (-1 : ℝ) 1,
    Filter.inter_mem ht self_mem_nhdsWithin, ?_⟩
  intro y hy z hz
  rw [← huv y hy.2, ← huv z hz.2]
  exact hLip hy.1 hz.1

private theorem fiveCellClippedOfSmooth_real
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) :
    ∀ y ∈ Icc (-fiveCellOperatorHalfWidth) fiveCellOperatorHalfWidth,
      fiveCellClippedOfSmooth w hw y =
        ((fiveCellClippedOfSmooth w hw y).re : ℂ) := by
  intro y hy
  unfold fiveCellClippedOfSmooth
  simp only [hy, ↓reduceIte, Complex.ofReal_re]

private theorem fiveCellClippedOfSmooth_endpoints
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hend : w (-1) = 0 ∧ w 1 = 0) :
    fiveCellClippedOfSmooth w hw (-fiveCellOperatorHalfWidth) = 0 ∧
      fiveCellClippedOfSmooth w hw fiveCellOperatorHalfWidth = 0 := by
  unfold fiveCellClippedOfSmooth
  have hwidthNe : fiveCellOperatorHalfWidth ≠ 0 :=
    fiveCellOperatorHalfWidth_pos.ne'
  constructor
  · have hmem : -fiveCellOperatorHalfWidth ∈
      Icc (-fiveCellOperatorHalfWidth) fiveCellOperatorHalfWidth :=
      ⟨le_rfl, by linarith [fiveCellOperatorHalfWidth_pos]⟩
    change (if -fiveCellOperatorHalfWidth ∈
        Icc (-fiveCellOperatorHalfWidth) fiveCellOperatorHalfWidth then
      (w ((-fiveCellOperatorHalfWidth) /
        fiveCellOperatorHalfWidth) : ℂ) else 0) = 0
    rw [if_pos hmem]
    simp only [neg_div, div_self hwidthNe, hend.1, Complex.ofReal_zero]
  · have hmem : fiveCellOperatorHalfWidth ∈
      Icc (-fiveCellOperatorHalfWidth) fiveCellOperatorHalfWidth :=
      ⟨by linarith [fiveCellOperatorHalfWidth_pos], le_rfl⟩
    change (if fiveCellOperatorHalfWidth ∈
        Icc (-fiveCellOperatorHalfWidth) fiveCellOperatorHalfWidth then
      (w (fiveCellOperatorHalfWidth /
        fiveCellOperatorHalfWidth) : ℂ) else 0) = 0
    rw [if_pos hmem]
    simp only [div_self hwidthNe, hend.2, Complex.ofReal_zero]

/- The critical form gives a clean quadratic model for every smooth
endpoint-zero profile.  This is the only analytic bridge needed for the ray
identity below. -/
private theorem clippedCriticalForm_self_re_eq_physical
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hend : w (-1) = 0 ∧ w 1 = 0) :
    (yoshidaClippedLocalCriticalForm fiveCellOperatorHalfWidth
        fiveCellOperatorHalfWidth_pos
        (fiveCellClippedOfSmooth w hw)
        (fiveCellClippedOfSmooth w hw)).re =
      fiveCellOperatorHalfWidth *
        centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth w := by
  let f := fiveCellClippedOfSmooth w hw
  let wc := fiveCellCompactRestriction w
  have hprofile : fiveCellClippedCenteredRealProfile f = wc := by
    simpa only [f, wc] using
      fiveCellClippedCenteredRealProfile_ofSmooth w hw
  have hwOne : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have hwLip : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hwOne.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hwc : ∀ x ∈ Icc (-1 : ℝ) 1, wc x = w x := by
    intro x hx
    simp only [wc, fiveCellCompactRestriction, hx, ↓reduceIte]
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fiveCellClippedCenteredRealProfile f) := by
    rw [hprofile]
    exact locallyLipschitzOn_congr_Icc
      (fun x hx ↦ (hwc x hx).symm) hwLip
  have hfend := fiveCellClippedOfSmooth_endpoints w hw hend
  have hdiag :=
    clippedCriticalFormValue_eq_centeredClippedPhysicalQuadratic_of_endpoints_zero
      fiveCellOperatorHalfWidth_pos f
      (fiveCellClippedOfSmooth_real w hw) hfend.1 hfend.2 hlocal
  simp only [clippedCriticalFormValue] at hdiag
  change (yoshidaClippedLocalCriticalForm fiveCellOperatorHalfWidth
      fiveCellOperatorHalfWidth_pos f f).re =
    fiveCellOperatorHalfWidth *
      centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth
        (fiveCellClippedCenteredRealProfile f) at hdiag
  rw [hprofile] at hdiag
  calc
    (yoshidaClippedLocalCriticalForm fiveCellOperatorHalfWidth
        fiveCellOperatorHalfWidth_pos f f).re =
        fiveCellOperatorHalfWidth *
          centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth wc := hdiag
    _ = fiveCellOperatorHalfWidth *
        centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth w := by
      rw [centeredClippedPhysicalQuadratic_congr_Icc hwc]

private theorem fiveCellClippedOfSmooth_add_smul
    (u v : ℝ → ℝ) (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v) (s : ℝ) :
    fiveCellClippedOfSmooth (u + s • v) (hu.add (hv.const_smul s)) =
      fiveCellClippedOfSmooth u hu +
        (s : ℂ) • fiveCellClippedOfSmooth v hv := by
  apply Subtype.ext
  funext y
  unfold fiveCellClippedOfSmooth
  by_cases hy : y ∈
      Icc (-fiveCellOperatorHalfWidth) fiveCellOperatorHalfWidth
  · simp only [hy, ↓reduceIte, Submodule.coe_add, Pi.add_apply,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    push_cast
    rfl
  · simp only [hy, ↓reduceIte, Submodule.coe_add, Pi.add_apply,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_zero, add_zero]

/- The physical diagonal is a literal quadratic polynomial on every smooth
endpoint-zero ray.  The coefficient is the real Hermitian polarization of
the clipped critical form. -/
private theorem centeredClippedPhysicalQuadratic_add_smul
    (u v : ℝ → ℝ) (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v)
    (huend : u (-1) = 0 ∧ u 1 = 0)
    (hvend : v (-1) = 0 ∧ v 1 = 0)
    (s : ℝ) :
    centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth
        (u + s • v) =
      centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth u +
        2 * s *
          ((yoshidaClippedLocalCriticalForm fiveCellOperatorHalfWidth
              fiveCellOperatorHalfWidth_pos
              (fiveCellClippedOfSmooth u hu)
              (fiveCellClippedOfSmooth v hv)).re /
            fiveCellOperatorHalfWidth) +
        s ^ 2 * centeredClippedPhysicalQuadratic
          fiveCellOperatorHalfWidth v := by
  let f := fiveCellClippedOfSmooth u hu
  let g := fiveCellClippedOfSmooth v hv
  let huv : ContDiff ℝ ∞ (u + s • v) := hu.add (hv.const_smul s)
  let h := fiveCellClippedOfSmooth (u + s • v) huv
  let B := yoshidaClippedLocalCriticalForm fiveCellOperatorHalfWidth
    fiveCellOperatorHalfWidth_pos
  have hend : (u + s • v) (-1) = 0 ∧ (u + s • v) 1 = 0 := by
    constructor <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        huend.1, huend.2, hvend.1, hvend.2, mul_zero, add_zero]
  have hclip : h = f + (s : ℂ) • g := by
    simpa only [h, f, g, huv] using
      fiveCellClippedOfSmooth_add_smul u v hu hv s
  have huDiag := clippedCriticalForm_self_re_eq_physical u hu huend
  have hvDiag := clippedCriticalForm_self_re_eq_physical v hv hvend
  have huvDiag := clippedCriticalForm_self_re_eq_physical
    (u + s • v) huv hend
  change (B f f).re = fiveCellOperatorHalfWidth *
    centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth u at huDiag
  change (B g g).re = fiveCellOperatorHalfWidth *
    centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth v at hvDiag
  change (B h h).re = fiveCellOperatorHalfWidth *
    centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth
      (u + s • v) at huvDiag
  have hconj := yoshidaClippedLocalCriticalForm_conj_apply
    fiveCellOperatorHalfWidth_pos f g
  change star (B g f) = B f g at hconj
  have hre : (B g f).re = (B f g).re := by
    have h := congrArg Complex.re hconj
    simpa using h
  have hleft (w : YoshidaClippedSmooth fiveCellOperatorHalfWidth) :
      B ((s : ℂ) • g) w = (s : ℂ) * B g w := by
    calc
      B ((s : ℂ) • g) w = star (s : ℂ) * B g w := by
        simpa only [smul_eq_mul] using
          (LinearMap.map_smulₛₗ₂ B (s : ℂ) g w)
      _ = (s : ℂ) * B g w := by
        rw [Complex.star_def, Complex.conj_ofReal]
  have hright (w : YoshidaClippedSmooth fiveCellOperatorHalfWidth) :
      B w ((s : ℂ) • g) = (s : ℂ) * B w g := by
    rw [map_smul]
    simp only [smul_eq_mul]
  have hform : (B h h).re =
      (B f f).re + 2 * s * (B f g).re + s ^ 2 * (B g g).re := by
    rw [hclip]
    simp only [map_add, LinearMap.add_apply]
    rw [hleft f, hright f, hleft ((s : ℂ) • g), hright g]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [hre]
    ring
  rw [huvDiag, huDiag, hvDiag] at hform
  have hwidthNe : fiveCellOperatorHalfWidth ≠ 0 :=
    fiveCellOperatorHalfWidth_pos.ne'
  field_simp [hwidthNe]
  nlinarith

private theorem fiveCellEndpointPairing_add_smul
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (s : ℝ) :
    fiveCellEndpointPairing (u + s • v) =
      fiveCellEndpointPairing u +
        s * fiveCellEndpointPolarCross u v +
          s ^ 2 * fiveCellEndpointPairing v := by
  have h := fiveCellEndpointPairing_linearCombination u v hu hv 1 s
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul,
    one_pow, one_mul] using h

/-- Exact degree-two ray identity for the complete five-cell endpoint
operator.  It is proved from the clipped Hermitian critical form and the
retained prime polarization, rather than assumed as an abstract quadratic
law. -/
theorem fiveCellEndpointOperator_add_smul
    (u v : ℝ → ℝ) (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v)
    (huend : u (-1) = 0 ∧ u 1 = 0)
    (hvend : v (-1) = 0 ∧ v 1 = 0)
    (s : ℝ) :
    fiveCellEndpointOperator (u + s • v) =
      fiveCellEndpointOperator u +
        2 * s * fiveCellEndpointOperatorCross u v +
          s ^ 2 * fiveCellEndpointOperator v := by
  let f := fiveCellClippedOfSmooth u hu
  let g := fiveCellClippedOfSmooth v hv
  let X : ℝ :=
    (yoshidaClippedLocalCriticalForm fiveCellOperatorHalfWidth
        fiveCellOperatorHalfWidth_pos f g).re /
        fiveCellOperatorHalfWidth -
      (Real.sqrt 2 * Real.log 2 / 2) *
        fiveCellEndpointPolarCross u v
  have hgeneral (t : ℝ) :
      fiveCellEndpointOperator (u + t • v) =
        fiveCellEndpointOperator u + 2 * t * X +
          t ^ 2 * fiveCellEndpointOperator v := by
    have hphysical := centeredClippedPhysicalQuadratic_add_smul
      u v hu hv huend hvend t
    have hprime := fiveCellEndpointPairing_add_smul
      u v hu.continuous hv.continuous t
    unfold fiveCellEndpointOperator
    dsimp only [X, f, g]
    rw [hphysical, hprime]
    ring
  have hone := hgeneral 1
  have hadd : u + (1 : ℝ) • v = u + v := by
    simp
  rw [hadd] at hone
  have hcross : fiveCellEndpointOperatorCross u v = X := by
    unfold fiveCellEndpointOperatorCross
    nlinarith
  rw [hcross]
  exact hgeneral s

/-- A quadratic ray is nonnegative at every real parameter exactly when its
low diagonal and inverse-free Schur determinant are nonnegative, once the
tail diagonal is known nonnegative. -/
theorem quadraticRay_nonnegative_iff_schur
    {L T C : ℝ} (hT : 0 ≤ T) :
    (∀ s : ℝ, 0 ≤ L + 2 * s * C + s ^ 2 * T) ↔
      0 ≤ L ∧ C ^ 2 ≤ L * T := by
  constructor
  · intro h
    have hL : 0 ≤ L := by
      simpa using h 0
    refine ⟨hL, ?_⟩
    rcases hT.eq_or_lt with hTzero | hTpos
    · subst T
      by_cases hC : C = 0
      · simp [hC]
      · have hs := h (-(L + 1) / (2 * C))
        have hcalc :
            L + 2 * (-(L + 1) / (2 * C)) * C +
                (-(L + 1) / (2 * C)) ^ 2 * 0 = -1 := by
          field_simp [hC]
          ring
        rw [hcalc] at hs
        linarith
    · have hs := h (-C / T)
      have hcalc :
          L + 2 * (-C / T) * C + (-C / T) ^ 2 * T =
            (L * T - C ^ 2) / T := by
        field_simp [hTpos.ne']
        ring
      rw [hcalc] at hs
      have hscaled := mul_nonneg hs hTpos.le
      rw [div_mul_cancel₀ _ hTpos.ne'] at hscaled
      nlinarith
  · rintro ⟨hL, hC⟩ s
    let C' := s * C
    let T' := s ^ 2 * T
    have hT' : 0 ≤ T' := by
      exact mul_nonneg (sq_nonneg s) hT
    have hC' : C' ^ 2 ≤ L * T' := by
      dsimp only [C', T']
      nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hC)]
    have hsum : 0 ≤ L + T' := add_nonneg hL hT'
    have hamgm : 4 * L * T' ≤ (L + T') ^ 2 := by
      nlinarith [sq_nonneg (L - T')]
    have hsquares : (2 * |C'|) ^ 2 ≤ (L + T') ^ 2 := by
      rw [mul_pow, sq_abs]
      nlinarith
    have habs0 : 0 ≤ 2 * |C'| :=
      mul_nonneg (by norm_num) (abs_nonneg C')
    have habs : 2 * |C'| ≤ L + T' :=
      (sq_le_sq₀ habs0 hsum).mp hsquares
    have hneg : -C' ≤ |C'| := neg_le_abs C'
    dsimp only [C', T'] at *
    nlinarith

/-- For two smooth endpoint-zero five-cell profiles, the actual low diagonal
and mixed Schur inequality are equivalent to one operator statement on the
whole affine ray. -/
theorem fiveCellEndpointOperator_forall_add_smul_nonnegative_iff_schur
    (u v : ℝ → ℝ) (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v)
    (huend : u (-1) = 0 ∧ u 1 = 0)
    (hvend : v (-1) = 0 ∧ v 1 = 0)
    (hvNonnegative : 0 ≤ fiveCellEndpointOperator v) :
    (∀ s : ℝ, 0 ≤ fiveCellEndpointOperator (u + s • v)) ↔
      0 ≤ fiveCellEndpointOperator u ∧
        fiveCellEndpointOperatorCross u v ^ 2 ≤
          fiveCellEndpointOperator u * fiveCellEndpointOperator v := by
  rw [show (∀ s : ℝ,
      0 ≤ fiveCellEndpointOperator (u + s • v)) ↔
      ∀ s : ℝ,
        0 ≤ fiveCellEndpointOperator u +
          2 * s * fiveCellEndpointOperatorCross u v +
            s ^ 2 * fiveCellEndpointOperator v by
    constructor
    · intro h s
      rw [← fiveCellEndpointOperator_add_smul
        u v hu hv huend hvend s]
      exact h s
    · intro h s
      rw [fiveCellEndpointOperator_add_smul
        u v hu hv huend hvend s]
      exact h s]
  exact quadraticRay_nonnegative_iff_schur hvNonnegative

/-! ## Reflection transport of the endpoint-adapted split -/

private theorem fiveCellEvenEndpointReserve_even :
    Function.Even fiveCellEvenEndpointReserve := by
  intro x
  unfold fiveCellEvenEndpointReserve
  rw [← eval_centeredShiftedLegendreReal,
    ← eval_centeredShiftedLegendreReal,
    eval_centeredShiftedLegendreReal_neg]
  norm_num

private theorem fiveCellOddEndpointReserve_odd :
    Function.Odd fiveCellOddEndpointReserve := by
  intro x
  unfold fiveCellOddEndpointReserve
  rw [← eval_centeredShiftedLegendreReal,
    ← eval_centeredShiftedLegendreReal,
    eval_centeredShiftedLegendreReal_neg]
  norm_num

private theorem fiveCellEndpointAdaptedLow_even
    (e : ℝ → ℝ) (hec : Continuous e) (heven : Function.Even e) :
    Function.Even (fiveCellEndpointAdaptedLow e hec) := by
  let p := centeredLegendreLowProjection e hec 9
  have hpEven : Function.Even p := by
    simpa only [p] using centeredLegendreLowProjection_even e hec heven 9
  have hpNeg : p (-1) = p 1 := by
    have h := hpEven 1
    norm_num at h ⊢
    exact h
  have halt : fiveCellLowEndpointAlternating e hec = 0 := by
    unfold fiveCellLowEndpointAlternating
    change (p (-1) - p 1) / 2 = 0
    rw [hpNeg]
    ring
  intro x
  unfold fiveCellEndpointAdaptedLow
  change p (-x) - fiveCellLowEndpointMean e hec *
      fiveCellEvenEndpointReserve (-x) -
        fiveCellLowEndpointAlternating e hec *
          fiveCellOddEndpointReserve (-x) = _
  rw [hpEven x, fiveCellEvenEndpointReserve_even x, halt]
  ring

private theorem fiveCellEndpointAdaptedLow_odd
    (o : ℝ → ℝ) (hoc : Continuous o) (hodd : Function.Odd o) :
    Function.Odd (fiveCellEndpointAdaptedLow o hoc) := by
  let p := centeredLegendreLowProjection o hoc 9
  have hpOdd : Function.Odd p := by
    simpa only [p] using centeredLegendreLowProjection_odd o hoc hodd 9
  have hpNeg : p (-1) = -p 1 := by
    have h := hpOdd 1
    norm_num at h ⊢
    exact h
  have hmean : fiveCellLowEndpointMean o hoc = 0 := by
    unfold fiveCellLowEndpointMean
    change (p (-1) + p 1) / 2 = 0
    rw [hpNeg]
    ring
  intro x
  unfold fiveCellEndpointAdaptedLow
  change p (-x) - fiveCellLowEndpointMean o hoc *
      fiveCellEvenEndpointReserve (-x) -
        fiveCellLowEndpointAlternating o hoc *
          fiveCellOddEndpointReserve (-x) = _
  rw [hpOdd x, fiveCellOddEndpointReserve_odd x, hmean]
  ring

private theorem factorTwoReflectionEvenPart_sub
    (u v : ℝ → ℝ) :
    factorTwoReflectionEvenPart (u - v) =
      factorTwoReflectionEvenPart u - factorTwoReflectionEvenPart v := by
  funext x
  unfold factorTwoReflectionEvenPart
  simp only [Pi.sub_apply]
  ring

private theorem factorTwoReflectionOddPart_sub
    (u v : ℝ → ℝ) :
    factorTwoReflectionOddPart (u - v) =
      factorTwoReflectionOddPart u - factorTwoReflectionOddPart v := by
  funext x
  unfold factorTwoReflectionOddPart
  simp only [Pi.sub_apply]
  ring

private theorem fiveCellEndpointAdaptedLow_congr
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (h : u = v) :
    fiveCellEndpointAdaptedLow u hu =
      fiveCellEndpointAdaptedLow v hv := by
  subst v
  rfl

private theorem fiveCellEndpointAdaptedLow_reflectionEven
    (w : ℝ → ℝ) (hw : Continuous w) :
    factorTwoReflectionEvenPart (fiveCellEndpointAdaptedLow w hw) =
      fiveCellEndpointAdaptedLow (factorTwoReflectionEvenPart w)
        (continuous_factorTwoReflectionEvenPart hw) := by
  let e := factorTwoReflectionEvenPart w
  let o := factorTwoReflectionOddPart w
  let hec : Continuous e := continuous_factorTwoReflectionEvenPart hw
  let hoc : Continuous o := continuous_factorTwoReflectionOddPart hw
  have heven : Function.Even e := factorTwoReflectionEvenPart_even w
  have hodd : Function.Odd o := factorTwoReflectionOddPart_odd w
  have hsplit : e + o = w := by
    simpa only [e, o] using factorTwoReflectionEvenPart_add_oddPart w
  have hlow : fiveCellEndpointAdaptedLow w hw =
      fiveCellEndpointAdaptedLow e hec +
        fiveCellEndpointAdaptedLow o hoc := by
    have hleft : fiveCellEndpointAdaptedLow w hw =
        fiveCellEndpointAdaptedLow (e + o) (hec.add hoc) :=
      fiveCellEndpointAdaptedLow_congr
        w (e + o) hw (hec.add hoc) hsplit.symm
    exact hleft.trans (fiveCellEndpointAdaptedLow_add e o hec hoc)
  have hle := fiveCellEndpointAdaptedLow_even e hec heven
  have hlo := fiveCellEndpointAdaptedLow_odd o hoc hodd
  change factorTwoReflectionEvenPart (fiveCellEndpointAdaptedLow w hw) =
    fiveCellEndpointAdaptedLow e hec
  funext x
  rw [hlow]
  unfold factorTwoReflectionEvenPart
  simp only [Pi.add_apply]
  rw [hle x, hlo x]
  ring

private theorem fiveCellEndpointAdaptedLow_reflectionOdd
    (w : ℝ → ℝ) (hw : Continuous w) :
    factorTwoReflectionOddPart (fiveCellEndpointAdaptedLow w hw) =
      fiveCellEndpointAdaptedLow (factorTwoReflectionOddPart w)
        (continuous_factorTwoReflectionOddPart hw) := by
  let e := factorTwoReflectionEvenPart w
  let o := factorTwoReflectionOddPart w
  let hec : Continuous e := continuous_factorTwoReflectionEvenPart hw
  let hoc : Continuous o := continuous_factorTwoReflectionOddPart hw
  have heven : Function.Even e := factorTwoReflectionEvenPart_even w
  have hodd : Function.Odd o := factorTwoReflectionOddPart_odd w
  have hsplit : e + o = w := by
    simpa only [e, o] using factorTwoReflectionEvenPart_add_oddPart w
  have hlow : fiveCellEndpointAdaptedLow w hw =
      fiveCellEndpointAdaptedLow e hec +
        fiveCellEndpointAdaptedLow o hoc := by
    have hleft : fiveCellEndpointAdaptedLow w hw =
        fiveCellEndpointAdaptedLow (e + o) (hec.add hoc) :=
      fiveCellEndpointAdaptedLow_congr
        w (e + o) hw (hec.add hoc) hsplit.symm
    exact hleft.trans (fiveCellEndpointAdaptedLow_add e o hec hoc)
  have hle := fiveCellEndpointAdaptedLow_even e hec heven
  have hlo := fiveCellEndpointAdaptedLow_odd o hoc hodd
  change factorTwoReflectionOddPart (fiveCellEndpointAdaptedLow w hw) =
    fiveCellEndpointAdaptedLow o hoc
  funext x
  rw [hlow]
  unfold factorTwoReflectionOddPart
  simp only [Pi.add_apply]
  rw [hle x, hlo x]
  ring

private theorem fiveCellEndpointAdaptedTail_reflectionEven
    (w : ℝ → ℝ) (hw : Continuous w) :
    factorTwoReflectionEvenPart (fiveCellEndpointAdaptedTail w hw) =
      fiveCellEndpointAdaptedTail (factorTwoReflectionEvenPart w)
        (continuous_factorTwoReflectionEvenPart hw) := by
  change factorTwoReflectionEvenPart
      (w - fiveCellEndpointAdaptedLow w hw) =
    factorTwoReflectionEvenPart w -
      fiveCellEndpointAdaptedLow (factorTwoReflectionEvenPart w)
        (continuous_factorTwoReflectionEvenPart hw)
  rw [factorTwoReflectionEvenPart_sub,
    fiveCellEndpointAdaptedLow_reflectionEven]

private theorem fiveCellEndpointAdaptedTail_reflectionOdd
    (w : ℝ → ℝ) (hw : Continuous w) :
    factorTwoReflectionOddPart (fiveCellEndpointAdaptedTail w hw) =
      fiveCellEndpointAdaptedTail (factorTwoReflectionOddPart w)
        (continuous_factorTwoReflectionOddPart hw) := by
  change factorTwoReflectionOddPart
      (w - fiveCellEndpointAdaptedLow w hw) =
    factorTwoReflectionOddPart w -
      fiveCellEndpointAdaptedLow (factorTwoReflectionOddPart w)
        (continuous_factorTwoReflectionOddPart hw)
  rw [factorTwoReflectionOddPart_sub,
    fiveCellEndpointAdaptedLow_reflectionOdd]

private theorem factorTwoReflectionEvenPart_endpoints_zero
    (w : ℝ → ℝ) (hend : w (-1) = 0 ∧ w 1 = 0) :
    factorTwoReflectionEvenPart w (-1) = 0 ∧
      factorTwoReflectionEvenPart w 1 = 0 := by
  constructor <;>
    norm_num [factorTwoReflectionEvenPart, hend.1, hend.2]

private theorem factorTwoReflectionOddPart_endpoints_zero
    (w : ℝ → ℝ) (hend : w (-1) = 0 ∧ w 1 = 0) :
    factorTwoReflectionOddPart w (-1) = 0 ∧
      factorTwoReflectionOddPart w 1 = 0 := by
  constructor <;>
    norm_num [factorTwoReflectionOddPart, hend.1, hend.2]

/-! ## Intrinsic same-parity frontier -/

/-- The exact two-channel analytic obligation after endpoint adaptation.
Each quantified low profile has only five, respectively four, real
coordinates.  The tail hypotheses are structural (smooth, endpoint-zero,
same parity, and above the ninth Legendre gap); the conclusion is one affine
ray inequality, not a matrix enumeration. -/
def FiveCellEndpointAdaptedIntrinsicParityRayNonnegative : Prop :=
  (∀ c0 c2 c4 c6 c8 : ℝ, ∀ r : ℝ → ℝ,
      ContDiff ℝ ∞ r →
      (r (-1) = 0 ∧ r 1 = 0) →
      Function.Even r →
      centeredLegendreMomentsVanishBelow r 9 →
      ∀ s : ℝ,
        0 ≤ fiveCellEndpointOperator
          (fiveCellEndpointAdaptedIntrinsicEvenProfile
              c0 c2 c4 c6 c8 + s • r)) ∧
    (∀ c1 c3 c5 c7 : ℝ, ∀ r : ℝ → ℝ,
      ContDiff ℝ ∞ r →
      (r (-1) = 0 ∧ r 1 = 0) →
      Function.Odd r →
      centeredLegendreMomentsVanishBelow r 9 →
      ∀ s : ℝ,
        0 ≤ fiveCellEndpointOperator
          (fiveCellEndpointAdaptedIntrinsicOddProfile
              c1 c3 c5 c7 + s • r))

/-- The two intrinsic ray inequalities close every finite diagonal and mixed
Schur term on the actual production split, hence the complete five-cell
factor-two domination target. -/
theorem realFiveCellFactorTwoDomination_of_intrinsicParityRays
    (hcert : FiveCellEndpointAdaptedIntrinsicParityRayNonnegative) :
    RealFiveCellFactorTwoDomination := by
  apply realFiveCellFactorTwoDomination_of_endpointAdaptedLowTailSchur
  intro parent _hparent k
  dsimp only
  let w := fiveCellNormalizedRealProfile parent k
  let hw : Continuous w :=
    (fiveCellNormalizedRealProfile_contDiff parent k).continuous
  let u := fiveCellEndpointAdaptedLow w hw
  let v := fiveCellEndpointAdaptedTail w hw
  let uE := factorTwoReflectionEvenPart u
  let uO := factorTwoReflectionOddPart u
  let vE := factorTwoReflectionEvenPart v
  let vO := factorTwoReflectionOddPart v
  let e := factorTwoReflectionEvenPart w
  let o := factorTwoReflectionOddPart w
  let hec : Continuous e := continuous_factorTwoReflectionEvenPart hw
  let hoc : Continuous o := continuous_factorTwoReflectionOddPart hw
  have heven : Function.Even e := by
    simpa only [e] using factorTwoReflectionEvenPart_even w
  have hodd : Function.Odd o := by
    simpa only [o] using factorTwoReflectionOddPart_odd w
  have huTop : ContDiff ℝ ∞ u := by
    simpa only [u] using contDiff_top_fiveCellEndpointAdaptedLow w hw
  have hvTop : ContDiff ℝ ∞ v := by
    simpa only [v, w, hw] using
      contDiff_top_fiveCellProductionEndpointAdaptedTail parent k
  have huETop : ContDiff ℝ ∞ uE := by
    dsimp only [uE]
    unfold factorTwoReflectionEvenPart
    fun_prop
  have huOTop : ContDiff ℝ ∞ uO := by
    dsimp only [uO]
    unfold factorTwoReflectionOddPart
    fun_prop
  have hvETop : ContDiff ℝ ∞ vE := by
    dsimp only [vE]
    unfold factorTwoReflectionEvenPart
    fun_prop
  have hvOTop : ContDiff ℝ ∞ vO := by
    dsimp only [vO]
    unfold factorTwoReflectionOddPart
    fun_prop
  have htraces := fiveCellProductionEndpointAdapted_traces_zero parent k
  have huEnd : u (-1) = 0 ∧ u 1 = 0 := by
    simpa only [u, w, hw] using htraces.1
  have hvEnd : v (-1) = 0 ∧ v 1 = 0 := by
    simpa only [v, w, hw] using htraces.2
  have huEEnd : uE (-1) = 0 ∧ uE 1 = 0 :=
    factorTwoReflectionEvenPart_endpoints_zero u huEnd
  have huOEnd : uO (-1) = 0 ∧ uO 1 = 0 :=
    factorTwoReflectionOddPart_endpoints_zero u huEnd
  have hvEEnd : vE (-1) = 0 ∧ vE 1 = 0 :=
    factorTwoReflectionEvenPart_endpoints_zero v hvEnd
  have hvOEnd : vO (-1) = 0 ∧ vO 1 = 0 :=
    factorTwoReflectionOddPart_endpoints_zero v hvEnd
  have hvEEven : Function.Even vE := by
    simpa only [vE] using factorTwoReflectionEvenPart_even v
  have hvOOdd : Function.Odd vO := by
    simpa only [vO] using factorTwoReflectionOddPart_odd v
  have huECoord : uE =
      fiveCellEndpointAdaptedIntrinsicEvenProfile
        (factorTwoCanonicalLegendreCoefficient e hec 0)
        (factorTwoCanonicalLegendreCoefficient e hec 2)
        (factorTwoCanonicalLegendreCoefficient e hec 4)
        (factorTwoCanonicalLegendreCoefficient e hec 6)
        (factorTwoCanonicalLegendreCoefficient e hec 8) := by
    calc
      uE = fiveCellEndpointAdaptedLow e hec := by
        simpa only [uE, u, e, hec] using
          fiveCellEndpointAdaptedLow_reflectionEven w hw
      _ = _ := fiveCellEndpointAdaptedLow_even_eq_intrinsic e hec heven
  have huOCoord : uO =
      fiveCellEndpointAdaptedIntrinsicOddProfile
        (-factorTwoCanonicalLegendreCoefficient o hoc 1)
        (-factorTwoCanonicalLegendreCoefficient o hoc 3)
        (-factorTwoCanonicalLegendreCoefficient o hoc 5)
        (-factorTwoCanonicalLegendreCoefficient o hoc 7) := by
    calc
      uO = fiveCellEndpointAdaptedLow o hoc := by
        simpa only [uO, u, o, hoc] using
          fiveCellEndpointAdaptedLow_reflectionOdd w hw
      _ = _ := fiveCellEndpointAdaptedLow_odd_eq_intrinsic o hoc hodd
  have hvEeq : vE = fiveCellEndpointAdaptedTail e hec := by
    simpa only [vE, v, e, hec] using
      fiveCellEndpointAdaptedTail_reflectionEven w hw
  have hvOeq : vO = fiveCellEndpointAdaptedTail o hoc := by
    simpa only [vO, v, o, hoc] using
      fiveCellEndpointAdaptedTail_reflectionOdd w hw
  have hvEMom : centeredLegendreMomentsVanishBelow vE 9 := by
    rw [hvEeq]
    exact fiveCellEndpointAdaptedTail_momentsVanishBelow e hec
  have hvOMom : centeredLegendreMomentsVanishBelow vO 9 := by
    rw [hvOeq]
    exact fiveCellEndpointAdaptedTail_momentsVanishBelow o hoc
  have hvENonnegative : 0 ≤ fiveCellEndpointOperator vE := by
    exact fiveCellEndpointOperator_nonnegative_of_tailNine vE
      hvETop.continuous
      ((hvETop.of_le (by norm_num)).contDiffOn.locallyLipschitzOn
        (convex_Icc (-1) 1)) hvEMom
  have hvONonnegative : 0 ≤ fiveCellEndpointOperator vO := by
    exact fiveCellEndpointOperator_nonnegative_of_tailNine vO
      hvOTop.continuous
      ((hvOTop.of_le (by norm_num)).contDiffOn.locallyLipschitzOn
        (convex_Icc (-1) 1)) hvOMom
  have heRayRaw := hcert.1
    (factorTwoCanonicalLegendreCoefficient e hec 0)
    (factorTwoCanonicalLegendreCoefficient e hec 2)
    (factorTwoCanonicalLegendreCoefficient e hec 4)
    (factorTwoCanonicalLegendreCoefficient e hec 6)
    (factorTwoCanonicalLegendreCoefficient e hec 8)
    vE hvETop hvEEnd hvEEven hvEMom
  have hoRayRaw := hcert.2
    (-factorTwoCanonicalLegendreCoefficient o hoc 1)
    (-factorTwoCanonicalLegendreCoefficient o hoc 3)
    (-factorTwoCanonicalLegendreCoefficient o hoc 5)
    (-factorTwoCanonicalLegendreCoefficient o hoc 7)
    vO hvOTop hvOEnd hvOOdd hvOMom
  have heRay : ∀ s : ℝ,
      0 ≤ fiveCellEndpointOperator (uE + s • vE) := by
    intro s
    rw [huECoord]
    exact heRayRaw s
  have hoRay : ∀ s : ℝ,
      0 ≤ fiveCellEndpointOperator (uO + s • vO) := by
    intro s
    rw [huOCoord]
    exact hoRayRaw s
  have heSchur :=
    (fiveCellEndpointOperator_forall_add_smul_nonnegative_iff_schur
      uE vE huETop hvETop huEEnd hvEEnd hvENonnegative).mp heRay
  have hoSchur :=
    (fiveCellEndpointOperator_forall_add_smul_nonnegative_iff_schur
      uO vO huOTop hvOTop huOEnd hvOEnd hvONonnegative).mp hoRay
  have hsplits :=
    fiveCellProductionEndpointAdapted_operator_eq_reflectionParity parent k
  have huSplit : fiveCellEndpointOperator u =
      fiveCellEndpointOperator uE + fiveCellEndpointOperator uO := by
    simpa only [u, uE, uO, w, hw] using hsplits.1
  have hvSplit : fiveCellEndpointOperator v =
      fiveCellEndpointOperator vE + fiveCellEndpointOperator vO := by
    simpa only [v, vE, vO, w, hw] using hsplits.2
  have hcrossSplit : fiveCellEndpointOperatorCross u v =
      fiveCellEndpointOperatorCross uE vE +
        fiveCellEndpointOperatorCross uO vO := by
    simpa only [u, v, uE, uO, vE, vO, w, hw] using
      fiveCellProductionEndpointAdapted_operatorCross_eq_reflectionParity
        parent k
  have hlow : 0 ≤ fiveCellEndpointOperator u := by
    rw [huSplit]
    exact add_nonneg heSchur.1 hoSchur.1
  have hmixed : fiveCellEndpointOperatorCross u v ^ 2 ≤
      fiveCellEndpointOperator u * fiveCellEndpointOperator v :=
    fiveCellEndpointOperatorCross_sq_le_of_reflectionParitySchur
      u v huSplit hvSplit hcrossSplit
      heSchur.1 hoSchur.1 hvENonnegative hvONonnegative
      heSchur.2 hoSchur.2
  simpa only [u, v] using And.intro hlow hmixed

/-! ## Strength audit of the universal ray certificate -/

/-- Universal positivity on smooth endpoint-zero profiles, separated by
reflection parity. -/
def FiveCellSmoothEndpointZeroParityNonnegative : Prop :=
  (∀ e : ℝ → ℝ,
      ContDiff ℝ ∞ e →
      (e (-1) = 0 ∧ e 1 = 0) →
      Function.Even e →
      0 ≤ fiveCellEndpointOperator e) ∧
    (∀ o : ℝ → ℝ,
      ContDiff ℝ ∞ o →
      (o (-1) = 0 ∧ o 1 = 0) →
      Function.Odd o →
      0 ≤ fiveCellEndpointOperator o)

/-- The universal intrinsic-ray certificate is not merely a finite-low
matrix condition: endpoint-adapted decomposition shows that it proves the
complete smooth endpoint-zero operator in each parity sector. -/
theorem smoothEndpointZeroParityNonnegative_of_intrinsicParityRays
    (hcert : FiveCellEndpointAdaptedIntrinsicParityRayNonnegative) :
    FiveCellSmoothEndpointZeroParityNonnegative := by
  constructor
  · intro e heTop heEnd heven
    let hec : Continuous e := heTop.continuous
    let u := fiveCellEndpointAdaptedLow e hec
    let v := fiveCellEndpointAdaptedTail e hec
    have huCoord : u =
        fiveCellEndpointAdaptedIntrinsicEvenProfile
          (factorTwoCanonicalLegendreCoefficient e hec 0)
          (factorTwoCanonicalLegendreCoefficient e hec 2)
          (factorTwoCanonicalLegendreCoefficient e hec 4)
          (factorTwoCanonicalLegendreCoefficient e hec 6)
          (factorTwoCanonicalLegendreCoefficient e hec 8) := by
      simpa only [u] using
        fiveCellEndpointAdaptedLow_even_eq_intrinsic e hec heven
    have hvTop : ContDiff ℝ ∞ v := by
      dsimp only [v]
      unfold fiveCellEndpointAdaptedTail
      exact heTop.sub (contDiff_top_fiveCellEndpointAdaptedLow e hec)
    have hvEnd : v (-1) = 0 ∧ v 1 = 0 := by
      simpa only [v] using
        fiveCellEndpointAdaptedTail_endpoints_zero e hec heEnd
    have huEven : Function.Even u := by
      simpa only [u] using fiveCellEndpointAdaptedLow_even e hec heven
    have hvEven : Function.Even v := by
      intro x
      dsimp only [v]
      unfold fiveCellEndpointAdaptedTail
      rw [heven x, fiveCellEndpointAdaptedLow_even e hec heven x]
    have hvMom : centeredLegendreMomentsVanishBelow v 9 := by
      simpa only [v] using
        fiveCellEndpointAdaptedTail_momentsVanishBelow e hec
    have hray := hcert.1
      (factorTwoCanonicalLegendreCoefficient e hec 0)
      (factorTwoCanonicalLegendreCoefficient e hec 2)
      (factorTwoCanonicalLegendreCoefficient e hec 4)
      (factorTwoCanonicalLegendreCoefficient e hec 6)
      (factorTwoCanonicalLegendreCoefficient e hec 8)
      v hvTop hvEnd hvEven hvMom 1
    have huv : u + v = e := by
      simpa only [u, v] using fiveCellEndpointAdaptedLow_add_tail e hec
    rw [← huv, huCoord]
    simpa using hray
  · intro o hoTop hoEnd hodd
    let hoc : Continuous o := hoTop.continuous
    let u := fiveCellEndpointAdaptedLow o hoc
    let v := fiveCellEndpointAdaptedTail o hoc
    have huCoord : u =
        fiveCellEndpointAdaptedIntrinsicOddProfile
          (-factorTwoCanonicalLegendreCoefficient o hoc 1)
          (-factorTwoCanonicalLegendreCoefficient o hoc 3)
          (-factorTwoCanonicalLegendreCoefficient o hoc 5)
          (-factorTwoCanonicalLegendreCoefficient o hoc 7) := by
      simpa only [u] using
        fiveCellEndpointAdaptedLow_odd_eq_intrinsic o hoc hodd
    have hvTop : ContDiff ℝ ∞ v := by
      dsimp only [v]
      unfold fiveCellEndpointAdaptedTail
      exact hoTop.sub (contDiff_top_fiveCellEndpointAdaptedLow o hoc)
    have hvEnd : v (-1) = 0 ∧ v 1 = 0 := by
      simpa only [v] using
        fiveCellEndpointAdaptedTail_endpoints_zero o hoc hoEnd
    have huOdd : Function.Odd u := by
      simpa only [u] using fiveCellEndpointAdaptedLow_odd o hoc hodd
    have hvOdd : Function.Odd v := by
      intro x
      dsimp only [v]
      unfold fiveCellEndpointAdaptedTail
      rw [hodd x, fiveCellEndpointAdaptedLow_odd o hoc hodd x]
      ring
    have hvMom : centeredLegendreMomentsVanishBelow v 9 := by
      simpa only [v] using
        fiveCellEndpointAdaptedTail_momentsVanishBelow o hoc
    have hray := hcert.2
      (-factorTwoCanonicalLegendreCoefficient o hoc 1)
      (-factorTwoCanonicalLegendreCoefficient o hoc 3)
      (-factorTwoCanonicalLegendreCoefficient o hoc 5)
      (-factorTwoCanonicalLegendreCoefficient o hoc 7)
      v hvTop hvEnd hvOdd hvMom 1
    have huv : u + v = o := by
      simpa only [u, v] using fiveCellEndpointAdaptedLow_add_tail o hoc
    rw [← huv, huCoord]
    simpa using hray

/-! ## The odd ray after retaining its shared degree-nine reserve -/

/-- The complete odd polynomial block below the genuine `P11+` residual.
Unlike the endpoint-adapted four-coordinate profile, its `P9` coefficient is
free: it absorbs the `P9` component of the original ninth-gap tail. -/
def fiveCellOddP11FiniteProfile
    (c1 c3 c5 c7 c9 : ℝ) : ℝ → ℝ :=
  factorTwoIntrinsicNineOddProfile c1 c3 c5 c7 +
    fun x ↦ c9 * factorTwoCenteredP9 x

theorem contDiff_top_fiveCellOddP11FiniteProfile
    (c1 c3 c5 c7 c9 : ℝ) :
    ContDiff ℝ ∞ (fiveCellOddP11FiniteProfile c1 c3 c5 c7 c9) := by
  unfold fiveCellOddP11FiniteProfile factorTwoIntrinsicNineOddProfile
    factorTwoIntrinsicEightOddProfile factorTwoIntrinsicSixOddTail
  apply ContDiff.add
  · apply ContDiff.add
    · apply ContDiff.add
      · unfold factorTwoOddStructuralLowProfile centeredP1 centeredP3
        fun_prop
      · unfold factorTwoCenteredP5
        fun_prop
    · rw [show factorTwoCenteredP7 = fun x ↦
          (429 * x ^ 7 - 693 * x ^ 5 + 315 * x ^ 3 - 35 * x) / 16 by
        funext x
        exact factorTwoCenteredP7_eq x]
      fun_prop
  · rw [show factorTwoCenteredP9 = fun x ↦
        (12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
          4620 * x ^ 3 + 315 * x) / 128 by
      funext x
      exact factorTwoCenteredP9_eq x]
    fun_prop

theorem fiveCellOddP11FiniteProfile_odd
    (c1 c3 c5 c7 c9 : ℝ) :
    Function.Odd (fiveCellOddP11FiniteProfile c1 c3 c5 c7 c9) := by
  intro x
  unfold fiveCellOddP11FiniteProfile factorTwoIntrinsicNineOddProfile
    factorTwoIntrinsicEightOddProfile factorTwoIntrinsicSixOddTail
    factorTwoOddStructuralLowProfile
  simp only [Pi.add_apply]
  rw [odd_factorTwoCenteredP5 x, odd_factorTwoCenteredP7 x,
    odd_factorTwoCenteredP9 x]
  unfold centeredP1 centeredP3
  ring

theorem fiveCellOddP11FiniteProfile_one
    (c1 c3 c5 c7 c9 : ℝ) :
    fiveCellOddP11FiniteProfile c1 c3 c5 c7 c9 1 =
      c1 + c3 + c5 + c7 + c9 := by
  unfold fiveCellOddP11FiniteProfile factorTwoIntrinsicNineOddProfile
    factorTwoIntrinsicEightOddProfile factorTwoIntrinsicSixOddTail
    factorTwoOddStructuralLowProfile centeredP1 centeredP3
    factorTwoCenteredP5
  simp only [Pi.add_apply]
  rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
  norm_num

private theorem fiveCellOddEndpointReserve_eq_neg_centeredP9 (x : ℝ) :
    fiveCellOddEndpointReserve x = -factorTwoCenteredP9 x := by
  unfold fiveCellOddEndpointReserve factorTwoCenteredP9
  ring

/-- Endpoint adaptation forces exactly the coefficient
`c9 = -(c1+c3+c5+c7)`.  This is the structural reason the original odd low
block has four coordinates while the coupled finite/`P11+` block has five. -/
theorem fiveCellEndpointAdaptedIntrinsicOddProfile_eq_P11Finite
    (c1 c3 c5 c7 : ℝ) :
    fiveCellEndpointAdaptedIntrinsicOddProfile c1 c3 c5 c7 =
      fiveCellOddP11FiniteProfile c1 c3 c5 c7
        (-(c1 + c3 + c5 + c7)) := by
  let p := factorTwoIntrinsicNineOddProfile c1 c3 c5 c7
  have hp1 : p 1 = c1 + c3 + c5 + c7 := by
    have h := fiveCellOddP11FiniteProfile_one c1 c3 c5 c7 0
    change p 1 + 0 * factorTwoCenteredP9 1 = _ at h
    simpa only [zero_mul, add_zero] using h
  funext x
  unfold fiveCellEndpointAdaptedIntrinsicOddProfile
  change p x + p 1 * fiveCellOddEndpointReserve x = _
  rw [hp1, fiveCellOddEndpointReserve_eq_neg_centeredP9]
  unfold fiveCellOddP11FiniteProfile
  change p x + (c1 + c3 + c5 + c7) * (-factorTwoCenteredP9 x) =
    p x + -(c1 + c3 + c5 + c7) * factorTwoCenteredP9 x
  ring

theorem contDiff_top_fiveCellEndpointAdaptedIntrinsicOddProfile
    (c1 c3 c5 c7 : ℝ) :
    ContDiff ℝ ∞
      (fiveCellEndpointAdaptedIntrinsicOddProfile c1 c3 c5 c7) := by
  rw [fiveCellEndpointAdaptedIntrinsicOddProfile_eq_P11Finite]
  exact contDiff_top_fiveCellOddP11FiniteProfile _ _ _ _ _

theorem fiveCellEndpointAdaptedIntrinsicOddProfile_odd
    (c1 c3 c5 c7 : ℝ) :
    Function.Odd
      (fiveCellEndpointAdaptedIntrinsicOddProfile c1 c3 c5 c7) := by
  rw [fiveCellEndpointAdaptedIntrinsicOddProfile_eq_P11Finite]
  exact fiveCellOddP11FiniteProfile_odd _ _ _ _ _

theorem fiveCellEndpointAdaptedIntrinsicOddProfile_endpoints_zero
    (c1 c3 c5 c7 : ℝ) :
    fiveCellEndpointAdaptedIntrinsicOddProfile c1 c3 c5 c7 (-1) = 0 ∧
      fiveCellEndpointAdaptedIntrinsicOddProfile c1 c3 c5 c7 1 = 0 := by
  let p := fiveCellEndpointAdaptedIntrinsicOddProfile c1 c3 c5 c7
  have hpOdd : Function.Odd p := by
    simpa only [p] using
      fiveCellEndpointAdaptedIntrinsicOddProfile_odd c1 c3 c5 c7
  have hpOne : p 1 = 0 := by
    rw [show p = fiveCellOddP11FiniteProfile c1 c3 c5 c7
        (-(c1 + c3 + c5 + c7)) by
      simpa only [p] using
        fiveCellEndpointAdaptedIntrinsicOddProfile_eq_P11Finite
          c1 c3 c5 c7,
      fiveCellOddP11FiniteProfile_one]
    ring
  constructor
  · have h := hpOdd 1
    norm_num at h ⊢
    change p (-1) = 0
    rw [h, hpOne]
    ring
  · exact hpOne

private theorem shiftedLegendreReal_one_centered_oddP11 (x : ℝ) :
    (shiftedLegendreReal 1).eval ((x + 1) / 2) = -centeredP1 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredP1]
  ring

private theorem shiftedLegendreReal_three_centered_oddP11 (x : ℝ) :
    (shiftedLegendreReal 3).eval ((x + 1) / 2) = -centeredP3 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredP3]
  ring

private theorem shiftedLegendreReal_five_centered_oddP11 (x : ℝ) :
    (shiftedLegendreReal 5).eval ((x + 1) / 2) =
      -factorTwoCenteredP5 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, factorTwoCenteredP5]
  ring

private theorem shiftedLegendreReal_seven_centered_oddP11 (x : ℝ) :
    (shiftedLegendreReal 7).eval ((x + 1) / 2) =
      -factorTwoCenteredP7 x := by
  have h := centeredPullback_factorTwoCenteredP7 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  linarith

private theorem shiftedLegendreReal_nine_centered_oddP11 (x : ℝ) :
    (shiftedLegendreReal 9).eval ((x + 1) / 2) =
      -factorTwoCenteredP9 x := by
  have h := centeredPullback_factorTwoCenteredP9 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  linarith

/-- Exact five-coordinate description of the cutoff-eleven projection of
an arbitrary odd profile.  Parity kills all six even coefficients at once;
the five surviving odd coefficients are retained symbolically. -/
theorem centeredLegendreLowProjection_eleven_eq_oddP11FiniteProfile
    (o : ℝ → ℝ) (hoc : Continuous o) (hodd : Function.Odd o) :
    centeredLegendreLowProjection o hoc 11 =
      fiveCellOddP11FiniteProfile
        (-factorTwoCanonicalLegendreCoefficient o hoc 1)
        (-factorTwoCanonicalLegendreCoefficient o hoc 3)
        (-factorTwoCanonicalLegendreCoefficient o hoc 5)
        (-factorTwoCanonicalLegendreCoefficient o hoc 7)
        (-factorTwoCanonicalLegendreCoefficient o hoc 9) := by
  have h0 := centeredPullback_repr_eq_zero_of_odd_of_even
    o (centeredPullback_memLp_two o hoc) hodd 0 (by norm_num : Even 0)
  have h2 := centeredPullback_repr_eq_zero_of_odd_of_even
    o (centeredPullback_memLp_two o hoc) hodd 2 (by norm_num : Even 2)
  have h4 := centeredPullback_repr_eq_zero_of_odd_of_even
    o (centeredPullback_memLp_two o hoc) hodd 4 (by norm_num : Even 4)
  have h6 := centeredPullback_repr_eq_zero_of_odd_of_even
    o (centeredPullback_memLp_two o hoc) hodd 6 (by norm_num : Even 6)
  have h8 := centeredPullback_repr_eq_zero_of_odd_of_even
    o (centeredPullback_memLp_two o hoc) hodd 8 (by norm_num : Even 8)
  have h10 := centeredPullback_repr_eq_zero_of_odd_of_even
    o (centeredPullback_memLp_two o hoc) hodd 10 (by norm_num : Even 10)
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 o hoc) 0 = 0 at h0
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 o hoc) 2 = 0 at h2
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 o hoc) 4 = 0 at h4
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 o hoc) 6 = 0 at h6
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 o hoc) 8 = 0 at h8
  change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 o hoc) 10 = 0 at h10
  funext x
  unfold centeredLegendreLowProjection centeredLegendreProjectionPolynomial
    shiftedLegendrePartialProjectionPolynomial
  rw [Polynomial.eval_finset_sum]
  simp only [normalizedShiftedLegendrePolynomial, Polynomial.eval_smul,
    smul_eq_mul, Finset.sum_range_succ, Finset.sum_range_zero,
    h0, h2, h4, h6, h8, h10, zero_mul, zero_add, add_zero]
  rw [shiftedLegendreReal_one_centered_oddP11,
    shiftedLegendreReal_three_centered_oddP11,
    shiftedLegendreReal_five_centered_oddP11,
    shiftedLegendreReal_seven_centered_oddP11,
    shiftedLegendreReal_nine_centered_oddP11]
  unfold fiveCellOddP11FiniteProfile factorTwoIntrinsicNineOddProfile
    factorTwoIntrinsicEightOddProfile factorTwoIntrinsicSixOddTail
    factorTwoOddStructuralLowProfile factorTwoCanonicalLegendreCoefficient
  simp only [Pi.add_apply]
  ring

/-- Finite diagonal obligation on the complete five-mode odd block. -/
def FiveCellOddP11FiniteDiagonalNonnegative : Prop :=
  ∀ c1 c3 c5 c7 c9 : ℝ,
    0 ≤ fiveCellEndpointOperator
      (fiveCellOddP11FiniteProfile c1 c3 c5 c7 c9)

/-- The sole infinite-dimensional odd obligation after retaining `P9`.
The residual begins at `P11`; its endpoint trace is not discarded, but is
kept as the exact condition that the reconstructed profile vanish at both
endpoints. -/
def FiveCellOddP11MixedSchur : Prop :=
  ∀ (c1 c3 c5 c7 c9 : ℝ) (r : ℝ → ℝ),
    Continuous r →
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) r →
    Function.Odd r →
    centeredLegendreMomentsVanishBelow r 11 →
    ((fiveCellOddP11FiniteProfile c1 c3 c5 c7 c9 + r) (-1) = 0 ∧
      (fiveCellOddP11FiniteProfile c1 c3 c5 c7 c9 + r) 1 = 0) →
    fiveCellEndpointOperatorCross
        (fiveCellOddP11FiniteProfile c1 c3 c5 c7 c9) r ^ 2 ≤
      fiveCellEndpointOperator
          (fiveCellOddP11FiniteProfile c1 c3 c5 c7 c9) *
        fiveCellEndpointOperator r

/-- Exact odd closure from the five-mode diagonal and the genuine `P11+`
Schur contraction.  The residual diagonal is discharged structurally by the
existing ninth-gap coercivity theorem. -/
theorem fiveCellEndpointOperator_nonnegative_of_odd_P11Schur
    (hfinite : FiveCellOddP11FiniteDiagonalNonnegative)
    (hmixed : FiveCellOddP11MixedSchur)
    (o : ℝ → ℝ) (hoTop : ContDiff ℝ ∞ o)
    (hoEnd : o (-1) = 0 ∧ o 1 = 0) (hodd : Function.Odd o) :
    0 ≤ fiveCellEndpointOperator o := by
  let hoc : Continuous o := hoTop.continuous
  let p := centeredLegendreLowProjection o hoc 11
  let r := centeredLegendreHigherResidual o hoc 11
  let c1 := -factorTwoCanonicalLegendreCoefficient o hoc 1
  let c3 := -factorTwoCanonicalLegendreCoefficient o hoc 3
  let c5 := -factorTwoCanonicalLegendreCoefficient o hoc 5
  let c7 := -factorTwoCanonicalLegendreCoefficient o hoc 7
  let c9 := -factorTwoCanonicalLegendreCoefficient o hoc 9
  have hpCoord : p = fiveCellOddP11FiniteProfile c1 c3 c5 c7 c9 := by
    simpa only [p, c1, c3, c5, c7, c9] using
      centeredLegendreLowProjection_eleven_eq_oddP11FiniteProfile
        o hoc hodd
  have hrContinuous : Continuous r := by
    simpa only [r] using
      continuous_centeredLegendreHigherResidual o hoc 11
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    simpa only [r] using
      locallyLipschitzOn_centeredLegendreHigherResidual o hoc
        ((hoTop.of_le (by norm_num)).contDiffOn.locallyLipschitzOn
          (convex_Icc (-1) 1)) 11
  have hrOdd : Function.Odd r := by
    simpa only [r] using
      centeredLegendreHigherResidual_odd o hoc hodd 11
  have hrGap11 : centeredLegendreMomentsVanishBelow r 11 := by
    simpa only [r] using
      centeredLegendreHigherResidual_momentsVanishBelow o hoc 11
  have hrGap9 : centeredLegendreMomentsVanishBelow r 9 := by
    intro n hn
    exact hrGap11 n (by omega)
  have hreconstruct : p + r = o := by
    simpa only [p, r] using
      centeredLegendreLowProjection_add_higherResidual o hoc 11
  have hprofileEnd :
      (fiveCellOddP11FiniteProfile c1 c3 c5 c7 c9 + r) (-1) = 0 ∧
        (fiveCellOddP11FiniteProfile c1 c3 c5 c7 c9 + r) 1 = 0 := by
    rw [← hpCoord, hreconstruct]
    exact hoEnd
  have hpNonnegative := hfinite c1 c3 c5 c7 c9
  have hrNonnegative := fiveCellEndpointOperator_nonnegative_of_odd_tailNine
    r hrContinuous hrLocal hrOdd hrGap9
  have hcross := hmixed c1 c3 c5 c7 c9 r hrContinuous hrLocal hrOdd
    hrGap11 hprofileEnd
  rw [← hpCoord] at hpNonnegative hcross
  rw [← hreconstruct]
  exact fiveCellEndpointOperator_add_nonnegative_of_schur
    p r hpNonnegative hrNonnegative hcross

/-- Consequently the same two structural obligations close every actual
endpoint-adapted odd ninth-gap ray used by the production split. -/
theorem fiveCellEndpointAdaptedIntrinsicOddRay_nonnegative_of_P11Schur
    (hfinite : FiveCellOddP11FiniteDiagonalNonnegative)
    (hmixed : FiveCellOddP11MixedSchur)
    (c1 c3 c5 c7 : ℝ) (r : ℝ → ℝ)
    (hrTop : ContDiff ℝ ∞ r)
    (hrEnd : r (-1) = 0 ∧ r 1 = 0)
    (hrOdd : Function.Odd r)
    (_hrGap : centeredLegendreMomentsVanishBelow r 9)
    (s : ℝ) :
    0 ≤ fiveCellEndpointOperator
      (fiveCellEndpointAdaptedIntrinsicOddProfile c1 c3 c5 c7 + s • r) := by
  let p := fiveCellEndpointAdaptedIntrinsicOddProfile c1 c3 c5 c7
  let w := p + s • r
  have hpTop : ContDiff ℝ ∞ p := by
    simpa only [p] using
      contDiff_top_fiveCellEndpointAdaptedIntrinsicOddProfile c1 c3 c5 c7
  have hpEnd : p (-1) = 0 ∧ p 1 = 0 := by
    simpa only [p] using
      fiveCellEndpointAdaptedIntrinsicOddProfile_endpoints_zero c1 c3 c5 c7
  have hpOdd : Function.Odd p := by
    simpa only [p] using
      fiveCellEndpointAdaptedIntrinsicOddProfile_odd c1 c3 c5 c7
  have hwTop : ContDiff ℝ ∞ w := by
    dsimp only [w]
    exact hpTop.add (by
      simpa only [Pi.smul_apply, smul_eq_mul] using contDiff_const.mul hrTop)
  have hwEnd : w (-1) = 0 ∧ w 1 = 0 := by
    constructor
    · dsimp only [w]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hpEnd.1, hrEnd.1]
      ring
    · dsimp only [w]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hpEnd.2, hrEnd.2]
      ring
  have hwOdd : Function.Odd w := by
    intro x
    dsimp only [w]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hpOdd x, hrOdd x]
    ring
  simpa only [w, p] using
    fiveCellEndpointOperator_nonnegative_of_odd_P11Schur
      hfinite hmixed w hwTop hwEnd hwOdd


end

end ArithmeticHodge.Analysis.YoshidaFiveCellEndpointParitySchurClosureStructural
