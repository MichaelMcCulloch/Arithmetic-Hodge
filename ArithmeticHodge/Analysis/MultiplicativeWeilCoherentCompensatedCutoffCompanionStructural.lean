import ArithmeticHodge.Analysis.MultiplicativeWeilMellinBumpSequence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ContDiff Distributions Interval

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCompensatedCutoffCompanionStructural

noncomputable section

open MultiplicativeWeil

private theorem eq_zero_lt_of_tsupport_subset_Icc
    (q : BombieriTest) {a b x : ℝ}
    (hq : tsupport q ⊆ Set.Icc a b) (hx : x < a) :
    q x = 0 := by
  by_contra hne
  have hxt : x ∈ tsupport q :=
    subset_tsupport q (Function.mem_support.mpr hne)
  exact (not_le_of_gt hx) (hq hxt).1

private theorem eq_zero_gt_of_tsupport_subset_Icc
    (q : BombieriTest) {a b x : ℝ}
    (hq : tsupport q ⊆ Set.Icc a b) (hx : b < x) :
    q x = 0 := by
  by_contra hne
  have hxt : x ∈ tsupport q :=
    subset_tsupport q (Function.mem_support.mpr hne)
  exact (not_le_of_gt hx) (hq hxt).2

/-- A smooth source supported in a positive closed interval and of zero
ordinary mass on the positive half-line has a Bombieri primitive supported
in exactly the same closed interval. -/
theorem exists_bombieri_companion_of_zeroMass
    (q : BombieriTest) {a b : ℝ}
    (ha : 0 < a)
    (hq : tsupport q ⊆ Set.Icc a b)
    (hmass : (∫ z : ℝ in Set.Ioi 0, q z) = 0) :
    ∃ U : BombieriTest,
      tsupport U ⊆ Set.Icc a b ∧
      ∀ z : ℝ, deriv U z = q z := by
  let Q : ℝ → ℂ := fun x ↦ ∫ t : ℝ in a..x, q t
  have hqcont : Continuous (q : ℝ → ℂ) := q.contDiff.continuous
  have hqint : Integrable (q : ℝ → ℂ) :=
    hqcont.integrable_of_hasCompactSupport q.hasCompactSupport
  have hQderiv (x : ℝ) : HasDerivAt Q (q x) x := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hqcont.intervalIntegrable a x)
      hqcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hqcont.continuousAt
  have hQsmooth : ContDiff ℝ ∞ Q := by
    rw [contDiff_infty_iff_deriv]
    constructor
    · exact fun x ↦ (hQderiv x).differentiableAt
    · have hderiv : deriv Q = (q : ℝ → ℂ) := by
        funext x
        exact (hQderiv x).deriv
      rw [hderiv]
      exact q.contDiff
  have hQzero_left {x : ℝ} (hx : x < a) : Q x = 0 := by
    dsimp only [Q]
    rw [intervalIntegral.integral_of_ge hx.le,
      integral_Ioc_eq_integral_Ioo]
    simp only [neg_eq_zero]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact eq_zero_lt_of_tsupport_subset_Icc q hq ht.2
  have hzero_interval_zero_a : (∫ t : ℝ in (0 : ℝ)..a, q t) = 0 := by
    rw [intervalIntegral.integral_of_le ha.le,
      integral_Ioc_eq_integral_Ioo]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact eq_zero_lt_of_tsupport_subset_Icc q hq ht.2
  have hmass_a : (∫ z : ℝ in Set.Ioi a, q z) = 0 := by
    have hsplit := intervalIntegral.integral_Ioi_sub_Ioi
      (f := (q : ℝ → ℂ)) hqint.integrableOn ha.le
    rw [hmass, hzero_interval_zero_a] at hsplit
    simpa using hsplit
  have hQzero_right {x : ℝ} (hx : b < x) : Q x = 0 := by
    have htail : (∫ z : ℝ in Set.Ioi x, q z) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact eq_zero_gt_of_tsupport_subset_Icc q hq (hx.trans ht)
    have hsplit := intervalIntegral.integral_interval_add_Ioi
      (f := (q : ℝ → ℂ))
      (hqint.integrableOn : IntegrableOn (q : ℝ → ℂ) (Set.Ioi a))
      (hqint.integrableOn : IntegrableOn (q : ℝ → ℂ) (Set.Ioi x))
    change Q x + (∫ z : ℝ in Set.Ioi x, q z) =
      (∫ z : ℝ in Set.Ioi a, q z) at hsplit
    rw [htail, hmass_a, add_zero] at hsplit
    exact hsplit
  have hQfunSupport : Function.support Q ⊆ Set.Icc a b := by
    intro x hx
    by_contra hout
    simp only [Set.mem_Icc, not_and_or, not_le] at hout
    rcases hout with hxleft | hxright
    · exact hx (hQzero_left hxleft)
    · exact hx (hQzero_right hxright)
  have hQcompact : HasCompactSupport Q :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hQfunSupport
  have hQsupport : tsupport Q ⊆ Set.Icc a b :=
    isClosed_Icc.closure_subset_iff.mpr hQfunSupport
  let U : BombieriTest := TestFunction.mk Q hQsmooth hQcompact (by
    exact hQsupport.trans (fun x hx ↦ ha.trans_le hx.1))
  refine ⟨U, ?_, ?_⟩
  · exact hQsupport
  · intro z
    exact (hQderiv z).deriv

/-- Subtracting the mass of `eta' * parent` times a same-window unit-mass
bump gives a zero-mass source whose primitive remains in that same window. -/
theorem exists_compensatedCutoffDerivative_companion
    (parent rho : BombieriTest) (eta : ℝ → ℝ)
    (heta : ContDiff ℝ ∞ eta)
    {a b : ℝ} (ha : 0 < a)
    (hparent : tsupport parent ⊆ Set.Icc a b)
    (hrho : tsupport rho ⊆ Set.Icc a b)
    (hrhoMass : (∫ z : ℝ in Set.Ioi 0, rho z) = 1) :
    ∃ U : BombieriTest,
      tsupport U ⊆ Set.Icc a b ∧
      ∀ z : ℝ,
        deriv U z =
          ((deriv eta z : ℝ) : ℂ) * parent z -
            (∫ w : ℝ in Set.Ioi 0,
              ((deriv eta w : ℝ) : ℂ) * parent w) * rho z := by
  have hetaDeriv : ContDiff ℝ ∞ (deriv eta) :=
    (contDiff_infty_iff_deriv.mp heta).2
  have hweight : ContDiff ℝ ∞
      (fun z : ℝ ↦ ((deriv eta z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hetaDeriv
  let weighted : BombieriTest := TestFunction.mk
    (fun z : ℝ ↦ ((deriv eta z : ℝ) : ℂ) * parent z)
    (hweight.mul parent.contDiff)
    parent.hasCompactSupport.mul_left
    ((tsupport_mul_subset_right :
      tsupport (fun z : ℝ ↦
        ((deriv eta z : ℝ) : ℂ) * parent z) ⊆
          tsupport (parent : ℝ → ℂ)).trans parent.tsupport_subset)
  let mass : ℂ := ∫ z : ℝ in Set.Ioi 0, weighted z
  let q : BombieriTest := weighted - mass • rho
  have hweightedSupport : tsupport weighted ⊆ Set.Icc a b := by
    change tsupport (fun z : ℝ ↦
      ((deriv eta z : ℝ) : ℂ) * parent z) ⊆ Set.Icc a b
    exact (tsupport_mul_subset_right :
      tsupport (fun z : ℝ ↦
        ((deriv eta z : ℝ) : ℂ) * parent z) ⊆
          tsupport (parent : ℝ → ℂ)).trans hparent
  have hqSupport : tsupport q ⊆ Set.Icc a b := by
    change tsupport (fun z : ℝ ↦ weighted z - mass * rho z) ⊆
      Set.Icc a b
    exact (tsupport_sub (weighted : ℝ → ℂ)
      (fun z : ℝ ↦ mass * rho z)).trans
        (Set.union_subset hweightedSupport
          ((tsupport_mul_subset_right :
            tsupport (fun z : ℝ ↦ mass * rho z) ⊆
              tsupport (rho : ℝ → ℂ)).trans hrho))
  have hweightedInt : Integrable
      (weighted : ℝ → ℂ) (volume.restrict (Set.Ioi 0)) :=
    weighted.contDiff.continuous.integrable_of_hasCompactSupport
      weighted.hasCompactSupport |>.integrableOn
  have hrhoInt : Integrable
      (rho : ℝ → ℂ) (volume.restrict (Set.Ioi 0)) :=
    rho.contDiff.continuous.integrable_of_hasCompactSupport
      rho.hasCompactSupport |>.integrableOn
  have hqMass : (∫ z : ℝ in Set.Ioi 0, q z) = 0 := by
    change (∫ z : ℝ in Set.Ioi 0, weighted z - mass * rho z) = 0
    rw [integral_sub hweightedInt (hrhoInt.const_mul mass)]
    have hmul : (∫ z : ℝ in Set.Ioi 0, mass * rho z) =
        mass * (∫ z : ℝ in Set.Ioi 0, rho z) := by
      exact integral_const_mul mass (rho : ℝ → ℂ)
    rw [hmul, hrhoMass]
    change mass - mass * 1 = 0
    ring
  obtain ⟨U, hUsupport, hUderiv⟩ :=
    exists_bombieri_companion_of_zeroMass q ha hqSupport hqMass
  refine ⟨U, hUsupport, ?_⟩
  intro z
  have hz := hUderiv z
  change deriv U z = weighted z - mass * rho z at hz
  change deriv U z =
    ((deriv eta z : ℝ) : ℂ) * parent z -
      (∫ w : ℝ in Set.Ioi 0,
        ((deriv eta w : ℝ) : ℂ) * parent w) * rho z
  simpa only [weighted, mass] using hz

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCompensatedCutoffCompanionStructural
