import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCorrectedPotentialStructural
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false

open Complex Finset MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction ContDiff

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFarOuterIntegrabilityStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilCorrectedChebyshevPotentialStructural
open MultiplicativeWeilDirectedCorrelationPhysicalStructural
open MultiplicativeWeilDirectedCorrelationSmoothStructural

/-- A compactly supported `C¹` derivative remains integrable after
multiplication by the Chebyshev error.  This is the local integrability step
inside the finite Abel proof, exported separately for finite-sum exchange. -/
theorem chebyshevError_mul_deriv_integrableOn_Ioi
    (H : ℝ → ℂ) (hH : ContDiff ℝ 1 H)
    {a b : ℝ}
    (hsupport : tsupport H ⊆ Set.Icc a b) :
    IntegrableOn (fun x : ℝ ↦
      ((Chebyshev.psi x - x : ℝ) : ℂ) * deriv H x) (Set.Ioi 0) := by
  let c : ℕ → ℂ := fun n ↦
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (max b 2)
  have hbN : b < (N : ℝ) :=
    (le_max_left b 2).trans_lt hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hderivZero (x : ℝ) (hx : (N : ℝ) < x) : deriv H x = 0 := by
    apply deriv_of_notMem_tsupport
    intro hxmem
    have hxb := (hsupport hxmem).2
    exact (not_lt_of_ge hxb) (hbN.trans_le hx.le)
  have hpsi (x : ℝ) :
      (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k) =
        ((Chebyshev.psi x : ℝ) : ℂ) := by
    dsimp only [c]
    rw [Chebyshev.psi_eq_sum_Icc]
    push_cast
    rfl
  have hderivInt : IntegrableOn (deriv H) (Set.Icc 0 (N : ℝ)) :=
    (hH.continuous_deriv (by norm_num)).integrableOn_Icc
  have hsumInt := integrableOn_mul_sum_Icc
    (m := 0) (a := 0) (b := (N : ℝ)) c (by norm_num) hderivInt
  have hpsiInt : IntegrableOn
      (fun x : ℝ ↦ ((Chebyshev.psi x : ℝ) : ℂ) * deriv H x)
      (Set.Icc 0 (N : ℝ)) := by
    refine hsumInt.congr_fun ?_ measurableSet_Icc
    intro x _hx
    change deriv H x * (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k) =
      ((Chebyshev.psi x : ℝ) : ℂ) * deriv H x
    rw [hpsi]
    ring
  have hxInt : IntegrableOn
      (fun x : ℝ ↦ (x : ℂ) * deriv H x)
      (Set.Icc 0 (N : ℝ)) := by
    exact (Complex.ofRealCLM.continuous.mul
      (hH.continuous_deriv (by norm_num))).integrableOn_Icc
  have herrorInt : IntegrableOn (fun x : ℝ ↦
      ((Chebyshev.psi x - x : ℝ) : ℂ) * deriv H x)
      (Set.Icc 0 (N : ℝ)) := by
    refine (hpsiInt.sub hxInt).congr_fun ?_ measurableSet_Icc
    intro x _hx
    change ((Chebyshev.psi x : ℝ) : ℂ) * deriv H x -
      (x : ℂ) * deriv H x = _
    push_cast
    ring
  apply herrorInt.of_forall_diff_eq_zero measurableSet_Ioi
  intro x hx
  have hxN : (N : ℝ) < x := by
    by_contra hnot
    exact hx.2 ⟨le_of_lt hx.1, le_of_not_gt hnot⟩
  rw [hderivZero x hxN, mul_zero]

/-- A compactly supported `C¹` derivative supported strictly to the right of
the pole is integrable against the corrected Chebyshev potential. -/
theorem correctedPotential_mul_deriv_integrableOn_Ioi
    (H : ℝ → ℂ) (hH : ContDiff ℝ 1 H)
    {a b : ℝ} (ha : 1 < a)
    (hsupport : tsupport H ⊆ Set.Icc a b) :
    IntegrableOn (fun x : ℝ ↦
      ((correctedChebyshevPotential x : ℝ) : ℂ) * deriv H x)
      (Set.Ioi 0) := by
  have hpotential : ContinuousOn
      (fun x : ℝ ↦ ((correctedChebyshevPotential x : ℝ) : ℂ))
      (Set.Icc a b) := by
    intro x hx
    exact Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
      (hasDerivAt_correctedChebyshevPotential
        (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  have hderiv : ContinuousOn (deriv H) (Set.Icc a b) :=
    (hH.continuous_deriv (by norm_num)).continuousOn
  have hlocal : IntegrableOn (fun x : ℝ ↦
      ((correctedChebyshevPotential x : ℝ) : ℂ) * deriv H x)
      (Set.Icc a b) :=
    (hpotential.mul hderiv).integrableOn_Icc
  apply hlocal.of_forall_diff_eq_zero measurableSet_Ioi
  intro x hx
  have hxNot : x ∉ tsupport H := by
    intro hxt
    exact hx.2 (hsupport hxt)
  have hd : deriv H x = 0 := deriv_of_notMem_tsupport hxNot
  rw [hd, mul_zero]

private def starDirectedCorrelation (f h : BombieriTest) (x : ℝ) : ℂ :=
  starRingEnd ℂ (bombieriDirectedCorrelation f h x)

private theorem starDirectedCorrelation_tsupport_subset
    (f h : BombieriTest) {af bf ah bh : ℝ}
    (haf : 0 < af) (hah : 0 < ah) (hbh : 0 < bh)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hh : tsupport h ⊆ Set.Icc ah bh) :
    tsupport (starDirectedCorrelation f h) ⊆
      Set.Icc (af / bh) (bf / ah) := by
  apply isClosed_Icc.closure_subset_iff.mpr
  intro x hx
  by_contra hout
  exact hx
    (star_bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
      f h haf hah hbh hf hh hout)

/-- The Chebyshev-error term in every strictly separated coherent pair is
integrable on the positive half-line. -/
theorem chebyshevError_mul_deriv_star_directedCorrelation_integrableOn
    (f h : BombieriTest) {af bf ah bh : ℝ}
    (hah : 0 < ah) (hbh : 0 < bh)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hh : tsupport h ⊆ Set.Icc ah bh)
    (hsep : bh < af) :
    IntegrableOn (fun x : ℝ ↦
      ((Chebyshev.psi x - x : ℝ) : ℂ) *
        deriv (fun y : ℝ ↦
          starRingEnd ℂ (bombieriDirectedCorrelation f h y)) x)
      (Set.Ioi 0) := by
  have haf : 0 < af := hbh.trans hsep
  let a : ℝ := af / bh
  let b : ℝ := max a (bf / ah)
  have hsuppBase := starDirectedCorrelation_tsupport_subset
    f h haf hah hbh hf hh
  have hsupp : tsupport (starDirectedCorrelation f h) ⊆ Set.Icc a b := by
    intro x hx
    have hx' := hsuppBase hx
    exact ⟨hx'.1, hx'.2.trans (le_max_right _ _)⟩
  exact chebyshevError_mul_deriv_integrableOn_Ioi
    (starDirectedCorrelation f h)
    (star_bombieriDirectedCorrelation_contDiff_one f h)
    hsupp

/-- The corrected-potential term in every strictly separated coherent pair
is integrable on the positive half-line. -/
theorem correctedPotential_mul_deriv_star_directedCorrelation_integrableOn
    (f h : BombieriTest) {af bf ah bh : ℝ}
    (hah : 0 < ah) (hbh : 0 < bh)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hh : tsupport h ⊆ Set.Icc ah bh)
    (hsep : bh < af) :
    IntegrableOn (fun x : ℝ ↦
      ((correctedChebyshevPotential x : ℝ) : ℂ) *
        deriv (fun y : ℝ ↦
          starRingEnd ℂ (bombieriDirectedCorrelation f h y)) x)
      (Set.Ioi 0) := by
  have haf : 0 < af := hbh.trans hsep
  let a : ℝ := af / bh
  let b : ℝ := max a (bf / ah)
  have ha : 1 < a := by
    dsimp only [a]
    rw [one_lt_div hbh]
    exact hsep
  have hsuppBase := starDirectedCorrelation_tsupport_subset
    f h haf hah hbh hf hh
  have hsupp : tsupport (starDirectedCorrelation f h) ⊆ Set.Icc a b := by
    intro x hx
    have hx' := hsuppBase hx
    exact ⟨hx'.1, hx'.2.trans (le_max_right _ _)⟩
  exact correctedPotential_mul_deriv_integrableOn_Ioi
    (starDirectedCorrelation f h)
    (star_bombieriDirectedCorrelation_contDiff_one f h)
    ha hsupp

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFarOuterIntegrabilityStructural
