import ArithmeticHodge.Analysis.Contour.RectangleFiniteResidues
import ArithmeticHodge.Analysis.Contour.RectangleMeromorphicGoursat
import ArithmeticHodge.Analysis.Contour.RectangleWeightedLogDeriv
import Mathlib.Analysis.Meromorphic.NormalForm

set_option autoImplicit false

open Complex Set Filter Topology
open scoped Interval Real

namespace ArithmeticHodge.Analysis.Contour

noncomputable section

theorem rectIntegral_weighted_logDeriv_scratch
    {F H : ℂ → ℂ} {S : Finset ℂ} {ord : ℂ → ℤ} {z w : ℂ}
    (hrew : z.re < w.re) (himw : z.im < w.im)
    (hF : MeromorphicOn F ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hH : AnalyticOnNhd ℂ H ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hsupp : ∀ s ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]),
      meromorphicOrderAt F s ≠ 0 → s ∈ S)
    (hord : ∀ rho ∈ S,
      meromorphicOrderAt F rho = (ord rho : WithTop ℤ))
    (hS : ∀ rho ∈ S,
      z.re < rho.re ∧ rho.re < w.re ∧ z.im < rho.im ∧ rho.im < w.im) :
    rectIntegral (fun s => H s * logDeriv F s) z w =
      2 * (Real.pi : ℂ) * I * ∑ rho ∈ S, (ord rho : ℂ) * H rho := by
  let R : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]
  let A : ℂ → ℂ := weightedLogDerivRemainder F H S ord
  let B : ℂ → ℂ := toMeromorphicNFOn A R
  have hrem := weightedLogDerivRemainder_meromorphicOn_order_nonneg
    S ord
    (by simpa only [uIcc_of_le hrew.le, uIcc_of_le himw.le] using hF)
    (by simpa only [uIcc_of_le hrew.le, uIcc_of_le himw.le] using hH)
    (by simpa only [uIcc_of_le hrew.le, uIcc_of_le himw.le] using hsupp)
    hord
  have hAmero : MeromorphicOn A R := by
    simpa only [A, R, uIcc_of_le hrew.le, uIcc_of_le himw.le] using hrem.1
  have hAord : ∀ s ∈ R, 0 ≤ meromorphicOrderAt A s := by
    simpa only [A, R, uIcc_of_le hrew.le, uIcc_of_le himw.le] using hrem.2
  have hB_nf : MeromorphicNFOn B R := by
    simpa only [B] using meromorphicNFOn_toMeromorphicNFOn A R
  have hB_an : AnalyticOnNhd ℂ B R := by
    intro s hs
    refine (hB_nf hs).meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
    rw [show meromorphicOrderAt B s = meromorphicOrderAt A s by
      simpa only [B] using meromorphicOrderAt_toMeromorphicNFOn hAmero hs]
    exact hAord s hs
  have hAB : A =ᶠ[codiscreteWithin R] B := by
    simpa only [B] using toMeromorphicNFOn_eqOn_codiscrete hAmero
  have htarget :
      (fun s => H s * logDeriv F s) =ᶠ[codiscreteWithin R]
        (fun s => B s + ∑ rho ∈ S, (ord rho : ℂ) * H rho * (s - rho)⁻¹) := by
    filter_upwards [hAB] with s hs
    let P : ℂ := ∑ rho ∈ S, (ord rho : ℂ) * H rho * (s - rho)⁻¹
    change H s * logDeriv F s = B s + P
    calc
      H s * logDeriv F s =
          (H s * logDeriv F s - P) + P := (sub_add_cancel _ _).symm
      _ = A s + P := by rfl
      _ = B s + P := congrArg (fun x => x + P) hs
  calc
    rectIntegral (fun s => H s * logDeriv F s) z w =
        rectIntegral
          (fun s => B s +
            ∑ rho ∈ S, (ord rho : ℂ) * H rho * (s - rho)⁻¹) z w :=
      ArithmeticHodge.Analysis.rectIntegral_congr_codiscreteWithin htarget
    _ = 2 * (Real.pi : ℂ) * I *
          ∑ rho ∈ S, (ord rho : ℂ) * H rho :=
      by
        simpa only [mul_one] using
          (rectIntegral_finite_simple_residues_add_remainder
            (G := B) (H := fun _ : ℂ => 1)
            (a := fun rho => (ord rho : ℂ) * H rho)
            (S := S) (z := z) (w := w) hrew himw
            (fun s hs => (hB_an s hs).differentiableAt)
            (fun _ _ => differentiableAt_const (c := (1 : ℂ))) hS)

#print axioms rectIntegral_weighted_logDeriv_scratch

end

end ArithmeticHodge.Analysis.Contour
