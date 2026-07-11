import ArithmeticHodge.Analysis.Contour.RectangleWeightedArgumentPrinciple
import ArithmeticHodge.Analysis.XiZeroMultiplicity

/-!
# The xi divisor on a rectangle

The weighted rectangular argument principle is specialized to the entire
Riemann xi function and its finite, enumeration-independent zero divisor.
-/

set_option autoImplicit false

open Complex Set
open scoped Interval Real

namespace ArithmeticHodge.Analysis.Contour

noncomputable section

/-- On a rectangle whose xi zeros are strictly interior, the contour integral
of `H · ξ'/ξ` is the finite sum of `H` over those zeros with analytic
multiplicity. -/
theorem rectIntegral_xi_logDeriv
    {H : ℂ → ℂ} {z w : ℂ}
    (hrew : z.re < w.re) (himw : z.im < w.im)
    (hH : AnalyticOnNhd ℂ H ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hinterior : ∀ rho ∈
      xiZerosInRectangle z.re w.re z.im w.im,
      z.re < rho.re ∧ rho.re < w.re ∧
        z.im < rho.im ∧ rho.im < w.im) :
    rectIntegral (fun s => H s * logDeriv xiFunction s) z w =
      2 * (Real.pi : ℂ) * I *
        ∑ rho ∈ xiZerosInRectangle z.re w.re z.im w.im,
          (xiZeroMultiplicity rho : ℂ) * H rho := by
  let S : Finset ℂ := xiZerosInRectangle z.re w.re z.im w.im
  have hxi_univ : AnalyticOnNhd ℂ xiFunction Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_xiFunction
  have hxi : MeromorphicOn xiFunction
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) :=
    fun s _ => hxi_univ.meromorphicOn s (Set.mem_univ s)
  have hsupp : ∀ s ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]),
      meromorphicOrderAt xiFunction s ≠ 0 → s ∈ S := by
    intro s hs horder
    have hmult : xiZeroMultiplicity s ≠ 0 := by
      intro hzero
      apply horder
      rw [meromorphicOrderAt_xiFunction_eq_xiZeroMultiplicity, hzero]
      simp
    have hxi_zero : xiFunction s = 0 :=
      (xiZeroMultiplicity_pos_iff s).mp (Nat.pos_of_ne_zero hmult)
    change s ∈ xiZerosInRectangle z.re w.re z.im w.im
    rw [mem_xiZerosInRectangle_iff]
    exact ⟨by
      simpa only [xiZeroRectangle, uIcc_of_le hrew.le,
        uIcc_of_le himw.le] using hs, hxi_zero⟩
  have hord : ∀ rho ∈ S,
      meromorphicOrderAt xiFunction rho =
        ((xiZeroMultiplicity rho : ℤ) : WithTop ℤ) := by
    intro rho _
    exact meromorphicOrderAt_xiFunction_eq_xiZeroMultiplicity rho
  simpa only [S, Int.cast_natCast] using
    (rectIntegral_weighted_logDeriv
      (F := xiFunction) (H := H) (S := S)
      (ord := fun rho => (xiZeroMultiplicity rho : ℤ))
      (z := z) (w := w) hrew himw hxi hH hsupp hord
      (by simpa only [S] using hinterior))

end

end ArithmeticHodge.Analysis.Contour
