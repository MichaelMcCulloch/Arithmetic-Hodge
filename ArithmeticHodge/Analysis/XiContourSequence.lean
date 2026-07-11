import ArithmeticHodge.Analysis.Contour.XiRectangleArgumentPrinciple
import ArithmeticHodge.Analysis.XiZeroFreeHeight

/-!
# Zero-free xi contour exhaustion

Every entire weight admits a sequence of paired zero-free rectangles exhausting
the critical strip.  On each rectangle the weighted argument principle is an
exact finite multiplicity sum.
-/

set_option autoImplicit false

open Complex Filter Set
open scoped Interval Real

namespace ArithmeticHodge.Analysis

/-- Choose paired zero-free heights tending to infinity and record the exact
finite weighted xi-divisor identity on every corresponding rectangle. -/
theorem exists_xi_contour_sequence
    (H : ℂ → ℂ) (hH : Differentiable ℂ H) :
    ∃ T : ℕ → ℝ,
      Tendsto T atTop atTop ∧
      ∀ n : ℕ,
        (n : ℝ) < T n ∧ T n < (n : ℝ) + 1 ∧
        (∀ σ ∈ Set.Icc (0 : ℝ) 1, xiFunction (σ + T n * I) ≠ 0) ∧
        (∀ σ ∈ Set.Icc (0 : ℝ) 1, xiFunction (σ - T n * I) ≠ 0) ∧
        rectIntegral (fun s => H s * logDeriv xiFunction s)
            ((0 : ℂ) - T n * I) ((1 : ℂ) + T n * I) =
          2 * (Real.pi : ℂ) * I *
            ∑ rho ∈ xiZerosInRectangle 0 1 (-T n) (T n),
              (xiZeroMultiplicity rho : ℂ) * H rho := by
  classical
  obtain ⟨T, hT_tendsto, hT⟩ := exists_xi_zero_free_horizontal_pair_sequence
  refine ⟨T, hT_tendsto, fun n =>
    ⟨(hT n).1, (hT n).2.1, (hT n).2.2.1, (hT n).2.2.2, ?_⟩⟩
  have hT_pos : 0 < T n := (Nat.cast_nonneg n).trans_lt (hT n).1
  have hH_univ : AnalyticOnNhd ℂ H Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hH
  have hinterior : ∀ rho ∈ xiZerosInRectangle 0 1 (-T n) (T n),
      0 < rho.re ∧ rho.re < 1 ∧ -T n < rho.im ∧ rho.im < T n :=
    xiZerosInRectangle_strict_interior_of_horizontal_pair
      (hT n).2.2.1 (hT n).2.2.2
  have hcontour := Contour.rectIntegral_xi_logDeriv
    (H := H)
    (z := (0 : ℂ) - T n * I)
    (w := (1 : ℂ) + T n * I)
    (by simp)
    (by simp only [sub_im, zero_im, mul_im, ofReal_re, I_im, ofReal_im,
      I_re, zero_mul, add_zero, mul_one, add_im, one_im]; linarith)
    (hH_univ.mono (Set.subset_univ _))
    (by simpa using hinterior)
  simpa using hcontour

end ArithmeticHodge.Analysis
