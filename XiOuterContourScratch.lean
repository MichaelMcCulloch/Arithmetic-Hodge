import ArithmeticHodge.Analysis.Contour.XiRectangleArgumentPrinciple
import ArithmeticHodge.Analysis.XiZeroFreeHeight

set_option autoImplicit false

open Complex Filter Set
open scoped Interval Real

namespace ArithmeticHodge.Analysis

noncomputable section

theorem xiZerosInRectangle_outer_eq_critical_scratch
    {sigmaLower sigmaUpper heightLower heightUpper : ℝ}
    (hlower : sigmaLower ≤ 0) (hupper : 1 ≤ sigmaUpper) :
    xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper =
      xiZerosInRectangle 0 1 heightLower heightUpper := by
  ext z
  simp only [mem_xiZerosInRectangle_iff]
  constructor
  · rintro ⟨hzrect, hzero⟩
    have hre := xiFunction_zero_re hzero
    rw [xiZeroRectangle, mem_reProdIm] at hzrect ⊢
    exact ⟨⟨⟨hre.1.le, hre.2.le⟩, hzrect.2⟩, hzero⟩
  · rintro ⟨hzrect, hzero⟩
    rw [xiZeroRectangle, mem_reProdIm] at hzrect ⊢
    exact ⟨⟨⟨hlower.trans hzrect.1.1, hzrect.1.2.trans hupper⟩,
      hzrect.2⟩, hzero⟩

theorem exists_xi_outer_contour_sequence_scratch
    (sigmaLower sigmaUpper : ℝ)
    (hlower : sigmaLower < 0) (hupper : 1 < sigmaUpper)
    (H : ℂ → ℂ) (hH : Differentiable ℂ H) :
    ∃ T : ℕ → ℝ,
      Tendsto T atTop atTop ∧
      ∀ n : ℕ,
        (n : ℝ) < T n ∧ T n < (n : ℝ) + 1 ∧
        (∀ σ ∈ Set.Icc sigmaLower sigmaUpper,
          xiFunction (σ + T n * I) ≠ 0) ∧
        (∀ σ ∈ Set.Icc sigmaLower sigmaUpper,
          xiFunction (σ - T n * I) ≠ 0) ∧
        rectIntegral (fun s => H s * logDeriv xiFunction s)
            ((sigmaLower : ℂ) - T n * I)
            ((sigmaUpper : ℂ) + T n * I) =
          2 * (Real.pi : ℂ) * I *
            ∑ rho ∈ xiZerosInRectangle 0 1 (-T n) (T n),
              (xiZeroMultiplicity rho : ℂ) * H rho := by
  classical
  let T : ℕ → ℝ := fun n =>
    Classical.choose
      (exists_xi_zero_free_horizontal_pair_between
        sigmaLower sigmaUpper (n : ℝ) ((n : ℝ) + 1)
        (Nat.cast_nonneg n) (by linarith))
  have hspec (n : ℕ) :
      T n ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1) ∧
      (∀ σ ∈ Set.Icc sigmaLower sigmaUpper,
        xiFunction (σ + T n * I) ≠ 0) ∧
      (∀ σ ∈ Set.Icc sigmaLower sigmaUpper,
        xiFunction (σ - T n * I) ≠ 0) :=
    Classical.choose_spec
      (exists_xi_zero_free_horizontal_pair_between
        sigmaLower sigmaUpper (n : ℝ) ((n : ℝ) + 1)
        (Nat.cast_nonneg n) (by linarith))
  have hT_tendsto : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun n => (hspec n).1.1.le)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  refine ⟨T, hT_tendsto, fun n =>
    ⟨(hspec n).1.1, (hspec n).1.2, (hspec n).2.1,
      (hspec n).2.2, ?_⟩⟩
  have hT_pos : 0 < T n := (Nat.cast_nonneg n).trans_lt (hspec n).1.1
  have hH_univ : AnalyticOnNhd ℂ H Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hH
  have hinterior : ∀ rho ∈
      xiZerosInRectangle sigmaLower sigmaUpper (-T n) (T n),
      sigmaLower < rho.re ∧ rho.re < sigmaUpper ∧
        -T n < rho.im ∧ rho.im < T n := by
    intro rho hrho
    have hdata := (mem_xiZerosInRectangle_iff
      sigmaLower sigmaUpper (-T n) (T n) rho).1 hrho
    have hrect := hdata.1
    rw [xiZeroRectangle, mem_reProdIm] at hrect
    have hre := xiFunction_zero_re hdata.2
    refine ⟨hlower.trans hre.1, hre.2.trans hupper, ?_, ?_⟩
    · apply lt_of_le_of_ne hrect.2.1
      intro heq
      have hrho_eq : (rho.re : ℂ) - T n * I = rho := by
        apply Complex.ext
        · simp
        · simp [← heq]
      exact (hspec n).2.2 rho.re hrect.1
        (by simpa only [hrho_eq] using hdata.2)
    · apply lt_of_le_of_ne hrect.2.2
      intro heq
      have hrho_eq : (rho.re : ℂ) + T n * I = rho := by
        apply Complex.ext
        · simp
        · simp [heq]
      exact (hspec n).2.1 rho.re hrect.1
        (by simpa only [hrho_eq] using hdata.2)
  have hcontour := Contour.rectIntegral_xi_logDeriv
    (H := H)
    (z := (sigmaLower : ℂ) - T n * I)
    (w := (sigmaUpper : ℂ) + T n * I)
    (by
      simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        zero_mul, mul_zero, sub_zero, add_re, add_zero]
      linarith)
    (by simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      zero_mul, add_zero, mul_one, zero_sub, add_im]; linarith)
    (hH_univ.mono (Set.subset_univ _))
    (by simpa using hinterior)
  have hcontour' :
      rectIntegral (fun s => H s * logDeriv xiFunction s)
          ((sigmaLower : ℂ) - T n * I)
          ((sigmaUpper : ℂ) + T n * I) =
        2 * (Real.pi : ℂ) * I *
          ∑ rho ∈ xiZerosInRectangle sigmaLower sigmaUpper (-T n) (T n),
            (xiZeroMultiplicity rho : ℂ) * H rho := by
    simpa using hcontour
  rw [xiZerosInRectangle_outer_eq_critical_scratch hlower.le hupper.le] at hcontour'
  exact hcontour'

#print axioms xiZerosInRectangle_outer_eq_critical_scratch
#print axioms exists_xi_outer_contour_sequence_scratch

end

end ArithmeticHodge.Analysis
