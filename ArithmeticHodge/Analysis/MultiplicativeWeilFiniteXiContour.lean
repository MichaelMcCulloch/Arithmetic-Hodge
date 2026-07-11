import ArithmeticHodge.Analysis.Contour.XiRectangleArgumentPrinciple
import ArithmeticHodge.Analysis.MultiplicativeWeil
import ArithmeticHodge.Analysis.MultiplicativeWeilXiBoundary
import ArithmeticHodge.Analysis.XiZeroFreeHeight

/-!
# Finite Bombieri--xi contour formula

The Mellin transform of a Bombieri test is entire.  Consequently the weighted
xi argument principle and the codiscrete xi/zeta/gamma boundary rewrite combine
into an exact finite zero-sum formula on every zero-free rectangle.
-/

set_option autoImplicit false

open Asymptotics Complex Filter MeasureTheory Set Topology
open scoped ContDiff Distributions Interval Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private theorem bombieriTest_eventuallyEq_zero_atTop
    (f : BombieriTest) :
    (f : ℝ → ℂ) =ᶠ[atTop] 0 := by
  have hcompact : (f : ℝ → ℂ) =ᶠ[coclosedCompact ℝ] 0 :=
    hasCompactSupport_iff_eventuallyEq.mp f.hasCompactSupport
  rw [Filter.coclosedCompact_eq_cocompact] at hcompact
  exact hcompact.filter_mono _root_.atTop_le_cocompact

private theorem bombieriTest_eventuallyEq_zero_nhdsGT_zero
    (f : BombieriTest) :
    (f : ℝ → ℂ) =ᶠ[𝓝[>] 0] 0 := by
  have hzero_notMem : (0 : ℝ) ∉ tsupport (f : ℝ → ℂ) := by
    intro hzero
    have hpos := f.tsupport_subset hzero
    change (0 : ℝ) < 0 at hpos
    exact (lt_irrefl 0) hpos
  have hcompl : (tsupport (f : ℝ → ℂ))ᶜ ∈ 𝓝 (0 : ℝ) :=
    (isClosed_tsupport (f : ℝ → ℂ)).isOpen_compl.mem_nhds hzero_notMem
  have hzero : (f : ℝ → ℂ) =ᶠ[𝓝 (0 : ℝ)] 0 := by
    filter_upwards [hcompl] with x hx
    exact image_eq_zero_of_notMem_tsupport hx
  exact hzero.filter_mono inf_le_left

/-- The Mellin transform of a compactly supported smooth test on `(0,∞)` is
entire. -/
theorem bombieriMellin_differentiable (f : BombieriTest) :
    Differentiable ℂ (mellin (f : ℝ → ℂ)) := by
  intro s
  let a : ℝ := s.re + 1
  let b : ℝ := s.re - 1
  have hlocal : LocallyIntegrableOn (f : ℝ → ℂ) (Ioi 0) :=
    f.contDiff.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htop : (f : ℝ → ℂ) =O[atTop] (fun x : ℝ ↦ x ^ (-a)) :=
    (Asymptotics.isBigO_zero (fun x : ℝ ↦ x ^ (-a)) atTop).congr'
      (bombieriTest_eventuallyEq_zero_atTop f).symm EventuallyEq.rfl
  have hbot : (f : ℝ → ℂ) =O[𝓝[>] 0] (fun x : ℝ ↦ x ^ (-b)) :=
    (Asymptotics.isBigO_zero (fun x : ℝ ↦ x ^ (-b)) (𝓝[>] 0)).congr'
      (bombieriTest_eventuallyEq_zero_nhdsGT_zero f).symm EventuallyEq.rfl
  exact mellin_differentiableAt_of_isBigO_rpow hlocal htop
    (by simp only [a]; linarith) hbot (by simp only [b]; linarith)

private theorem bombieriMellin_analyticOnNhd
    (f : BombieriTest) (U : Set ℂ) :
    AnalyticOnNhd ℂ (mellin (f : ℝ → ℂ)) U := by
  intro s _
  exact (bombieriMellin_differentiable f).analyticAt s

/-- Exact normalized finite Bombieri zero-sum formula on any rectangle whose
boundary is free of xi zeros. -/
theorem bombieriFiniteXiContour_of_boundary_zero_free
    (f : BombieriTest) {z w : ℂ}
    (hrew : z.re < w.re) (himw : z.im < w.im)
    (hboundary : ∀ s ∈ xiZeroRectangle z.re w.re z.im w.im,
      s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im →
      xiFunction s ≠ 0) :
    ∑ rho ∈ xiZerosInRectangle z.re w.re z.im w.im,
        (xiZeroMultiplicity rho : ℂ) * mellin (f : ℝ → ℂ) rho =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        rectIntegral
          (fun s ↦ mellin (f : ℝ → ℂ) s *
            (deriv riemannZeta s / riemannZeta s +
              1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
                Complex.digamma (s / 2) / 2)) z w := by
  let M : ℂ → ℂ := mellin (f : ℝ → ℂ)
  have hxi :=
    Contour.rectIntegral_xi_logDeriv_of_boundary_zero_free
      (H := M) hrew himw
      (bombieriMellin_analyticOnNhd f
        ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) hboundary
  have hrewrite :=
    rectIntegral_weighted_xi_logDeriv_eq_zeta_gamma_polar M z w
  have hexplicit :
      rectIntegral
          (fun s ↦ M s *
            (deriv riemannZeta s / riemannZeta s +
              1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
                Complex.digamma (s / 2) / 2)) z w =
        2 * (Real.pi : ℂ) * I *
          ∑ rho ∈ xiZerosInRectangle z.re w.re z.im w.im,
            (xiZeroMultiplicity rho : ℂ) * M rho :=
    hrewrite.symm.trans hxi
  rw [show (fun s ↦ mellin (f : ℝ → ℂ) s *
      (deriv riemannZeta s / riemannZeta s +
        1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
          Complex.digamma (s / 2) / 2)) =
      fun s ↦ M s *
      (deriv riemannZeta s / riemannZeta s +
        1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
          Complex.digamma (s / 2) / 2) by rfl]
  rw [hexplicit]
  have hfactor : 2 * (Real.pi : ℂ) * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  simp only [M]
  field_simp

/-- On `[0,1] × [-T,T]`, paired horizontal nonvanishing suffices because
xi's vertical boundary is automatically zero-free. -/
theorem bombieriFiniteCriticalStripXiContour_of_horizontal_pair
    (f : BombieriTest) {T : ℝ} (hT : 0 < T)
    (hupper : ∀ σ ∈ Set.Icc (0 : ℝ) 1,
      xiFunction (σ + T * I) ≠ 0)
    (hlower : ∀ σ ∈ Set.Icc (0 : ℝ) 1,
      xiFunction (σ - T * I) ≠ 0) :
    ∑ rho ∈ xiZerosInRectangle 0 1 (-T) T,
        (xiZeroMultiplicity rho : ℂ) * mellin (f : ℝ → ℂ) rho =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        rectIntegral
          (fun s ↦ mellin (f : ℝ → ℂ) s *
            (deriv riemannZeta s / riemannZeta s +
              1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
                Complex.digamma (s / 2) / 2))
          ((-T : ℂ) * I) (1 + (T : ℂ) * I) := by
  let z : ℂ := (-T : ℂ) * I
  let w : ℂ := 1 + (T : ℂ) * I
  have hrew : z.re < w.re := by simp [z, w]
  have himw : z.im < w.im := by
    simp only [z, w, mul_im, neg_re, neg_im, ofReal_re, I_im, ofReal_im,
      I_re, mul_one, zero_mul, add_zero, add_im, one_im, zero_add]
    linarith
  have hboundary : ∀ s ∈ xiZeroRectangle z.re w.re z.im w.im,
      s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im →
      xiFunction s ≠ 0 := by
    intro s hs hedge hzero
    have hsrect : s ∈ xiZeroRectangle 0 1 (-T) T := by
      simpa [z, w] using hs
    have hsfin : s ∈ xiZerosInRectangle 0 1 (-T) T :=
      (mem_xiZerosInRectangle_iff 0 1 (-T) T s).2 ⟨hsrect, hzero⟩
    have hinterior :=
      xiZerosInRectangle_strict_interior_of_horizontal_pair hupper hlower s hsfin
    have hedge' :
        s.re = 0 ∨ s.re = 1 ∨ s.im = -T ∨ s.im = T := by
      simpa [z, w] using hedge
    rcases hedge' with hre0 | hre1 | him0 | him1
    · exact (ne_of_gt hinterior.1) hre0
    · exact (ne_of_lt hinterior.2.1) hre1
    · exact (ne_of_gt hinterior.2.2.1) him0
    · exact (ne_of_lt hinterior.2.2.2) him1
  have h := bombieriFiniteXiContour_of_boundary_zero_free
    f (z := z) (w := w) hrew himw hboundary
  simpa [z, w] using h

/-- With fixed vertical sides strictly outside the critical strip, paired
horizontal nonvanishing gives the same critical-strip zero sum while putting
the right edge in the zeta Dirichlet-series half-plane. -/
theorem bombieriFiniteOuterXiContour_of_horizontal_pair
    (f : BombieriTest) {sigmaLower sigmaUpper T : ℝ}
    (hlower : sigmaLower < 0) (hupper : 1 < sigmaUpper) (hT : 0 < T)
    (htop : ∀ σ ∈ Set.Icc sigmaLower sigmaUpper,
      xiFunction (σ + T * I) ≠ 0)
    (hbottom : ∀ σ ∈ Set.Icc sigmaLower sigmaUpper,
      xiFunction (σ - T * I) ≠ 0) :
    ∑ rho ∈ xiZerosInRectangle 0 1 (-T) T,
        (xiZeroMultiplicity rho : ℂ) * mellin (f : ℝ → ℂ) rho =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        rectIntegral
          (fun s ↦ mellin (f : ℝ → ℂ) s *
            (deriv riemannZeta s / riemannZeta s +
              1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
                Complex.digamma (s / 2) / 2))
          ((sigmaLower : ℂ) - (T : ℂ) * I)
          ((sigmaUpper : ℂ) + (T : ℂ) * I) := by
  let z : ℂ := (sigmaLower : ℂ) - (T : ℂ) * I
  let w : ℂ := (sigmaUpper : ℂ) + (T : ℂ) * I
  have hrew : z.re < w.re := by
    simp only [z, w, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      zero_mul, mul_zero, sub_zero, add_re, add_zero]
    linarith
  have himw : z.im < w.im := by
    simp only [z, w, sub_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      zero_mul, mul_one, zero_sub, add_im, zero_add]
    linarith
  have hboundary : ∀ s ∈ xiZeroRectangle z.re w.re z.im w.im,
      s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im →
      xiFunction s ≠ 0 := by
    intro s hs hedge hzero
    have hsrect : s ∈ xiZeroRectangle sigmaLower sigmaUpper (-T) T := by
      simpa [z, w] using hs
    have hcoords := hsrect
    rw [xiZeroRectangle, mem_reProdIm] at hcoords
    have hedge' : s.re = sigmaLower ∨ s.re = sigmaUpper ∨
        s.im = -T ∨ s.im = T := by
      simpa [z, w] using hedge
    have hre := xiFunction_zero_re hzero
    rcases hedge' with hreL | hreU | himL | himU
    · linarith
    · linarith
    · have heq : (s.re : ℂ) - T * I = s := by
        apply Complex.ext
        · simp
        · simp [← himL]
      exact hbottom s.re hcoords.1 (by simpa only [heq] using hzero)
    · have heq : (s.re : ℂ) + T * I = s := by
        apply Complex.ext
        · simp
        · simp [himU]
      exact htop s.re hcoords.1 (by simpa only [heq] using hzero)
  have h := bombieriFiniteXiContour_of_boundary_zero_free
    f (z := z) (w := w) hrew himw hboundary
  have h' :
      ∑ rho ∈ xiZerosInRectangle sigmaLower sigmaUpper (-T) T,
          (xiZeroMultiplicity rho : ℂ) * mellin (f : ℝ → ℂ) rho =
        (2 * (Real.pi : ℂ) * I)⁻¹ *
          rectIntegral
            (fun s ↦ mellin (f : ℝ → ℂ) s *
              (deriv riemannZeta s / riemannZeta s +
                1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
                  Complex.digamma (s / 2) / 2)) z w := by
    simpa [z, w] using h
  rw [xiZerosInRectangle_outer_eq_critical hlower.le hupper.le] at h'
  exact h'

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
