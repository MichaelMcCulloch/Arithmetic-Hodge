import ArithmeticHodge.Analysis.MultiplicativeWeilFunctional
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions SchwartzMap FourierTransform

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The Mellin transform of a Bombieri test is the Fourier transform of its
weighted logarithmic pullback, with Mathlib's `2 * pi` normalization. -/
theorem bombieriMellin_eq_fourier_logarithmicPullback
    (f : BombieriTest) (s : ℂ) :
    mellin (f : ℝ → ℂ) s =
      𝓕 (f.logarithmicPullbackSchwartz s.re) (s.im / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  rfl

/-- On a fixed vertical line, the Mellin transform is the Fourier transform
of a single Schwartz function. -/
theorem bombieriMellin_vertical_eq_fourier
    (f : BombieriTest) (σ t : ℝ) :
    mellin (f : ℝ → ℂ) (σ + t * I) =
      𝓕 (f.logarithmicPullbackSchwartz σ) (t / (2 * Real.pi)) := by
  simpa using
    bombieriMellin_eq_fourier_logarithmicPullback f (σ + t * I)

/-- Mellin transforms of Bombieri tests decay faster than every power on
each fixed vertical line.  The `2 * pi` scaling is kept explicit so the
bound is exactly the native Schwartz estimate. -/
theorem bombieriMellin_vertical_rapidDecay
    (f : BombieriTest) (σ : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      |t / (2 * Real.pi)| ^ k *
          ‖mellin (f : ℝ → ℂ) (σ + t * I)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    (𝓕 (f.logarithmicPullbackSchwartz σ)).decay k 0
  refine ⟨C, hC, fun t ↦ ?_⟩
  rw [bombieriMellin_vertical_eq_fourier]
  simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_zero] using
    hbound (t / (2 * Real.pi))

/-- The Mellin transform of a Bombieri test is integrable on every vertical
line.  This closes the `VerticalIntegrable` hypothesis in Mathlib's Mellin
inversion theorem without any extra assumption. -/
theorem BombieriTest.mellin_verticalIntegrable
    (f : BombieriTest) (σ : ℝ) :
    VerticalIntegrable (mellin (f : ℝ → ℂ)) σ := by
  let F : SchwartzMap ℝ ℂ :=
    𝓕 (f.logarithmicPullbackSchwartz σ)
  have hfourier : Integrable (F : ℝ → ℂ) := F.integrable
  have hscaled := hfourier.comp_div
    (show 2 * Real.pi ≠ 0 by positivity)
  change Integrable (fun t : ℝ ↦
    mellin (f : ℝ → ℂ) (σ + t * I))
  rw [show (fun t : ℝ ↦ mellin (f : ℝ → ℂ) (σ + t * I)) =
      fun t : ℝ ↦ F (t / (2 * Real.pi)) by
    funext t
    exact bombieriMellin_vertical_eq_fourier f σ t]
  exact hscaled

/-- Mellin inversion is unconditional on the bundled Bombieri test space:
compact smooth support supplies both Mellin convergence and the newly proved
vertical integrability. -/
theorem BombieriTest.mellinInv_mellin_eq
    (f : BombieriTest) (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (mellin (f : ℝ → ℂ)) x = f x := by
  exact _root_.mellinInv_mellin_eq σ (f : ℝ → ℂ) hx
    (f.mellinConvergent σ) (f.mellin_verticalIntegrable σ)
    f.contDiff.continuous.continuousAt

/-- A single positive Dirichlet-series term on a vertical Mellin line
integrates to evaluation of the test function.  This is the atomic identity
behind the prime-side contour calculation. -/
theorem bombieriMellin_integral_mul_LSeriesTerm
    (f : BombieriTest) (a : ℕ → ℂ) (σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, mellin (f : ℝ → ℂ) (σ + t * I) *
          LSeries.term a (σ + t * I) n =
      a n * f n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hinv := f.mellinInv_mellin_eq σ hnpos
  rw [← hinv]
  unfold mellinInv
  simp_rw [LSeries.term_of_ne_zero hn]
  simp only [smul_eq_mul]
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  change c * (∫ t : ℝ, mellin (f : ℝ → ℂ) (σ + t * I) *
      (a n / (n : ℂ) ^ (σ + t * I))) =
    a n * (c * ∫ t : ℝ,
      (n : ℂ) ^ (-(σ + t * I)) *
        mellin (f : ℝ → ℂ) (σ + t * I))
  calc
    _ = c * ∫ t : ℝ, a n *
        ((n : ℂ) ^ (-(σ + t * I)) *
          mellin (f : ℝ → ℂ) (σ + t * I)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [div_eq_mul_inv, ← cpow_neg]
      ring
    _ = _ := by
      have hconst := MeasureTheory.integral_const_mul (μ := volume) (a n) (fun t : ℝ ↦
        (n : ℂ) ^ (-(σ + t * I)) *
          mellin (f : ℝ → ℂ) (σ + t * I))
      calc
        c * ∫ t : ℝ, a n *
            ((n : ℂ) ^ (-(σ + t * I)) *
              mellin (f : ℝ → ℂ) (σ + t * I)) =
            c * (a n * ∫ t : ℝ,
              (n : ℂ) ^ (-(σ + t * I)) *
                mellin (f : ℝ → ℂ) (σ + t * I)) :=
          congrArg (fun z : ℂ ↦ c * z) hconst
        _ = _ := by ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

#print axioms ArithmeticHodge.Analysis.MultiplicativeWeil.bombieriMellin_eq_fourier_logarithmicPullback
#print axioms ArithmeticHodge.Analysis.MultiplicativeWeil.bombieriMellin_vertical_rapidDecay
#print axioms ArithmeticHodge.Analysis.MultiplicativeWeil.BombieriTest.mellin_verticalIntegrable
#print axioms ArithmeticHodge.Analysis.MultiplicativeWeil.BombieriTest.mellinInv_mellin_eq
#print axioms ArithmeticHodge.Analysis.MultiplicativeWeil.bombieriMellin_integral_mul_LSeriesTerm
