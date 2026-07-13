import ArithmeticHodge.Analysis.YoshidaBombieriCrossDistribution
import ArithmeticHodge.Analysis.YoshidaFactorTwoAdjacentKernel

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped FourierTransform SchwartzMap

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoCrossDistribution

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaCauchyPairing

/-!
# The adjacent factor-two cross distribution

For a ratio-two seed, the critical pullback and its normalized factor-two
dilation occupy adjacent logarithmic cells.  The cross-correlation therefore
lives on the one-sided interval `[0, 2 * log 2]`, and its zero-lag value
vanishes.  These facts remove every harmonic counterterm from the complex
digamma distribution without evaluating a finite certificate.
-/

def factorTwoLogLength : ℝ := Real.log 2

theorem factorTwoLogLength_pos : 0 < factorTwoLogLength := by
  exact Real.log_pos (by norm_num)

def factorTwoSelfCorrelation (g : BombieriTest) (s : ℝ) : ℂ :=
  crossCorrelation
    (g.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ)
    (g.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ) s

def factorTwoAdjacentCorrelation (g : BombieriTest) (u : ℝ) : ℂ :=
  bombieriCriticalCrossCorrelation g
    (normalizedDilation 2 (by norm_num) g) u

theorem factorTwoAdjacentCorrelation_eq_shift
    (g : BombieriTest) (u : ℝ) :
    factorTwoAdjacentCorrelation g u =
      factorTwoSelfCorrelation g (u - factorTwoLogLength) := by
  rw [factorTwoAdjacentCorrelation, bombieriCriticalCrossCorrelation,
    factorTwoSelfCorrelation, crossCorrelation_apply,
    crossCorrelation_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [normalizedDilation_logarithmicPullbackSchwartz_critical]
  congr 2
  unfold factorTwoLogLength
  ring

private theorem logarithmic_support_width_le_factorTwoLogLength
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hratio : b / a ≤ 2) :
    -Real.log a - -Real.log b ≤ factorTwoLogLength := by
  have hb : 0 < b := ha.trans_le hab
  have hlog : Real.log (b / a) ≤ Real.log 2 :=
    Real.log_le_log (div_pos hb ha) hratio
  rw [Real.log_div hb.ne' ha.ne'] at hlog
  change -Real.log a - -Real.log b ≤ Real.log 2
  linarith

theorem factorTwoAdjacentCorrelation_zero
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoAdjacentCorrelation g 0 = 0 := by
  let l : ℝ := -Real.log b
  let r : ℝ := -Real.log a
  let L : ℝ := factorTwoLogLength
  have hwidth : r - l ≤ L := by
    simpa only [l, r, L] using
      logarithmic_support_width_le_factorTwoLogLength ha hab hratio
  rw [factorTwoAdjacentCorrelation_eq_shift, factorTwoSelfCorrelation,
    crossCorrelation_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [(countable_singleton r).ae_notMem volume] with x hx
  by_cases hxleft : x ∈ Set.Icc l r
  · by_cases hxright : -L + x ∈ Set.Icc l r
    · have hxr : x = r := by
        apply le_antisymm hxleft.2
        linarith [hxright.1, hwidth]
      exact (hx (by simpa only [mem_singleton_iff] using hxr)).elim
    · have hz :
          g.logarithmicPullbackSchwartz (1 / 2)
              (0 - factorTwoLogLength + x) = 0 :=
        logarithmicPullbackSchwartz_eq_zero_outside
          g (a := a) (b := b) (u := 0 - factorTwoLogLength + x)
            ha hsupport (by
              simpa only [l, r, L, zero_sub] using hxright)
      rw [hz, mul_zero]
      simp
  · have hz : g.logarithmicPullbackSchwartz (1 / 2) x = 0 :=
      logarithmicPullbackSchwartz_eq_zero_outside
        g (a := a) (b := b) (u := x) ha hsupport
          (by simpa only [l, r] using hxleft)
    rw [hz, star_zero, zero_mul]
    simp

theorem factorTwoAdjacentCorrelation_eq_zero_outside
    (g : BombieriTest) {a b u : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hu : u ∉ Set.Icc 0 (2 * factorTwoLogLength)) :
    factorTwoAdjacentCorrelation g u = 0 := by
  let l : ℝ := -Real.log b
  let r : ℝ := -Real.log a
  let L : ℝ := factorTwoLogLength
  have hwidth : r - l ≤ L := by
    simpa only [l, r, L] using
      logarithmic_support_width_le_factorTwoLogLength ha hab hratio
  have hu' : u < 0 ∨ 2 * L < u := by
    simpa only [mem_Icc, not_and_or, not_le, L] using hu
  rw [factorTwoAdjacentCorrelation_eq_shift, factorTwoSelfCorrelation,
    crossCorrelation_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  by_cases hxleft : x ∈ Set.Icc l r
  · by_cases hxright : (u - L) + x ∈ Set.Icc l r
    · rcases hu' with hu_neg | hu_large
      · exfalso
        have : r < x := by
          linarith [hxright.1, hwidth]
        exact (not_lt_of_ge hxleft.2) this
      · exfalso
        have : x < l := by
          linarith [hxright.2, hwidth]
        exact (not_lt_of_ge hxleft.1) this
    · have hz :
          g.logarithmicPullbackSchwartz (1 / 2)
              (u - factorTwoLogLength + x) = 0 :=
        logarithmicPullbackSchwartz_eq_zero_outside
          g (a := a) (b := b) (u := u - factorTwoLogLength + x)
            ha hsupport (by simpa only [l, r, L] using hxright)
      rw [hz, mul_zero]
      simp
  · have hz : g.logarithmicPullbackSchwartz (1 / 2) x = 0 :=
      logarithmicPullbackSchwartz_eq_zero_outside
        g (a := a) (b := b) (u := x) ha hsupport
          (by simpa only [l, r] using hxleft)
    rw [hz, star_zero, zero_mul]
    simp

theorem factorTwoCriticalSpectralProduct_eq
    (g : BombieriTest) (v : ℝ) :
    bombieriCriticalSpectralProduct g
        (normalizedDilation 2 (by norm_num) g) v =
      starRingEnd ℂ
          (mellin (g : ℝ → ℂ)
            ((1 / 2 : ℝ) + v * Complex.I)) *
        (factorTwoMellinPhase v *
          mellin (g : ℝ → ℂ)
            ((1 / 2 : ℝ) + v * Complex.I)) := by
  rw [bombieriCriticalSpectralProduct,
    mellin_normalizedDilation_two_vertical,
    factorTwoMellinWeight_half]
  simp only [starRingEnd_apply]
  ring_nf

theorem normalized_factorTwoLocalCriticalKernel_eq_neg_cauchySeries
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, bombieriLocalCriticalKernel v *
        (starRingEnd ℂ
          (mellin (g : ℝ → ℂ)
            ((1 / 2 : ℝ) + v * Complex.I)) *
          (factorTwoMellinPhase v *
            mellin (g : ℝ → ℂ)
              ((1 / 2 : ℝ) + v * Complex.I)))) =
      -(bombieriCauchyCrossValue g
          (normalizedDilation 2 (by norm_num) g) 0 +
        ∑' k : ℕ,
          bombieriCauchyCrossValue g
            (normalizedDilation 2 (by norm_num) g) (k + 1)) := by
  have hdist := normalized_localCriticalKernel_crossProduct_eq_cauchySeries
    g (normalizedDilation 2 (by norm_num) g)
  have hzero := factorTwoAdjacentCorrelation_zero
    g ha hab hsupport hratio
  have hdist' :
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, bombieriLocalCriticalKernel v *
          (starRingEnd ℂ
            (mellin (g : ℝ → ℂ)
              ((1 / 2 : ℝ) + v * Complex.I)) *
            (factorTwoMellinPhase v *
              mellin (g : ℝ → ℂ)
                ((1 / 2 : ℝ) + v * Complex.I)))) =
        bombieriCrossDigammaCauchySeriesValue g
          (normalizedDilation 2 (by norm_num) g) := by
    calc
      _ = (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, bombieriLocalCriticalKernel v *
            bombieriCriticalSpectralProduct g
              (normalizedDilation 2 (by norm_num) g) v) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with v
        rw [factorTwoCriticalSpectralProduct_eq]
      _ = _ := hdist
  rw [bombieriCrossDigammaCauchySeriesValue,
    show bombieriCriticalCrossCorrelation g
        (normalizedDilation 2 (by norm_num) g) 0 = 0 by
      simpa only [factorTwoAdjacentCorrelation] using hzero] at hdist'
  simpa using hdist'

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoCrossDistribution
