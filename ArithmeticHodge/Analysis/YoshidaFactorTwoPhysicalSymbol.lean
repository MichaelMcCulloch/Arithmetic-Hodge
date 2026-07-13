import ArithmeticHodge.Analysis.YoshidaFactorTwoAdjacentSchwartz
import ArithmeticHodge.Analysis.YoshidaZeroCorrelationGeometricSeries

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction ComplexConjugate

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhysicalSymbol

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaBombieriCrossMoments
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoAdjacentSchwartz
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoMomentFormula
open YoshidaFactorTwoPrimeCorrelationSymbol
open YoshidaRenormalizedGeometricKernel
open YoshidaShiftedGeometricSeries
open YoshidaStructuralKernelIntegrability
open YoshidaZeroCorrelationGeometricSeries

/-!
# Exact physical formula for the factor-two cross symbol

The rank-one moment series is resummed against the one-sided adjacent
correlation.  The zero trace at the left endpoint makes the odd-kernel
singularity removable, so this is an exact structural integral rather than a
finite truncation or enclosure.
-/

def factorTwoPhysicalLength : ℝ := 2 * factorTwoLogLength

theorem factorTwoPhysicalLength_pos : 0 < factorTwoPhysicalLength := by
  unfold factorTwoPhysicalLength
  linarith [factorTwoLogLength_pos]

def factorTwoTailKernel (u : ℝ) : ℝ :=
  oddKernel u / 2 - Real.exp (-u / 2)

private theorem bombieriCauchyCrossValue_dilation_two_eq_interval
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) (k : ℕ) :
    bombieriCauchyCrossValue g
        (normalizedDilation 2 (by norm_num) g) k =
      ∫ u : ℝ in 0..factorTwoPhysicalLength,
        ((Real.exp (-oddRate k * u) : ℝ) : ℂ) *
          factorTwoAdjacentCorrelation g u := by
  have habs :
      bombieriCauchyCrossValue g
          (normalizedDilation 2 (by norm_num) g) k =
        ∫ u : ℝ,
          ((Real.exp (-oddRate k * u) : ℝ) : ℂ) *
            factorTwoAdjacentCorrelation g u := by
    rw [bombieriCauchyCrossValue]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hu : u ∈ Set.Icc 0 factorTwoPhysicalLength
    · rw [abs_of_nonneg hu.1]
      rfl
    · have hz := factorTwoAdjacentCorrelation_eq_zero_outside
        g ha hab hsupport hratio
          (by simpa only [factorTwoPhysicalLength] using hu)
      have hz' : bombieriCriticalCrossCorrelation g
          (normalizedDilation 2 (by norm_num) g) u = 0 := by
        simpa only [factorTwoAdjacentCorrelation] using hz
      rw [hz', hz, mul_zero, mul_zero]
  rw [habs, intervalIntegral.integral_of_le factorTwoPhysicalLength_pos.le,
    ← integral_Icc_eq_integral_Ioc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu ↦ by
    rw [factorTwoAdjacentCorrelation_eq_zero_outside
      g ha hab hsupport hratio
        (by simpa only [factorTwoPhysicalLength] using hu), mul_zero])).symm

private theorem cauchyCrossValue_re_eq_half_geometric
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) (k : ℕ) :
    (bombieriCauchyCrossValue g
        (normalizedDilation 2 (by norm_num) g) k).re =
      (1 / 2 : ℝ) * geometricIntegralTerm factorTwoPhysicalLength
        (fun u ↦ (factorTwoAdjacentCorrelation g u).re) k := by
  let J : ℝ → ℂ := fun u ↦
    ((Real.exp (-oddRate k * u) : ℝ) : ℂ) *
      factorTwoAdjacentCorrelation g u
  have hJ : IntervalIntegrable J volume 0 factorTwoPhysicalLength := by
    apply Continuous.intervalIntegrable
    have hexp : Continuous (fun u : ℝ ↦
        ((Real.exp (-oddRate k * u) : ℝ) : ℂ)) := by fun_prop
    exact hexp.mul
      (factorTwoAdjacentCorrelation_contDiff g 0).continuous
  rw [bombieriCauchyCrossValue_dilation_two_eq_interval
    g ha hab hsupport hratio k]
  change (∫ u : ℝ in 0..factorTwoPhysicalLength, J u).re = _
  calc
    (∫ u : ℝ in 0..factorTwoPhysicalLength, J u).re =
        ∫ u : ℝ in 0..factorTwoPhysicalLength, (J u).re := by
      simpa only [Complex.reCLM_apply] using
        (Complex.reCLM.intervalIntegral_comp_comm hJ).symm
    _ = ∫ u : ℝ in 0..factorTwoPhysicalLength,
        Real.exp (-oddRate k * u) *
          (factorTwoAdjacentCorrelation g u).re := by
      apply intervalIntegral.integral_congr
      intro u _hu
      simp only [J, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    _ = (1 / 2 : ℝ) * geometricIntegralTerm factorTwoPhysicalLength
        (fun u ↦ (factorTwoAdjacentCorrelation g u).re) k := by
      unfold geometricIntegralTerm
      ring

private theorem cauchyCrossValue_im_eq_half_geometric
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) (k : ℕ) :
    (bombieriCauchyCrossValue g
        (normalizedDilation 2 (by norm_num) g) k).im =
      (1 / 2 : ℝ) * geometricIntegralTerm factorTwoPhysicalLength
        (fun u ↦ (factorTwoAdjacentCorrelation g u).im) k := by
  let J : ℝ → ℂ := fun u ↦
    ((Real.exp (-oddRate k * u) : ℝ) : ℂ) *
      factorTwoAdjacentCorrelation g u
  have hJ : IntervalIntegrable J volume 0 factorTwoPhysicalLength := by
    apply Continuous.intervalIntegrable
    have hexp : Continuous (fun u : ℝ ↦
        ((Real.exp (-oddRate k * u) : ℝ) : ℂ)) := by fun_prop
    exact hexp.mul
      (factorTwoAdjacentCorrelation_contDiff g 0).continuous
  rw [bombieriCauchyCrossValue_dilation_two_eq_interval
    g ha hab hsupport hratio k]
  change (∫ u : ℝ in 0..factorTwoPhysicalLength, J u).im = _
  calc
    (∫ u : ℝ in 0..factorTwoPhysicalLength, J u).im =
        ∫ u : ℝ in 0..factorTwoPhysicalLength, (J u).im := by
      simpa only [Complex.imCLM_apply] using
        (Complex.imCLM.intervalIntegral_comp_comm hJ).symm
    _ = ∫ u : ℝ in 0..factorTwoPhysicalLength,
        Real.exp (-oddRate k * u) *
          (factorTwoAdjacentCorrelation g u).im := by
      apply intervalIntegral.integral_congr
      intro u _hu
      simp only [J, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
    _ = (1 / 2 : ℝ) * geometricIntegralTerm factorTwoPhysicalLength
        (fun u ↦ (factorTwoAdjacentCorrelation g u).im) k := by
      unfold geometricIntegralTerm
      ring

private theorem shiftedHalfGeometric_limit_eq_tailIntegral
    {L : ℝ} (_hL : 0 < L) (C : ℝ → ℝ)
    (hC : ContDiff ℝ 1 C) (hC0 : C 0 = 0) :
    (1 / 2 : ℝ) *
        ((∫ u : ℝ in 0..L, oddKernel u * C u) -
          geometricIntegralTerm L C 0) =
      ∫ u : ℝ in 0..L, factorTwoTailKernel u * C u := by
  obtain ⟨D, hD, hrem⟩ := exists_continuous_removable_slope C hC
  have hodd : IntervalIntegrable (fun u : ℝ ↦ oddKernel u * C u)
      volume 0 L := by
    have hbase := oddKernel_mul_u_intervalIntegrable hD L
    apply hbase.congr
    intro u _hu
    change oddKernel u * (u * D u) = oddKernel u * C u
    rw [hrem u, hC0]
    ring
  have hexp : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-u / 2) * C u) volume 0 L :=
    Continuous.intervalIntegrable (by fun_prop) 0 L
  unfold geometricIntegralTerm factorTwoTailKernel
  rw [show oddRate 0 = (1 / 2 : ℝ) by norm_num [oddRate]]
  simp_rw [show ∀ u : ℝ, -(1 / 2 : ℝ) * u = -u / 2 by
    intro u
    ring]
  rw [show (∫ u : ℝ in 0..L,
      (oddKernel u / 2 - Real.exp (-u / 2)) * C u) =
      ∫ u : ℝ in 0..L,
        (1 / 2 : ℝ) * (oddKernel u * C u) -
          Real.exp (-u / 2) * C u by
    apply intervalIntegral.integral_congr
    intro u _hu
    ring]
  rw [intervalIntegral.integral_sub (hodd.const_mul (1 / 2 : ℝ)) hexp,
    intervalIntegral.integral_const_mul]
  ring

private theorem tailKernel_mul_intervalIntegrable
    {L : ℝ} (C : ℝ → ℝ)
    (hC : ContDiff ℝ 1 C) (hC0 : C 0 = 0) :
    IntervalIntegrable (fun u : ℝ ↦ factorTwoTailKernel u * C u)
      volume 0 L := by
  obtain ⟨D, hD, hrem⟩ := exists_continuous_removable_slope C hC
  have hodd : IntervalIntegrable (fun u : ℝ ↦ oddKernel u * C u)
      volume 0 L := by
    have hbase := oddKernel_mul_u_intervalIntegrable hD L
    apply hbase.congr
    intro u _hu
    change oddKernel u * (u * D u) = oddKernel u * C u
    rw [hrem u, hC0]
    ring
  have hexp : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-u / 2) * C u) volume 0 L :=
    Continuous.intervalIntegrable (by fun_prop) 0 L
  have hbase := (hodd.const_mul (1 / 2 : ℝ)).sub hexp
  apply hbase.congr
  intro u _hu
  unfold factorTwoTailKernel
  ring

theorem factorTwoTailMomentSymbol_eq_re_im_integrals
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoTailMomentSymbol g =
      ((∫ u : ℝ in 0..factorTwoPhysicalLength,
        factorTwoTailKernel u *
          (factorTwoAdjacentCorrelation g u).re : ℝ) : ℂ) +
      ((∫ u : ℝ in 0..factorTwoPhysicalLength,
        factorTwoTailKernel u *
          (factorTwoAdjacentCorrelation g u).im : ℝ) : ℂ) * Complex.I := by
  let Cre : ℝ → ℝ := fun u ↦ (factorTwoAdjacentCorrelation g u).re
  let Cim : ℝ → ℝ := fun u ↦ (factorTwoAdjacentCorrelation g u).im
  have hHdiff := factorTwoAdjacentCorrelation_contDiff g (1 : ℕ∞)
  have hCre : ContDiff ℝ 1 Cre := by
    exact Complex.reCLM.contDiff.comp hHdiff
  have hCim : ContDiff ℝ 1 Cim := by
    exact Complex.imCLM.contDiff.comp hHdiff
  have hzero := factorTwoAdjacentCorrelation_zero
    g ha hab hsupport hratio
  have hCre0 : Cre 0 = 0 := by
    dsimp only [Cre]
    rw [hzero]
    simp
  have hCim0 : Cim 0 = 0 := by
    dsimp only [Cim]
    rw [hzero]
    simp
  let Lre : ℝ := (1 / 2 : ℝ) *
    ((∫ u : ℝ in 0..factorTwoPhysicalLength, oddKernel u * Cre u) -
      geometricIntegralTerm factorTwoPhysicalLength Cre 0)
  let Lim : ℝ := (1 / 2 : ℝ) *
    ((∫ u : ℝ in 0..factorTwoPhysicalLength, oddKernel u * Cim u) -
      geometricIntegralTerm factorTwoPhysicalLength Cim 0)
  have hgeomRe : HasSum
      (fun k : ℕ ↦ (1 / 2 : ℝ) *
        geometricIntegralTerm factorTwoPhysicalLength Cre (k + 1)) Lre := by
    simpa only [Lre] using
      zeroCorrelation_shifted_halfGeometric_hasSum
        factorTwoPhysicalLength_pos Cre hCre hCre0
  have hgeomIm : HasSum
      (fun k : ℕ ↦ (1 / 2 : ℝ) *
        geometricIntegralTerm factorTwoPhysicalLength Cim (k + 1)) Lim := by
    simpa only [Lim] using
      zeroCorrelation_shifted_halfGeometric_hasSum
        factorTwoPhysicalLength_pos Cim hCim hCim0
  have hARe : HasSum (fun k : ℕ ↦
      (bombieriCauchyCrossValue g
        (normalizedDilation 2 (by norm_num) g) (k + 1)).re) Lre := by
    apply HasSum.congr_fun hgeomRe
    intro k
    simpa only [Cre] using cauchyCrossValue_re_eq_half_geometric
      g ha hab hsupport hratio (k + 1)
  have hAIm : HasSum (fun k : ℕ ↦
      (bombieriCauchyCrossValue g
        (normalizedDilation 2 (by norm_num) g) (k + 1)).im) Lim := by
    apply HasSum.congr_fun hgeomIm
    intro k
    simpa only [Cim] using cauchyCrossValue_im_eq_half_geometric
      g ha hab hsupport hratio (k + 1)
  have hAReC : HasSum (fun k : ℕ ↦
      ((bombieriCauchyCrossValue g
        (normalizedDilation 2 (by norm_num) g) (k + 1)).re : ℂ))
      (Lre : ℂ) := (RCLike.hasSum_ofReal ℂ).2 hARe
  have hAImC : HasSum (fun k : ℕ ↦
      ((bombieriCauchyCrossValue g
        (normalizedDilation 2 (by norm_num) g) (k + 1)).im : ℂ))
      (Lim : ℂ) := (RCLike.hasSum_ofReal ℂ).2 hAIm
  have hparts := hAReC.add (hAImC.mul_right Complex.I)
  have hA : HasSum (fun k : ℕ ↦
      bombieriCauchyCrossValue g
        (normalizedDilation 2 (by norm_num) g) (k + 1))
      ((Lre : ℂ) + (Lim : ℂ) * Complex.I) := by
    apply HasSum.congr_fun hparts
    intro k
    exact (Complex.re_add_im _).symm
  have htail : HasSum (factorTwoTailMomentTerm g)
      ((Lre : ℂ) + (Lim : ℂ) * Complex.I) := by
    apply HasSum.congr_fun hA
    intro k
    simpa only [factorTwoTailMomentTerm] using
      (bombieriCauchyCrossValue_dilation_two_eq_moment
        g ha hab hsupport hratio (k + 1)).symm
  have hLre : Lre = ∫ u : ℝ in 0..factorTwoPhysicalLength,
      factorTwoTailKernel u * Cre u :=
    shiftedHalfGeometric_limit_eq_tailIntegral
      factorTwoPhysicalLength_pos Cre hCre hCre0
  have hLim : Lim = ∫ u : ℝ in 0..factorTwoPhysicalLength,
      factorTwoTailKernel u * Cim u :=
    shiftedHalfGeometric_limit_eq_tailIntegral
      factorTwoPhysicalLength_pos Cim hCim hCim0
  rw [factorTwoTailMomentSymbol, htail.tsum_eq, hLre, hLim]

theorem factorTwoTailMomentSymbol_eq_integral
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoTailMomentSymbol g =
      ∫ u : ℝ in 0..factorTwoPhysicalLength,
        ((factorTwoTailKernel u : ℝ) : ℂ) *
          factorTwoAdjacentCorrelation g u := by
  let Cre : ℝ → ℝ := fun u ↦ (factorTwoAdjacentCorrelation g u).re
  let Cim : ℝ → ℝ := fun u ↦ (factorTwoAdjacentCorrelation g u).im
  have hHdiff := factorTwoAdjacentCorrelation_contDiff g (1 : ℕ∞)
  have hCre : ContDiff ℝ 1 Cre :=
    Complex.reCLM.contDiff.comp hHdiff
  have hCim : ContDiff ℝ 1 Cim :=
    Complex.imCLM.contDiff.comp hHdiff
  have hzero := factorTwoAdjacentCorrelation_zero
    g ha hab hsupport hratio
  have hCre0 : Cre 0 = 0 := by
    dsimp only [Cre]
    rw [hzero]
    simp
  have hCim0 : Cim 0 = 0 := by
    dsimp only [Cim]
    rw [hzero]
    simp
  have hReR := tailKernel_mul_intervalIntegrable
    (L := factorTwoPhysicalLength) Cre hCre hCre0
  have hImR := tailKernel_mul_intervalIntegrable
    (L := factorTwoPhysicalLength) Cim hCim hCim0
  have hReC : IntervalIntegrable (fun u : ℝ ↦
      ((factorTwoTailKernel u * Cre u : ℝ) : ℂ))
      volume 0 factorTwoPhysicalLength := by
    constructor
    · exact hReR.1.ofReal
    · exact hReR.2.ofReal
  have hImC : IntervalIntegrable (fun u : ℝ ↦
      ((factorTwoTailKernel u * Cim u : ℝ) : ℂ))
      volume 0 factorTwoPhysicalLength := by
    constructor
    · exact hImR.1.ofReal
    · exact hImR.2.ofReal
  have hImI : IntervalIntegrable (fun u : ℝ ↦
      ((factorTwoTailKernel u * Cim u : ℝ) : ℂ) * Complex.I)
      volume 0 factorTwoPhysicalLength := by
    constructor
    · exact hImC.1.mul_const Complex.I
    · exact hImC.2.mul_const Complex.I
  rw [factorTwoTailMomentSymbol_eq_re_im_integrals
    g ha hab hsupport hratio]
  change ((∫ u : ℝ in 0..factorTwoPhysicalLength,
      factorTwoTailKernel u * Cre u : ℝ) : ℂ) +
    ((∫ u : ℝ in 0..factorTwoPhysicalLength,
      factorTwoTailKernel u * Cim u : ℝ) : ℂ) * Complex.I = _
  calc
    _ = (∫ u : ℝ in 0..factorTwoPhysicalLength,
          ((factorTwoTailKernel u * Cre u : ℝ) : ℂ)) +
        (∫ u : ℝ in 0..factorTwoPhysicalLength,
          ((factorTwoTailKernel u * Cim u : ℝ) : ℂ)) * Complex.I := by
      rw [intervalIntegral.integral_ofReal,
        intervalIntegral.integral_ofReal]
    _ = (∫ u : ℝ in 0..factorTwoPhysicalLength,
          ((factorTwoTailKernel u * Cre u : ℝ) : ℂ)) +
        ∫ u : ℝ in 0..factorTwoPhysicalLength,
          ((factorTwoTailKernel u * Cim u : ℝ) : ℂ) * Complex.I := by
      congr 1
      exact (intervalIntegral.integral_mul_const Complex.I
        (fun u : ℝ ↦
          ((factorTwoTailKernel u * Cim u : ℝ) : ℂ))).symm
    _ = ∫ u : ℝ in 0..factorTwoPhysicalLength,
        (((factorTwoTailKernel u * Cre u : ℝ) : ℂ) +
          ((factorTwoTailKernel u * Cim u : ℝ) : ℂ) * Complex.I) := by
      rw [intervalIntegral.integral_add hReC hImI]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u _hu
      calc
        (((factorTwoTailKernel u * Cre u : ℝ) : ℂ) +
            ((factorTwoTailKernel u * Cim u : ℝ) : ℂ) * Complex.I) =
            ((factorTwoTailKernel u : ℝ) : ℂ) *
              (((factorTwoAdjacentCorrelation g u).re : ℂ) +
                ((factorTwoAdjacentCorrelation g u).im : ℂ) *
                  Complex.I) := by
          dsimp only [Cre, Cim]
          push_cast
          ring
        _ = _ := by rw [Complex.re_add_im]

theorem factorTwoGrowingMomentSymbol_eq_integral
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoGrowingMomentSymbol g =
      ∫ u : ℝ in 0..factorTwoPhysicalLength,
        ((Real.exp (u / 2) : ℝ) : ℂ) *
          factorTwoAdjacentCorrelation g u := by
  have hmoment := integral_exp_mul_bombieriCriticalCrossCorrelation
    (1 / 2 : ℝ) g (normalizedDilation 2 (by norm_num) g)
  rw [bombieriCriticalMoment_normalizedDilation_two] at hmoment
  have hwhole : factorTwoGrowingMomentSymbol g =
      ∫ u : ℝ, ((Real.exp (u / 2) : ℝ) : ℂ) *
        factorTwoAdjacentCorrelation g u := by
    calc
      factorTwoGrowingMomentSymbol g =
          starRingEnd ℂ (bombieriCriticalMoment g (-(1 / 2))) *
            (((Real.exp ((1 / 2 : ℝ) * factorTwoLogLength) : ℝ) : ℂ) *
              bombieriCriticalMoment g (1 / 2)) := by
        unfold factorTwoGrowingMomentSymbol
        rw [show factorTwoLogLength / 2 =
          (1 / 2 : ℝ) * factorTwoLogLength by ring]
        ring
      _ = ∫ u : ℝ,
          ((Real.exp ((1 / 2 : ℝ) * u) : ℝ) : ℂ) *
            bombieriCriticalCrossCorrelation g
              (normalizedDilation 2 (by norm_num) g) u := hmoment.symm
      _ = ∫ u : ℝ, ((Real.exp (u / 2) : ℝ) : ℂ) *
          factorTwoAdjacentCorrelation g u := by
        apply integral_congr_ae
        filter_upwards [] with u
        unfold factorTwoAdjacentCorrelation
        congr 2
        congr 1
        ring
  rw [hwhole, intervalIntegral.integral_of_le factorTwoPhysicalLength_pos.le,
    ← integral_Icc_eq_integral_Ioc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu ↦ by
    rw [factorTwoAdjacentCorrelation_eq_zero_outside
      g ha hab hsupport hratio
        (by simpa only [factorTwoPhysicalLength] using hu), mul_zero])).symm

theorem factorTwoTailIntegrand_intervalIntegrable
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    IntervalIntegrable (fun u : ℝ ↦
      ((factorTwoTailKernel u : ℝ) : ℂ) *
        factorTwoAdjacentCorrelation g u)
      volume 0 factorTwoPhysicalLength := by
  let Cre : ℝ → ℝ := fun u ↦ (factorTwoAdjacentCorrelation g u).re
  let Cim : ℝ → ℝ := fun u ↦ (factorTwoAdjacentCorrelation g u).im
  have hHdiff := factorTwoAdjacentCorrelation_contDiff g (1 : ℕ∞)
  have hCre : ContDiff ℝ 1 Cre :=
    Complex.reCLM.contDiff.comp hHdiff
  have hCim : ContDiff ℝ 1 Cim :=
    Complex.imCLM.contDiff.comp hHdiff
  have hzero := factorTwoAdjacentCorrelation_zero
    g ha hab hsupport hratio
  have hCre0 : Cre 0 = 0 := by
    dsimp only [Cre]
    rw [hzero]
    simp
  have hCim0 : Cim 0 = 0 := by
    dsimp only [Cim]
    rw [hzero]
    simp
  have hReR := tailKernel_mul_intervalIntegrable
    (L := factorTwoPhysicalLength) Cre hCre hCre0
  have hImR := tailKernel_mul_intervalIntegrable
    (L := factorTwoPhysicalLength) Cim hCim hCim0
  have hReC : IntervalIntegrable (fun u : ℝ ↦
      ((factorTwoTailKernel u * Cre u : ℝ) : ℂ))
      volume 0 factorTwoPhysicalLength := by
    constructor
    · exact hReR.1.ofReal
    · exact hReR.2.ofReal
  have hImI : IntervalIntegrable (fun u : ℝ ↦
      ((factorTwoTailKernel u * Cim u : ℝ) : ℂ) * Complex.I)
      volume 0 factorTwoPhysicalLength := by
    constructor
    · exact hImR.1.ofReal.mul_const Complex.I
    · exact hImR.2.ofReal.mul_const Complex.I
  have hparts := hReC.add hImI
  apply hparts.congr
  intro u _hu
  calc
    (((factorTwoTailKernel u * Cre u : ℝ) : ℂ) +
        ((factorTwoTailKernel u * Cim u : ℝ) : ℂ) * Complex.I) =
        ((factorTwoTailKernel u : ℝ) : ℂ) *
          (((factorTwoAdjacentCorrelation g u).re : ℂ) +
            ((factorTwoAdjacentCorrelation g u).im : ℂ) * Complex.I) := by
      dsimp only [Cre, Cim]
      push_cast
      ring
    _ = _ := by rw [Complex.re_add_im]

theorem factorTwoLocalCrossSpectralSymbol_eq_physical
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoLocalCrossSpectralSymbol g =
      ∫ u : ℝ in 0..factorTwoPhysicalLength,
        ((factorTwoAdjacentSmoothKernel u : ℝ) : ℂ) *
          factorTwoAdjacentCorrelation g u := by
  have hgrow : IntervalIntegrable (fun u : ℝ ↦
      ((Real.exp (u / 2) : ℝ) : ℂ) *
        factorTwoAdjacentCorrelation g u)
      volume 0 factorTwoPhysicalLength := by
    apply Continuous.intervalIntegrable
    have hexp : Continuous (fun u : ℝ ↦
        ((Real.exp (u / 2) : ℝ) : ℂ)) := by fun_prop
    exact hexp.mul
      (factorTwoAdjacentCorrelation_contDiff g 0).continuous
  have htail := factorTwoTailIntegrand_intervalIntegrable
    g ha hab hsupport hratio
  rw [factorTwoLocalCrossSpectralSymbol_eq_moment
      g ha hab hsupport hratio,
    factorTwoGrowingMomentSymbol_eq_integral
      g ha hab hsupport hratio,
    factorTwoTailMomentSymbol_eq_integral
      g ha hab hsupport hratio,
    ← intervalIntegral.integral_sub hgrow htail]
  apply intervalIntegral.integral_congr
  intro u _hu
  unfold factorTwoAdjacentSmoothKernel factorTwoTailKernel
  change ((Real.exp (u / 2) : ℝ) : ℂ) *
      factorTwoAdjacentCorrelation g u -
    (((oddKernel u / 2 - Real.exp (-u / 2) : ℝ)) : ℂ) *
      factorTwoAdjacentCorrelation g u =
    (((2 * Real.cosh (u / 2) - oddKernel u / 2 : ℝ)) : ℂ) *
      factorTwoAdjacentCorrelation g u
  rw [Real.cosh_eq]
  push_cast
  ring

theorem factorTwoGlobalCrossSymbol_eq_physical
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoGlobalCrossSymbol g =
      (∫ u : ℝ in 0..factorTwoPhysicalLength,
        ((factorTwoAdjacentSmoothKernel u : ℝ) : ℂ) *
          factorTwoAdjacentCorrelation g u) -
        factorTwoPrimeCorrelationSymbol g := by
  rw [factorTwoGlobalCrossSymbol_eq_spectral_sub_prime,
    factorTwoLocalCrossSpectralSymbol_eq_physical
      g ha hab hsupport hratio,
    factorTwoPrimeCrossSymbol_eq_correlation]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhysicalSymbol
