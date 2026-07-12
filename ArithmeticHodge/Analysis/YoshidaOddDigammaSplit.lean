import ArithmeticHodge.Analysis.YoshidaOddDigammaIntegralCertificate

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaOddDigammaSplit

open DigammaTrapezoid
open YoshidaCoercivityNumerics
open YoshidaOddDigammaIntegralCertificate
open YoshidaOddDigammaLoss
open YoshidaOddTailPaired
open YoshidaSectionSixAnalytic
open YoshidaTZeroTailBounds
open YoshidaWeightedTailBounds

/-!
# Global odd digamma split

This module supplies the measure-theoretic assembly behind Yoshida's
equations (6.4)--(6.7).  The quarter-line digamma kernel is nonnegative beyond
its first positive zero and at least its value at `tOne` outside
`[-tOne,tOne]`.  Consequently the complete digamma energy is bounded below by
unit spectral mass, less exactly the high central-energy loss and the low
negative-digamma loss.

The theorem is stated first for an arbitrary cutoff and then specialized to
the actual odd `N = 10`, `tOne = 50` tail.  No pointwise substitute for the
low integral and no finite Fourier truncation is introduced.
-/

theorem clippedSection6DigammaLowerEstimate_of_split
    {N : ℕ} {tZero tOne a : ℝ} (ha : 0 < a)
    (ht : IsYoshidaTZero tZero) (htOne : 0 ≤ tOne)
    (htZeroOne : tZero ≤ tOne) (f : YoshidaClippedSmooth a)
    (hMassInt : Integrable (fun v : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear a ha v f)))
    (hDigammaInt : Integrable (fun v : ℝ ↦
      digammaQuarterVerticalRe v *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f)))
    (hParseval : clippedSpectralMass a ha f = 1)
    (hHigh : digammaQuarterVerticalRe tOne / (2 * Real.pi) *
        clippedCentralEnergy a ha f tOne ≤
      highFrequencyPenalty N tOne (digammaQuarterVerticalRe tOne))
    (hLow : -(1 / (2 * Real.pi)) *
        (∫ v : ℝ in -tZero..tZero,
          digammaQuarterVerticalRe v *
            Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) ≤
      lowIntervalPenalty N tZero) :
    ClippedSection6DigammaLowerEstimate N tZero tOne a ha f := by
  let q : ℝ → ℝ := fun v ↦
    Complex.normSq (yoshidaCriticalSampleLinear a ha v f)
  let C : ℝ := digammaQuarterVerticalRe tOne
  let SZero : Set ℝ := Set.Icc (-tZero) tZero
  let SOne : Set ℝ := Set.Icc (-tOne) tOne
  have hq0 (v : ℝ) : 0 ≤ q v := by
    dsimp only [q]
    exact Complex.normSq_nonneg _
  have hroot : digammaQuarterVerticalRe tZero = 0 := by
    simpa [digammaQuarterVerticalRe] using ht.2
  have hnonneg_of_not_mem {v : ℝ} (hv : v ∉ SZero) :
      0 ≤ digammaQuarterVerticalRe v := by
    have habs : tZero ≤ |v| := by
      have hnot : ¬ |v| ≤ tZero := by
        intro h
        apply hv
        exact (abs_le.mp h)
      exact (not_le.mp hnot).le
    have hmono := re_digamma_quarter_vertical_monotoneOn
      (show tZero ∈ Set.Ici (0 : ℝ) by exact ht.1.le)
      (show |v| ∈ Set.Ici (0 : ℝ) by exact abs_nonneg v) habs
    change digammaQuarterVerticalRe tZero ≤
      digammaQuarterVerticalRe |v| at hmono
    rw [hroot, digammaQuarterVerticalRe_abs] at hmono
    exact hmono
  have hC_le_of_not_mem {v : ℝ} (hv : v ∉ SOne) :
      C ≤ digammaQuarterVerticalRe v := by
    have habs : tOne ≤ |v| := by
      have hnot : ¬ |v| ≤ tOne := by
        intro h
        apply hv
        exact (abs_le.mp h)
      exact (not_le.mp hnot).le
    have hmono := re_digamma_quarter_vertical_monotoneOn
      (show tOne ∈ Set.Ici (0 : ℝ) by exact htOne)
      (show |v| ∈ Set.Ici (0 : ℝ) by exact abs_nonneg v) habs
    change digammaQuarterVerticalRe tOne ≤
      digammaQuarterVerticalRe |v| at hmono
    rw [digammaQuarterVerticalRe_abs] at hmono
    exact hmono
  have hpoint (v : ℝ) :
      C * q v - digammaQuarterVerticalRe v * q v ≤
        SOne.indicator (fun w ↦ C * q w) v +
          SZero.indicator
            (fun w ↦ -(digammaQuarterVerticalRe w * q w)) v := by
    by_cases hvZero : v ∈ SZero
    · have hvOne : v ∈ SOne := by
        rcases hvZero with ⟨hvLower, hvUpper⟩
        exact ⟨by linarith, by linarith⟩
      simp only [Set.indicator_of_mem hvOne, Set.indicator_of_mem hvZero]
      exact le_rfl
    · by_cases hvOne : v ∈ SOne
      · have hg0 := hnonneg_of_not_mem hvZero
        simp only [Set.indicator_of_mem hvOne,
          Set.indicator_of_notMem hvZero, add_zero]
        exact sub_le_self _ (mul_nonneg hg0 (hq0 v))
      · have hCg := hC_le_of_not_mem hvOne
        have hmul := mul_le_mul_of_nonneg_right hCg (hq0 v)
        simp only [Set.indicator_of_notMem hvOne,
          Set.indicator_of_notMem hvZero, zero_add]
        linarith
  have hCqInt : Integrable (fun v : ℝ ↦ C * q v) := by
    exact hMassInt.const_mul C
  have hgqInt : Integrable (fun v : ℝ ↦
      digammaQuarterVerticalRe v * q v) := by
    simpa only [q] using hDigammaInt
  have hleftInt : Integrable (fun v : ℝ ↦
      C * q v - digammaQuarterVerticalRe v * q v) :=
    hCqInt.sub hgqInt
  have hSZeroMeas : MeasurableSet SZero := by
    simpa only [SZero] using measurableSet_Icc
  have hSOneMeas : MeasurableSet SOne := by
    simpa only [SOne] using measurableSet_Icc
  have hLossInt : Integrable (fun v : ℝ ↦
      -(digammaQuarterVerticalRe v * q v)) := by
    simpa only [Pi.neg_apply] using hgqInt.neg
  have hrightInt : Integrable (fun v : ℝ ↦
      SOne.indicator (fun w ↦ C * q w) v +
        SZero.indicator
          (fun w ↦ -(digammaQuarterVerticalRe w * q w)) v) := by
    exact (hCqInt.indicator hSOneMeas).add
      (hLossInt.indicator hSZeroMeas)
  have hIntegral := integral_mono hleftInt hrightInt
    hpoint
  have hSet :
      C * (∫ v : ℝ, q v) -
          (∫ v : ℝ, digammaQuarterVerticalRe v * q v) ≤
        C * (∫ v : ℝ in SOne, q v) -
          (∫ v : ℝ in SZero,
            digammaQuarterVerticalRe v * q v) := by
    calc
      C * (∫ v : ℝ, q v) -
          (∫ v : ℝ, digammaQuarterVerticalRe v * q v) =
        ∫ v : ℝ, C * q v - digammaQuarterVerticalRe v * q v := by
          rw [integral_sub hCqInt hgqInt, integral_const_mul]
      _ ≤ ∫ v : ℝ,
          SOne.indicator (fun w ↦ C * q w) v +
            SZero.indicator
              (fun w ↦ -(digammaQuarterVerticalRe w * q w)) v :=
        hIntegral
      _ = C * (∫ v : ℝ in SOne, q v) -
          (∫ v : ℝ in SZero,
            digammaQuarterVerticalRe v * q v) := by
        rw [integral_add
          (hCqInt.indicator hSOneMeas)
          (hLossInt.indicator hSZeroMeas)]
        rw [integral_indicator hSOneMeas,
          integral_indicator hSZeroMeas]
        rw [integral_const_mul, integral_neg]
        ring
  have hCentral : (∫ v : ℝ in SOne, q v) =
      clippedCentralEnergy a ha f tOne := by
    unfold clippedCentralEnergy
    rw [intervalIntegral.integral_of_le (by linarith : -tOne ≤ tOne)]
    exact integral_Icc_eq_integral_Ioc
  have hLowInterval :
      (∫ v : ℝ in SZero,
        digammaQuarterVerticalRe v * q v) =
      ∫ v : ℝ in -tZero..tZero,
        digammaQuarterVerticalRe v * q v := by
    rw [intervalIntegral.integral_of_le (by linarith [ht.1] : -tZero ≤ tZero)]
    exact integral_Icc_eq_integral_Ioc
  rw [hCentral, hLowInterval] at hSet
  let p : ℝ := 1 / (2 * Real.pi)
  have hp0 : 0 ≤ p := by
    dsimp only [p]
    positivity
  have hScaled := mul_le_mul_of_nonneg_left hSet hp0
  have hMass : p * (∫ v : ℝ, q v) = 1 := by
    simpa only [p, q, clippedSpectralMass] using hParseval
  have hScaled' :
      p * (C * (∫ v : ℝ, q v)) -
          p * (∫ v : ℝ, digammaQuarterVerticalRe v * q v) ≤
        p * (C * clippedCentralEnergy a ha f tOne) -
          p * (∫ v : ℝ in -tZero..tZero,
            digammaQuarterVerticalRe v * q v) := by
    calc
      p * (C * (∫ v : ℝ, q v)) -
          p * (∫ v : ℝ, digammaQuarterVerticalRe v * q v) =
        p * (C * (∫ v : ℝ, q v) -
          (∫ v : ℝ, digammaQuarterVerticalRe v * q v)) := by ring
      _ ≤ p * (C * clippedCentralEnergy a ha f tOne -
          (∫ v : ℝ in -tZero..tZero,
            digammaQuarterVerticalRe v * q v)) := hScaled
      _ = p * (C * clippedCentralEnergy a ha f tOne) -
          p * (∫ v : ℝ in -tZero..tZero,
            digammaQuarterVerticalRe v * q v) := by ring
  have hCMass : p * (C * (∫ v : ℝ, q v)) = C := by
    calc
      p * (C * (∫ v : ℝ, q v)) =
          C * (p * (∫ v : ℝ, q v)) := by ring
      _ = C * 1 := by rw [hMass]
      _ = C := by ring
  rw [hCMass] at hScaled'
  have hBaseP :
      C - (p * C) * clippedCentralEnergy a ha f tOne -
          (-(p *
            (∫ v : ℝ in -tZero..tZero,
              digammaQuarterVerticalRe v * q v))) ≤
        p * (∫ v : ℝ, digammaQuarterVerticalRe v * q v) := by
    linarith
  have hBase :
      C - (C / (2 * Real.pi)) * clippedCentralEnergy a ha f tOne -
          (-(1 / (2 * Real.pi)) *
            (∫ v : ℝ in -tZero..tZero,
              digammaQuarterVerticalRe v * q v)) ≤
        (1 / (2 * Real.pi)) *
          (∫ v : ℝ, digammaQuarterVerticalRe v * q v) := by
    calc
      C - (C / (2 * Real.pi)) * clippedCentralEnergy a ha f tOne -
          (-(1 / (2 * Real.pi)) *
            (∫ v : ℝ in -tZero..tZero,
              digammaQuarterVerticalRe v * q v)) =
        C - (p * C) * clippedCentralEnergy a ha f tOne -
          (-(p *
            (∫ v : ℝ in -tZero..tZero,
              digammaQuarterVerticalRe v * q v))) := by
            dsimp only [p]
            ring
      _ ≤ p * (∫ v : ℝ, digammaQuarterVerticalRe v * q v) := hBaseP
      _ = (1 / (2 * Real.pi)) *
          (∫ v : ℝ, digammaQuarterVerticalRe v * q v) := by
            rfl
  unfold ClippedSection6DigammaLowerEstimate
  unfold clippedDigammaEnergy
  dsimp only [C] at hBase hHigh
  change digammaQuarterVerticalRe tOne -
      highFrequencyPenalty N tOne (digammaQuarterVerticalRe tOne) -
        lowIntervalPenalty N tZero ≤
    (1 / (2 * Real.pi)) *
      ∫ v : ℝ, digammaQuarterVerticalRe v *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f)
  dsimp only [q] at hBase hLow
  nlinarith

/-- The high-frequency half of the actual odd digamma split.  Only the low
digamma loss, spectral integrability, and unit Parseval identity remain as
inputs. -/
theorem oddTenTail_clippedSection6DigammaLowerEstimate_of_low
    {tZero : ℝ} (ht : IsYoshidaTZero tZero)
    (f : YoshidaClippedPeriodicCore yoshidaA)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)
    (henergy :
      (∫ x : ℝ in -yoshidaA..yoshidaA,
        ‖((f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) x‖ ^ 2) = 1)
    (hMassInt : Integrable (fun v : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear yoshidaA
        yoshidaA_pos v (f : YoshidaClippedSmooth yoshidaA))))
    (hDigammaInt : Integrable (fun v : ℝ ↦
      digammaQuarterVerticalRe v *
        Complex.normSq (yoshidaCriticalSampleLinear yoshidaA
          yoshidaA_pos v (f : YoshidaClippedSmooth yoshidaA))))
    (hParseval : clippedSpectralMass yoshidaA yoshidaA_pos
      (f : YoshidaClippedSmooth yoshidaA) = 1)
    (hLow : -(1 / (2 * Real.pi)) *
        (∫ v : ℝ in -tZero..tZero,
          digammaQuarterVerticalRe v *
            Complex.normSq (yoshidaCriticalSampleLinear yoshidaA
              yoshidaA_pos v (f : YoshidaClippedSmooth yoshidaA))) ≤
      lowIntervalPenalty 10 tZero) :
    ClippedSection6DigammaLowerEstimate 10 tZero 50 yoshidaA yoshidaA_pos
      (f : YoshidaClippedSmooth yoshidaA) := by
  have hC0 : 0 ≤ digammaQuarterVerticalRe 50 := by
    have h : (1609 / 500 : ℝ) ≤ digammaQuarterVerticalRe 50 := by
      simpa [digammaQuarterVerticalRe] using
        DigammaNumericBounds.digamma_quarter_vertical_re_fifty_lower
    exact (by norm_num : (0 : ℝ) ≤ 1609 / 500).trans h
  have hwindow : yoshidaA * 50 < piLowerR * (10 + 1 : ℕ) := by
    calc
      yoshidaA * 50 < (347 / 1000 : ℝ) * 50 := by
        exact mul_lt_mul_of_pos_right yoshidaA_lt_347_div_1000 (by norm_num)
      _ < piLowerR * (10 + 1 : ℕ) := by
        norm_num [piLowerR]
  have hHigh := oddTail_paired_central_energy_estimate6_6
    (N := 10) (C := digammaQuarterVerticalRe 50) (T := 50)
    (by norm_num) hC0 (by norm_num) f hf henergy hwindow
  apply clippedSection6DigammaLowerEstimate_of_split yoshidaA_pos ht
    (by norm_num) (by linarith [yoshidaTZero_le_51_div_25 ht])
    (f : YoshidaClippedSmooth yoshidaA) hMassInt hDigammaInt hParseval
  · simpa [highFrequencyPenalty, oscillatoryWindow] using hHigh
  · exact hLow

/-- The complete odd `N = 10` digamma split at any certified Yoshida zero.
The exact rational low-integral certificate and the infinite high-frequency
sampling estimate are both discharged.  Only spectral integrability and the
unit Parseval identity remain as analytic inputs. -/
theorem oddTenTail_clippedSection6DigammaLowerEstimate
    {tZero : ℝ} (ht : IsYoshidaTZero tZero)
    (f : YoshidaClippedPeriodicCore yoshidaA)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)
    (henergy :
      (∫ x : ℝ in -yoshidaA..yoshidaA,
        ‖((f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) x‖ ^ 2) = 1)
    (hMassInt : Integrable (fun v : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear yoshidaA
        yoshidaA_pos v (f : YoshidaClippedSmooth yoshidaA))))
    (hDigammaInt : Integrable (fun v : ℝ ↦
      digammaQuarterVerticalRe v *
        Complex.normSq (yoshidaCriticalSampleLinear yoshidaA
          yoshidaA_pos v (f : YoshidaClippedSmooth yoshidaA))))
    (hParseval : clippedSpectralMass yoshidaA yoshidaA_pos
      (f : YoshidaClippedSmooth yoshidaA) = 1) :
    ClippedSection6DigammaLowerEstimate 10 tZero 50 yoshidaA yoshidaA_pos
      (f : YoshidaClippedSmooth yoshidaA) := by
  apply oddTenTail_clippedSection6DigammaLowerEstimate_of_low ht f hf henergy
    hMassInt hDigammaInt hParseval
  exact oddTenTail_low_digamma_loss_le_lowIntervalPenalty_of_isYoshidaTZero
    ht f hf henergy

end ArithmeticHodge.Analysis.YoshidaOddDigammaSplit
