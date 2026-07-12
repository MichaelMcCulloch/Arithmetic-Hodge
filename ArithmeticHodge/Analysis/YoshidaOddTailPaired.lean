import ArithmeticHodge.Analysis.YoshidaClippedPeriodicCore
import ArithmeticHodge.Analysis.YoshidaInfiniteCriticalSample
import Mathlib.Analysis.MeanInequalities

set_option autoImplicit false

open AddCircle Complex MeasureTheory Real Set
open scoped BigOperators ENNReal InnerProductSpace ComplexConjugate

namespace ArithmeticHodge.Analysis.YoshidaOddTailPaired

noncomputable section

open YoshidaClippedCircleBridge
open YoshidaInfiniteCriticalSample
open YoshidaSectionSixAnalytic
open YoshidaWeightedTailBounds

/-!
# Exact odd-tail sampling and central coercive penalty

This module proves the infinite-mode odd half of Yoshida's equations
(6.5)--(6.6) on the faithful clipped periodic core.  It pairs the actual
positive and negative Fourier coefficients, carries Parseval's exact interval
normalization through an infinite Cauchy--Schwarz estimate, compares the full
paired-denominator sum with the committed weighted-tail functional, and
specializes the resulting central-energy scalar bound to the expression used
by the production low-interval penalty at N = 10.

The nonresonance window and unit-energy hypothesis remain explicit.  Nothing
here asserts boundedness of the local critical form on ordinary L2, exchanges
that form with an infinite Fourier sum, or bounds the negative digamma-weighted
integral.  In particular, `2773 / 1000` is not used here as a pointwise
digamma bound; its source role requires a separate half-integral certificate.
-/

theorem intervalExpQuotient_critical_eq_section6
    {a : ℝ} (ha : 0 < a) (v : ℝ) (n : ℤ)
    (hden : a * v - Real.pi * (n : ℝ) ≠ 0) :
    yoshidaIntervalExpQuotient a
        (yoshidaModeLaplaceExponent a n (v * Complex.I)) =
      (((2 * a * (-1 : ℝ) ^ n * Real.sin (a * v) /
        (a * v - Real.pi * (n : ℝ)) : ℝ) : ℂ)) := by
  have hmode := yoshidaCenteredLaplace_clippedExponential
    ha (v * Complex.I) n
  change yoshidaCriticalSampleLinear a ha v
      (yoshidaClippedExponential a n) =
    ((Real.sqrt (2 * a))⁻¹ : ℂ) *
      yoshidaIntervalExpQuotient a
        (yoshidaModeLaplaceExponent a n (v * Complex.I)) at hmode
  have hsec := criticalSample_clippedExponential_eq_section6
    ha v n hden
  rw [hsec] at hmode
  have hsqrt : Real.sqrt (2 * a) ≠ 0 := by positivity
  have hsqrtSq : Real.sqrt (2 * a) ^ 2 = 2 * a :=
    Real.sq_sqrt (by positivity)
  have hsqrtC : (((Real.sqrt (2 * a) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsqrt
  have hscaled := congrArg
    (fun z : ℂ ↦ ((Real.sqrt (2 * a) : ℝ) : ℂ) * z) hmode
  simp only [← mul_assoc, mul_inv_cancel₀ hsqrtC, one_mul] at hscaled
  calc
    yoshidaIntervalExpQuotient a
        (yoshidaModeLaplaceExponent a n (v * Complex.I)) =
      ((Real.sqrt (2 * a) : ℝ) : ℂ) *
        (((Real.sqrt (2 * a) * (-1 : ℝ) ^ n * Real.sin (a * v) /
          (a * v - Real.pi * (n : ℝ)) : ℝ) : ℂ)) := hscaled.symm
    _ = (((2 * a * (-1 : ℝ) ^ n * Real.sin (a * v) /
        (a * v - Real.pi * (n : ℝ)) : ℝ) : ℂ)) := by
      norm_cast
      field_simp [hden]
      rw [hsqrtSq]

/-- The exact removable critical multiplier, paired across positive and
negative frequencies of an odd Fourier tail. -/
theorem hasSum_criticalSample_oddTail_paired_exact
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule ha N)
    (v : ℝ) :
    HasSum
      (fun k : ℕ ↦
        let n : ℕ := N + 1 + k
        centeredFourierCoeff ha
            ((f : YoshidaClippedSmooth a) : ℝ → ℂ) (n : ℤ) *
          (yoshidaIntervalExpQuotient a
              (yoshidaModeLaplaceExponent a (n : ℤ) (v * Complex.I)) -
            yoshidaIntervalExpQuotient a
              (yoshidaModeLaplaceExponent a (-(n : ℤ)) (v * Complex.I))))
      (yoshidaCriticalSampleLinear a ha v
        (f : YoshidaClippedSmooth a)) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  let F := yoshidaClippedCircleL2 ha (f : YoshidaClippedSmooth a)
  let c : ℤ → ℂ := fun n ↦ centeredFourierCoeff ha
    ((f : YoshidaClippedSmooth a) : ℝ → ℂ) n
  let q : ℤ → ℂ := fun n ↦ yoshidaIntervalExpQuotient a
    (yoshidaModeLaplaceExponent a n (v * Complex.I))
  have htail : F ∈ oddFourierTailSubmodule (T := 2 * a) N :=
    (mem_yoshidaPeriodicCoreOddTailSubmodule_iff ha N f).mp hf
  have hodd : F ∈ oddL2Submodule (T := 2 * a) := htail.1
  have hzero : F ∈ fourierTailSubmodule (T := 2 * a) N := htail.2
  have hcneg (n : ℤ) : c (-n) = -c n := by
    dsimp only [c, F]
    rw [← fourierCoeff_yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) (-n)]
    rw [← fourierCoeff_yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) n]
    exact fourierCoeff_odd_of_mem hodd n
  have hc_of_nat_le (n : ℕ) (hn : n ≤ N) : c (n : ℤ) = 0 := by
    dsimp only [c, F]
    rw [← fourierCoeff_yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) (n : ℤ)]
    exact (mem_fourierTailSubmodule_iff N F).mp hzero (n : ℤ) (by
      simp only [Finset.mem_Icc]
      constructor <;> omega)
  have hc0 : c 0 = 0 := by
    simpa using hc_of_nat_le 0 (Nat.zero_le N)
  have hall : HasSum (fun n : ℤ ↦ c n * q n)
      (yoshidaCriticalSampleLinear a ha v
        (f : YoshidaClippedSmooth a)) := by
    simpa only [c, q] using hasSum_criticalSample_intervalExpQuotient
      ha v (f : YoshidaClippedSmooth a)
  let p : ℕ → ℂ := fun n ↦ c (n : ℤ) *
    (q (n : ℤ) - q (-(n : ℤ)))
  have hpaired : HasSum p
      (yoshidaCriticalSampleLinear a ha v
        (f : YoshidaClippedSmooth a)) := by
    have hraw := hall.nat_add_neg
    rw [hc0] at hraw
    simp only [zero_mul, add_zero] at hraw
    refine hraw.congr_fun ?_
    intro n
    dsimp only [p]
    rw [hcneg]
    ring
  have hhead : ∑ n ∈ Finset.range (N + 1),
      p n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnlt : n < N + 1 := Finset.mem_range.mp hn
    have hnle : n ≤ N := by omega
    dsimp only [p]
    rw [hc_of_nat_le n hnle, zero_mul]
  have hshift : HasSum (fun k : ℕ ↦ p (k + (N + 1)))
      (yoshidaCriticalSampleLinear a ha v
        (f : YoshidaClippedSmooth a)) := by
    apply (hasSum_nat_add_iff (f := p) (N + 1)).mpr
    rw [hhead, add_zero]
    exact hpaired
  simpa only [p, c, q, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hshift

def oddPairedDenominator (x : ℝ) (n : ℕ) : ℝ :=
  1 / (x - (n : ℝ)) - 1 / (x + (n : ℝ))

theorem summable_sq_oddPairedDenominator (x : ℝ) (N : ℕ) :
    Summable (fun k : ℕ ↦
      oddPairedDenominator x (N + 1 + k) ^ 2) := by
  have hminusBase :=
    (Real.summable_one_div_nat_add_rpow ((N + 1 : ℕ) - x) 2).mpr (by norm_num)
  have hplusBase :=
    (Real.summable_one_div_nat_add_rpow ((N + 1 : ℕ) + x) 2).mpr (by norm_num)
  have hminus : Summable (fun k : ℕ ↦
      1 / (x - ((N + 1 + k : ℕ) : ℝ)) ^ 2) := by
    apply hminusBase.congr
    intro k
    rw [Real.rpow_two, sq_abs]
    push_cast
    ring_nf
  have hplus : Summable (fun k : ℕ ↦
      1 / (x + ((N + 1 + k : ℕ) : ℝ)) ^ 2) := by
    apply hplusBase.congr
    intro k
    rw [Real.rpow_two, sq_abs]
    push_cast
    ring_nf
  have hmajor : Summable (fun k : ℕ ↦
      2 * (1 / (x - ((N + 1 + k : ℕ) : ℝ)) ^ 2 +
        1 / (x + ((N + 1 + k : ℕ) : ℝ)) ^ 2)) :=
    (hminus.add hplus).mul_left 2
  apply hmajor.of_nonneg_of_le
  · intro k
    positivity
  · intro k
    unfold oddPairedDenominator
    rw [← one_div_pow, ← one_div_pow]
    nlinarith [sq_nonneg
      (1 / (x - ((N + 1 + k : ℕ) : ℝ)) +
        1 / (x + ((N + 1 + k : ℕ) : ℝ)))]

theorem normSq_hasSum_mul_le
    {u w : ℕ → ℂ} {z : ℂ} {U W : ℝ}
    (hz : HasSum (fun k ↦ u k * w k) z)
    (hu : HasSum (fun k ↦ ‖u k‖ ^ 2) U)
    (hw : HasSum (fun k ↦ ‖w k‖ ^ 2) W) :
    Complex.normSq z ≤ U * W := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  have huR : HasSum (fun k ↦ ‖u k‖ ^ (2 : ℝ)) U := by
    simpa only [Real.rpow_two] using hu
  have hwR : HasSum (fun k ↦ ‖w k‖ ^ (2 : ℝ)) W := by
    simpa only [Real.rpow_two] using hw
  have hu0 : 0 ≤ U := hu.tsum_eq ▸ tsum_nonneg fun k ↦ sq_nonneg ‖u k‖
  have hw0 : 0 ≤ W := hw.tsum_eq ▸ tsum_nonneg fun k ↦ sq_nonneg ‖w k‖
  have hholder := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    hpq (fun k ↦ norm_nonneg (u k)) (fun k ↦ norm_nonneg (w k))
      huR.summable hwR.summable
  have hnormSummable : Summable (fun k ↦ ‖u k * w k‖) := by
    simpa only [norm_mul] using hholder.1
  have hnorm : ‖z‖ ≤ U ^ (1 / 2 : ℝ) * W ^ (1 / 2 : ℝ) := by
    calc
      ‖z‖ = ‖∑' k, u k * w k‖ := by rw [hz.tsum_eq]
      _ ≤ ∑' k, ‖u k * w k‖ := norm_tsum_le_tsum_norm hnormSummable
      _ = ∑' k, ‖u k‖ * ‖w k‖ := by simp only [norm_mul]
      _ ≤ (∑' k, ‖u k‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∑' k, ‖w k‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hholder.2
      _ = U ^ (1 / 2 : ℝ) * W ^ (1 / 2 : ℝ) := by
        rw [huR.tsum_eq, hwR.tsum_eq]
  rw [Complex.normSq_eq_norm_sq]
  have hUrpow : U ^ (1 / 2 : ℝ) = Real.sqrt U := by
    rw [Real.sqrt_eq_rpow]
  have hWrpow : W ^ (1 / 2 : ℝ) = Real.sqrt W := by
    rw [Real.sqrt_eq_rpow]
  rw [hUrpow, hWrpow] at hnorm
  nlinarith [Real.sq_sqrt hu0, Real.sq_sqrt hw0,
    mul_nonneg (Real.sqrt_nonneg U) (Real.sqrt_nonneg W), norm_nonneg z]

private theorem negOne_zpow_neg_nat (n : ℕ) :
    (-1 : ℝ) ^ (-(n : ℤ)) = (-1 : ℝ) ^ (n : ℤ) := by
  rw [← Int.cast_negOnePow, ← Int.cast_negOnePow]
  simp

private theorem negOne_zpow_sq (z : ℤ) :
    ((-1 : ℝ) ^ z) ^ 2 = 1 := by
  rw [← zpow_natCast]
  rw [← zpow_mul]
  change (-1 : ℝ) ^ (z * (2 : ℤ)) = 1
  rw [show z * (2 : ℤ) = 2 * z by ring]
  rw [zpow_mul]
  norm_num

theorem intervalExpQuotient_critical_pair_eq
    {a : ℝ} (ha : 0 < a) (v : ℝ) (n : ℕ)
    (hminus : a * v - Real.pi * (n : ℝ) ≠ 0)
    (hplus : a * v + Real.pi * (n : ℝ) ≠ 0) :
    yoshidaIntervalExpQuotient a
          (yoshidaModeLaplaceExponent a (n : ℤ) (v * Complex.I)) -
        yoshidaIntervalExpQuotient a
          (yoshidaModeLaplaceExponent a (-(n : ℤ)) (v * Complex.I)) =
      (((2 * a / Real.pi * (-1 : ℝ) ^ (n : ℤ) * Real.sin (a * v) *
        oddPairedDenominator (a * v / Real.pi) n : ℝ) : ℂ)) := by
  rw [intervalExpQuotient_critical_eq_section6 ha v (n : ℤ) hminus]
  rw [intervalExpQuotient_critical_eq_section6 ha v (-(n : ℤ))]
  · norm_num only [Int.cast_neg, Int.cast_natCast]
    rw [negOne_zpow_neg_nat]
    norm_cast
    norm_num only [Int.cast_neg, Int.cast_natCast]
    unfold oddPairedDenominator
    field_simp [hminus, hplus, Real.pi_ne_zero]
    ring_nf
  · norm_num only [Int.cast_neg, Int.cast_natCast]
    simpa [sub_eq_add_neg] using hplus

theorem hasSum_sq_centeredFourierCoeff_oddTail_positive
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule ha N) :
    HasSum
      (fun k : ℕ ↦
        ‖centeredFourierCoeff ha
          ((f : YoshidaClippedSmooth a) : ℝ → ℂ)
          ((N + 1 + k : ℕ) : ℤ)‖ ^ 2)
      ((1 / (4 * a)) *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  let F := yoshidaClippedCircleL2 ha (f : YoshidaClippedSmooth a)
  let c : ℤ → ℂ := fun n ↦ centeredFourierCoeff ha
    ((f : YoshidaClippedSmooth a) : ℝ → ℂ) n
  have htail : F ∈ oddFourierTailSubmodule (T := 2 * a) N :=
    (mem_yoshidaPeriodicCoreOddTailSubmodule_iff ha N f).mp hf
  have hodd : F ∈ oddL2Submodule (T := 2 * a) := htail.1
  have hzero : F ∈ fourierTailSubmodule (T := 2 * a) N := htail.2
  have hcneg (n : ℤ) : c (-n) = -c n := by
    dsimp only [c, F]
    rw [← fourierCoeff_yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) (-n)]
    rw [← fourierCoeff_yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) n]
    exact fourierCoeff_odd_of_mem hodd n
  have hc_of_nat_le (n : ℕ) (hn : n ≤ N) : c (n : ℤ) = 0 := by
    dsimp only [c, F]
    rw [← fourierCoeff_yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) (n : ℤ)]
    exact (mem_fourierTailSubmodule_iff N F).mp hzero (n : ℤ) (by
      simp only [Finset.mem_Icc]
      constructor <;> omega)
  have hc0 : c 0 = 0 := by
    simpa using hc_of_nat_le 0 (Nat.zero_le N)
  have hall : HasSum (fun n : ℤ ↦ ‖c n‖ ^ 2)
      ((2 * a)⁻¹ *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) := by
    simpa only [c, centeredFourierCoeff,
      show a - -a = 2 * a by ring, smul_eq_mul] using
        (hasSum_sq_fourierCoeffOn (neg_lt_self ha)
          (yoshidaClippedSmooth_memLp_two (f : YoshidaClippedSmooth a)))
  let p : ℕ → ℝ := fun n ↦ 2 * ‖c (n : ℤ)‖ ^ 2
  have hpaired : HasSum p
      ((2 * a)⁻¹ *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) := by
    have hraw := hall.nat_add_neg
    have hc0norm : ‖c 0‖ ^ 2 = 0 := by rw [hc0, norm_zero]; norm_num
    rw [hc0norm, add_zero] at hraw
    refine hraw.congr_fun ?_
    intro n
    dsimp only [p]
    rw [hcneg, norm_neg]
    ring
  have hhead : ∑ n ∈ Finset.range (N + 1), p n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnlt : n < N + 1 := Finset.mem_range.mp hn
    have hnle : n ≤ N := by omega
    dsimp only [p]
    rw [hc_of_nat_le n hnle, norm_zero]
    norm_num
  have hshift : HasSum (fun k : ℕ ↦ p (k + (N + 1)))
      ((2 * a)⁻¹ *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) := by
    apply (hasSum_nat_add_iff (f := p) (N + 1)).mpr
    rw [hhead, add_zero]
    exact hpaired
  have hhalf := hshift.mul_left (1 / 2 : ℝ)
  have hhalf' : HasSum
      (fun k : ℕ ↦ ‖c ((N + 1 + k : ℕ) : ℤ)‖ ^ 2)
      ((1 / 2 : ℝ) * ((2 * a)⁻¹ *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2)) := by
    refine hhalf.congr_fun ?_
    intro k
    dsimp only [p]
    rw [show (k + (N + 1) : ℕ) = N + 1 + k by omega]
    ring
  have hvalue : (1 / 2 : ℝ) * ((2 * a)⁻¹ *
      ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) =
      (1 / (4 * a)) *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2 := by
    field_simp [ha.ne']
    ring
  rw [hvalue] at hhalf'
  simpa only [c] using hhalf'

theorem oddTail_denominators_ne
    {a : ℝ} (ha : 0 < a) (N k : ℕ) {v : ℝ}
    (hwindow : a * |v| < Real.pi * (N + 1 : ℕ)) :
    let n : ℕ := N + 1 + k
    a * v - Real.pi * (n : ℝ) ≠ 0 ∧
      a * v + Real.pi * (n : ℝ) ≠ 0 := by
  dsimp only
  let n : ℕ := N + 1 + k
  have hn : 0 < n := by dsimp [n]; omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpiN : Real.pi * (N + 1 : ℕ) ≤ Real.pi * (n : ℝ) := by
    gcongr
    dsimp [n]
    exact_mod_cast (show N + 1 ≤ N + 1 + k by omega)
  have habs : |a * v| < Real.pi * (n : ℝ) := by
    rw [abs_mul, abs_of_pos ha]
    exact hwindow.trans_le hpiN
  have hpin : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
  constructor
  · intro h
    have hav : a * v = Real.pi * (n : ℝ) := sub_eq_zero.mp h
    rw [hav, abs_of_pos hpin] at habs
    exact lt_irrefl _ habs
  · intro h
    have hav : a * v = -(Real.pi * (n : ℝ)) := eq_neg_of_add_eq_zero_left h
    rw [hav, abs_neg, abs_of_pos hpin] at habs
    exact lt_irrefl _ habs

/-- Infinite paired Cauchy--Schwarz estimate for an actual periodic odd tail.
The circle `L²` norm enters only through Parseval for its coefficients. -/
theorem oddTail_paired_pointwise_estimate
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule ha N)
    {v : ℝ} (hwindow : a * |v| < Real.pi * (N + 1 : ℕ)) :
    Complex.normSq (yoshidaCriticalSampleLinear a ha v
        (f : YoshidaClippedSmooth a)) ≤
      a / Real.pi ^ 2 * Real.sin (a * v) ^ 2 *
        (∑' k : ℕ,
          oddPairedDenominator (a * v / Real.pi) (N + 1 + k) ^ 2) *
        (∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) := by
  let c : ℕ → ℂ := fun k ↦ centeredFourierCoeff ha
    ((f : YoshidaClippedSmooth a) : ℝ → ℂ)
      ((N + 1 + k : ℕ) : ℤ)
  let K : ℝ := 2 * a / Real.pi * Real.sin (a * v)
  let d : ℕ → ℝ := fun k ↦
    oddPairedDenominator (a * v / Real.pi) (N + 1 + k)
  let w : ℕ → ℂ := fun k ↦
    ((K * (-1 : ℝ) ^ ((N + 1 + k : ℕ) : ℤ) * d k : ℝ) : ℂ)
  have hz : HasSum (fun k ↦ c k * w k)
      (yoshidaCriticalSampleLinear a ha v
        (f : YoshidaClippedSmooth a)) := by
    have h := hasSum_criticalSample_oddTail_paired_exact ha N f hf v
    refine h.congr_fun ?_
    intro k
    obtain ⟨hminus, hplus⟩ := oddTail_denominators_ne ha N k hwindow
    dsimp only [c, w, K, d]
    rw [intervalExpQuotient_critical_pair_eq ha v (N + 1 + k)
      hminus hplus]
    ring_nf
  have hc : HasSum (fun k ↦ ‖c k‖ ^ 2)
      ((1 / (4 * a)) *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) := by
    simpa only [c] using
      hasSum_sq_centeredFourierCoeff_oddTail_positive ha N f hf
  have hdsum : Summable (fun k ↦ d k ^ 2) := by
    simpa only [d] using
      summable_sq_oddPairedDenominator (a * v / Real.pi) N
  have hd : HasSum (fun k ↦ d k ^ 2) (∑' k, d k ^ 2) := hdsum.hasSum
  have hw : HasSum (fun k ↦ ‖w k‖ ^ 2)
      (K ^ 2 * ∑' k, d k ^ 2) := by
    have hscaled := hd.mul_left (K ^ 2)
    refine hscaled.congr_fun ?_
    intro k
    dsimp only [w]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    calc
      (K * (-1 : ℝ) ^ ((N + 1 + k : ℕ) : ℤ) * d k) ^ 2 =
          K ^ 2 * (((-1 : ℝ) ^ ((N + 1 + k : ℕ) : ℤ)) ^ 2) *
            d k ^ 2 := by ring
      _ = K ^ 2 * d k ^ 2 := by rw [negOne_zpow_sq]; ring
  have hcs := normSq_hasSum_mul_le hz hc hw
  calc
    Complex.normSq (yoshidaCriticalSampleLinear a ha v
        (f : YoshidaClippedSmooth a)) ≤
      ((1 / (4 * a)) *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) *
        (K ^ 2 * ∑' k, d k ^ 2) := hcs
    _ = a / Real.pi ^ 2 * Real.sin (a * v) ^ 2 *
        (∑' k : ℕ,
          oddPairedDenominator (a * v / Real.pi) (N + 1 + k) ^ 2) *
        (∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) := by
      dsimp only [K, d]
      field_simp [ha.ne', Real.pi_ne_zero]
      ring

theorem abs_oddPairedDenominator_le_weightedRoot
    {y c : ℝ} {n : ℕ} (hn : 0 < n)
    (hy : |y| ≤ c) (hcden : c < Real.pi * (n : ℝ)) :
    |oddPairedDenominator (y / Real.pi) n| ≤
      1 / (n : ℝ) *
        (1 + Real.pi * n / (Real.pi * n - c)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let P : ℝ := Real.pi * (n : ℝ)
  have hP : 0 < P := by dsimp [P]; positivity
  have hylo : -c ≤ y := (abs_le.mp hy).1
  have hyhi : y ≤ c := (abs_le.mp hy).2
  have hdenC : 0 < P - c := sub_pos.mpr hcden
  have hminus : 0 < P - y := by linarith
  have hplus : 0 < P + y := by linarith
  have hxminus : y / Real.pi - (n : ℝ) < 0 := by
    rw [sub_neg]
    apply (div_lt_iff₀ Real.pi_pos).2
    dsimp only [P] at hminus
    nlinarith [Real.pi_pos]
  have hxplus : 0 < y / Real.pi + (n : ℝ) := by
    have hlt : -(n : ℝ) < y / Real.pi := by
      apply (lt_div_iff₀ Real.pi_pos).2
      dsimp only [P] at hplus
      nlinarith [Real.pi_pos]
    linarith
  have hpairNeg : oddPairedDenominator (y / Real.pi) n < 0 := by
    unfold oddPairedDenominator
    have hinvMinus : 1 / (y / Real.pi - (n : ℝ)) < 0 := one_div_neg.mpr hxminus
    have hinvPlus : 0 < 1 / (y / Real.pi + (n : ℝ)) := one_div_pos.mpr hxplus
    linarith
  rw [abs_of_neg hpairNeg]
  have hym : y - Real.pi * (n : ℝ) ≠ 0 := by
    dsimp only [P] at hminus
    linarith
  have hyp : y + Real.pi * (n : ℝ) ≠ 0 := by
    dsimp only [P] at hplus
    linarith
  have hmy : Real.pi * (n : ℝ) - y ≠ 0 := by
    dsimp only [P] at hminus
    linarith
  have hpy : Real.pi * (n : ℝ) + y ≠ 0 := by
    dsimp only [P] at hplus
    linarith
  have heq : -oddPairedDenominator (y / Real.pi) n =
      Real.pi / (P - y) + Real.pi / (P + y) := by
    unfold oddPairedDenominator
    dsimp only [P]
    field_simp [Real.pi_ne_zero, hym, hyp, hmy, hpy]
    all_goals ring
  rw [heq]
  have hroot : 1 / (n : ℝ) *
      (1 + Real.pi * n / (Real.pi * n - c)) =
      1 / (n : ℝ) + Real.pi / (P - c) := by
    dsimp only [P]
    field_simp [hnR.ne', hdenC.ne']
  rw [hroot]
  by_cases hy0 : 0 ≤ y
  · have hfirst : Real.pi / (P - y) ≤ Real.pi / (P - c) :=
      div_le_div_of_nonneg_left Real.pi_pos.le hdenC (by linarith)
    have hsecond : Real.pi / (P + y) ≤ 1 / (n : ℝ) := by
      calc
        Real.pi / (P + y) ≤ Real.pi / P :=
          div_le_div_of_nonneg_left Real.pi_pos.le hP (by linarith)
        _ = 1 / (n : ℝ) := by
          dsimp only [P]
          field_simp [Real.pi_ne_zero, hnR.ne']
    linarith
  · have hyneg : y < 0 := lt_of_not_ge hy0
    have hfirst : Real.pi / (P - y) ≤ 1 / (n : ℝ) := by
      calc
        Real.pi / (P - y) ≤ Real.pi / P :=
          div_le_div_of_nonneg_left Real.pi_pos.le hP (by linarith)
        _ = 1 / (n : ℝ) := by
          dsimp only [P]
          field_simp [Real.pi_ne_zero, hnR.ne']
    have hsecond : Real.pi / (P + y) ≤ Real.pi / (P - c) :=
      div_le_div_of_nonneg_left Real.pi_pos.le hdenC (by linarith)
    linarith

theorem oddPairedDenominator_sq_le_weightedTermR
    {y c : ℝ} {n : ℕ} (hn : 0 < n)
    (hy : |y| ≤ c) (hcden : c < Real.pi * (n : ℝ)) :
    oddPairedDenominator (y / Real.pi) n ^ 2 ≤
      YoshidaWeightedTailBounds.weightedTermR Real.pi c n := by
  have hroot := abs_oddPairedDenominator_le_weightedRoot hn hy hcden
  have hroot0 : 0 ≤ 1 / (n : ℝ) *
      (1 + Real.pi * n / (Real.pi * n - c)) := by
    have hden : 0 < Real.pi * (n : ℝ) - c := sub_pos.mpr hcden
    positivity
  have hsq := (sq_le_sq₀ (abs_nonneg _) hroot0).mpr hroot
  rw [sq_abs] at hsq
  unfold YoshidaWeightedTailBounds.weightedTermR
  calc
    oddPairedDenominator (y / Real.pi) n ^ 2 ≤
        (1 / (n : ℝ) *
          (1 + Real.pi * n / (Real.pi * n - c))) ^ 2 := hsq
    _ = 1 / (n : ℝ) ^ 2 *
        (1 + Real.pi * n / (Real.pi * n - c)) ^ 2 := by ring

/-- The production weighted-tail series is summable throughout the explicit
`piLowerR` nonresonance window.  This is the infinite-tail obligation needed
before comparing the exact paired denominator `tsum` with `weightedTail`. -/
theorem summable_weightedTail_of_piLower_window
    {N : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 ≤ T)
    (hwindow : yoshidaA * T < piLowerR * (N + 1 : ℕ)) :
    Summable (fun k : ℕ ↦
      weightedTermR Real.pi (yoshidaA * T) (N + k + 1)) := by
  have ha : 0 < yoshidaA := by
    unfold yoshidaA
    positivity
  have hc : 0 ≤ yoshidaA * T := mul_nonneg ha.le hT
  have hbase : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hq : 0 < piLowerR - yoshidaA * T / (N + 1 : ℕ) := by
    rw [sub_pos, div_lt_iff₀ hbase]
    exact hwindow
  have hupper : Summable (fun k : ℕ ↦
      weightedTermUpperR (yoshidaA * T) (N + k + 1)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      summable_weightedUpper_tail hc hN hq
  apply hupper.of_nonneg_of_le
  · intro k
    unfold weightedTermR
    positivity
  · intro k
    apply weightedTermR_le_of_bounds
    · omega
    · exact hc
    · exact hc
    · exact le_rfl
    · exact piLowerR_le_pi
    · have hcast : ((N + 1 : ℕ) : ℝ) ≤ (N + k + 1 : ℕ) := by
        exact_mod_cast (show N + 1 ≤ N + k + 1 by omega)
      exact hwindow.trans_le
        (mul_le_mul_of_nonneg_left hcast (by norm_num [piLowerR]))

/-- Exact infinite paired denominator mass is controlled by the committed
Yoshida `weightedTail`; no finite truncation occurs in this comparison. -/
theorem tsum_sq_oddPairedDenominator_le_weightedTail
    {N : ℕ} (hN : 0 < N) {T v : ℝ} (hT : 0 ≤ T)
    (hv : |v| ≤ T)
    (hwindow : yoshidaA * T < piLowerR * (N + 1 : ℕ)) :
    (∑' k : ℕ,
      oddPairedDenominator (yoshidaA * v / Real.pi) (N + 1 + k) ^ 2) ≤
      weightedTail N T := by
  have ha : 0 < yoshidaA := by
    unfold yoshidaA
    positivity
  have hc : 0 ≤ yoshidaA * T := mul_nonneg ha.le hT
  have hy : |yoshidaA * v| ≤ yoshidaA * T := by
    rw [abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left hv ha.le
  have hpoint (k : ℕ) :
      oddPairedDenominator (yoshidaA * v / Real.pi) (N + 1 + k) ^ 2 ≤
        weightedTermR Real.pi (yoshidaA * T) (N + k + 1) := by
    have hn : 0 < N + k + 1 := by omega
    have hcast : ((N + 1 : ℕ) : ℝ) ≤ (N + k + 1 : ℕ) := by
      exact_mod_cast (show N + 1 ≤ N + k + 1 by omega)
    have hpiBase : piLowerR * (N + 1 : ℕ) ≤
        Real.pi * (N + 1 : ℕ) :=
      mul_le_mul_of_nonneg_right piLowerR_le_pi (by positivity)
    have hpiTail : Real.pi * (N + 1 : ℕ) ≤
        Real.pi * (N + k + 1 : ℕ) :=
      mul_le_mul_of_nonneg_left hcast Real.pi_pos.le
    have hden : yoshidaA * T < Real.pi * (N + k + 1 : ℕ) :=
      hwindow.trans_le (hpiBase.trans hpiTail)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      oddPairedDenominator_sq_le_weightedTermR hn hy hden
  have hleft :=
    summable_sq_oddPairedDenominator (yoshidaA * v / Real.pi) N
  have hright := summable_weightedTail_of_piLower_window hN hT hwindow
  unfold weightedTail
  exact hleft.tsum_le_tsum hpoint hright

/-- The exact paired sample bound with the coefficient energy normalized to
one and the infinite denominator mass replaced by production `weightedTail`.
The `piLowerR` window is retained explicitly; it is stronger than the
nonresonance window used by the exact pairing formula. -/
theorem oddTail_paired_pointwise_estimate_weightedTail
    {N : ℕ} (hN : 0 < N)
    (f : YoshidaClippedPeriodicCore yoshidaA)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule
      YoshidaCoercivityNumerics.yoshidaA_pos N)
    (henergy :
      (∫ x : ℝ in -yoshidaA..yoshidaA,
        ‖((f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) x‖ ^ 2) = 1)
    {T v : ℝ} (hT : 0 ≤ T) (hv : |v| ≤ T)
    (hwindow : yoshidaA * T < piLowerR * (N + 1 : ℕ)) :
    Complex.normSq (yoshidaCriticalSampleLinear yoshidaA
        YoshidaCoercivityNumerics.yoshidaA_pos v
        (f : YoshidaClippedSmooth yoshidaA)) ≤
      yoshidaA / Real.pi ^ 2 * Real.sin (yoshidaA * v) ^ 2 *
        weightedTail N T := by
  have hpiBase : piLowerR * (N + 1 : ℕ) ≤
      Real.pi * (N + 1 : ℕ) :=
    mul_le_mul_of_nonneg_right piLowerR_le_pi (by positivity)
  have hnonres : yoshidaA * |v| < Real.pi * (N + 1 : ℕ) :=
    (mul_le_mul_of_nonneg_left hv
      YoshidaCoercivityNumerics.yoshidaA_pos.le).trans_lt
      (hwindow.trans_le hpiBase)
  have hraw := oddTail_paired_pointwise_estimate
    YoshidaCoercivityNumerics.yoshidaA_pos N f hf hnonres
  rw [henergy, mul_one] at hraw
  have hmass := tsum_sq_oddPairedDenominator_le_weightedTail
    hN hT hv hwindow
  have hscale : 0 ≤ yoshidaA / Real.pi ^ 2 *
      Real.sin (yoshidaA * v) ^ 2 :=
    mul_nonneg
      (div_nonneg YoshidaCoercivityNumerics.yoshidaA_pos.le (sq_nonneg _))
      (sq_nonneg _)
  exact hraw.trans (mul_le_mul_of_nonneg_left hmass hscale)

/-- Yoshida (6.6) for the actual periodic odd tail, with both the infinite
pairing and its Parseval energy normalization discharged. -/
theorem oddTail_paired_central_energy_estimate6_6
    {N : ℕ} (hN : 0 < N) {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (f : YoshidaClippedPeriodicCore yoshidaA)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule
      YoshidaCoercivityNumerics.yoshidaA_pos N)
    (henergy :
      (∫ x : ℝ in -yoshidaA..yoshidaA,
        ‖((f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) x‖ ^ 2) = 1)
    (hwindow : yoshidaA * T < piLowerR * (N + 1 : ℕ)) :
    C / (2 * Real.pi) *
        clippedCentralEnergy yoshidaA
          YoshidaCoercivityNumerics.yoshidaA_pos
          (f : YoshidaClippedSmooth yoshidaA) T ≤
      yoshidaA * C / (2 * Real.pi ^ 3) *
        (T - Real.sin (2 * yoshidaA * T) / (2 * yoshidaA)) *
          weightedTail N T := by
  apply paired_central_energy_estimate6_6
    YoshidaCoercivityNumerics.yoshidaA_pos hC hT
      (f : YoshidaClippedSmooth yoshidaA)
  intro v hv
  apply oddTail_paired_pointwise_estimate_weightedTail hN f hf henergy hT
  · exact abs_le.mpr ⟨by linarith [hv.1], hv.2⟩
  · exact hwindow

/-- On the certified low interval, Yoshida's oscillatory window is at most
two.  This converts the unweighted central-energy form of (6.6) into the same
scalar expression as `lowIntervalPenalty`; it does not control the negative
digamma-weighted integral. -/
theorem oscillatoryWindow_le_two_of_isYoshidaTZero
    {tZero : ℝ} (ht : YoshidaTZeroTailBounds.IsYoshidaTZero tZero) :
    tZero - Real.sin (2 * yoshidaA * tZero) / (2 * yoshidaA) ≤ 2 := by
  have ha := YoshidaCoercivityNumerics.yoshidaA_pos
  have ht0 : 0 ≤ tZero := ht.1.le
  have htUpper : tZero ≤ (51 / 25 : ℝ) :=
    YoshidaTZeroTailBounds.yoshidaTZero_le_51_div_25 ht
  have hat : yoshidaA * tZero ≤
      (((YoshidaTZeroTailBounds.lowCUpperQ : ℚ) : ℝ)) := by
    calc
      yoshidaA * tZero ≤ yoshidaA * (51 / 25 : ℝ) :=
        mul_le_mul_of_nonneg_left htUpper ha.le
      _ ≤ (((YoshidaTZeroTailBounds.lowCUpperQ : ℚ) : ℝ)) :=
        YoshidaTZeroTailBounds.yoshidaA_mul_51_div_25_le_lowCUpper
  have harg0 : 0 ≤ 2 * yoshidaA * tZero := by positivity
  have hargle : 2 * yoshidaA * tZero ≤ Real.pi / 2 := by
    have hpi := Real.pi_gt_three
    norm_num [YoshidaTZeroTailBounds.lowCUpperQ] at hat
    nlinarith
  by_cases htTwo : tZero ≤ 2
  · have hsin0 : 0 ≤ Real.sin (2 * yoshidaA * tZero) :=
      Real.sin_nonneg_of_nonneg_of_le_pi harg0 (by
        nlinarith [hargle, Real.pi_pos])
    have hquot0 : 0 ≤ Real.sin (2 * yoshidaA * tZero) /
        (2 * yoshidaA) := div_nonneg hsin0 (by positivity)
    linarith
  · have htLower : 2 ≤ tZero := le_of_not_ge htTwo
    have hsin := Real.mul_le_sin harg0 hargle
    have hsinDiv : 2 / Real.pi * tZero ≤
        Real.sin (2 * yoshidaA * tZero) / (2 * yoshidaA) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * yoshidaA)).2
      calc
        (2 / Real.pi * tZero) * (2 * yoshidaA) =
            2 / Real.pi * (2 * yoshidaA * tZero) := by ring
        _ ≤ Real.sin (2 * yoshidaA * tZero) := hsin
    have hhalf : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_le_four]
    have hone : (1 : ℝ) ≤ 2 / Real.pi * tZero := by
      calc
        (1 : ℝ) = (1 / 2 : ℝ) * 2 := by norm_num
        _ ≤ 2 / Real.pi * tZero :=
          mul_le_mul hhalf htLower (by norm_num) (by positivity)
    linarith

/-- A scalar central-energy corollary of odd `(6.5)--(6.6)` at `N = 10`.

This sound inequality lands at the expression named `lowIntervalPenalty`, but
is not itself the source's low digamma-loss estimate: that estimate must bound
the integral of `-Re digamma` and interpret `2773 / 1000` as a half-integral
bound, never as a pointwise bound. -/
theorem oddTenTail_central_energy_le_lowIntervalPenalty
    {tZero : ℝ} (ht : YoshidaTZeroTailBounds.IsYoshidaTZero tZero)
    (f : YoshidaClippedPeriodicCore yoshidaA)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule
      YoshidaCoercivityNumerics.yoshidaA_pos 10)
    (henergy :
      (∫ x : ℝ in -yoshidaA..yoshidaA,
        ‖((f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) x‖ ^ 2) = 1) :
    (2773 / 1000 : ℝ) / (2 * Real.pi) *
        clippedCentralEnergy yoshidaA
          YoshidaCoercivityNumerics.yoshidaA_pos
          (f : YoshidaClippedSmooth yoshidaA) tZero ≤
      YoshidaCoercivityNumerics.lowIntervalPenalty 10 tZero := by
  have htUpper : tZero ≤ (51 / 25 : ℝ) :=
    YoshidaTZeroTailBounds.yoshidaTZero_le_51_div_25 ht
  have hwindow : yoshidaA * tZero < piLowerR * (10 + 1 : ℕ) := by
    calc
      yoshidaA * tZero ≤ yoshidaA * (51 / 25 : ℝ) :=
        mul_le_mul_of_nonneg_left htUpper
          YoshidaCoercivityNumerics.yoshidaA_pos.le
      _ ≤ (((YoshidaTZeroTailBounds.lowCUpperQ : ℚ) : ℝ)) :=
        YoshidaTZeroTailBounds.yoshidaA_mul_51_div_25_le_lowCUpper
      _ < piLowerR * (10 + 1 : ℕ) := by
        norm_num [YoshidaTZeroTailBounds.lowCUpperQ, piLowerR]
  have hcentral := oddTail_paired_central_energy_estimate6_6
    (N := 10) (C := (2773 / 1000 : ℝ)) (T := tZero)
    (by norm_num) (by norm_num) ht.1.le f hf henergy hwindow
  refine hcentral.trans ?_
  have hosc := oscillatoryWindow_le_two_of_isYoshidaTZero ht
  have htail0 : 0 ≤ weightedTail 10 tZero :=
    YoshidaCoercivityNumerics.weightedTail_nonneg 10 tZero
  have hscale : 0 ≤ yoshidaA * (2773 / 1000 : ℝ) /
      (2 * Real.pi ^ 3) * weightedTail 10 tZero := by
    apply mul_nonneg
    · exact div_nonneg
        (mul_nonneg YoshidaCoercivityNumerics.yoshidaA_pos.le (by norm_num))
        (by positivity)
    · exact htail0
  calc
    yoshidaA * (2773 / 1000 : ℝ) / (2 * Real.pi ^ 3) *
        (tZero - Real.sin (2 * yoshidaA * tZero) / (2 * yoshidaA)) *
          weightedTail 10 tZero =
      (yoshidaA * (2773 / 1000 : ℝ) / (2 * Real.pi ^ 3) *
        weightedTail 10 tZero) *
        (tZero - Real.sin (2 * yoshidaA * tZero) / (2 * yoshidaA)) := by
          ring
    _ ≤ (yoshidaA * (2773 / 1000 : ℝ) / (2 * Real.pi ^ 3) *
        weightedTail 10 tZero) * 2 :=
      mul_le_mul_of_nonneg_left hosc hscale
    _ = YoshidaCoercivityNumerics.lowIntervalPenalty 10 tZero := by
      unfold YoshidaCoercivityNumerics.lowIntervalPenalty
      ring

end

end ArithmeticHodge.Analysis.YoshidaOddTailPaired
