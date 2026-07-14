import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp

noncomputable section

open YoshidaConstantBounds
open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoStructuralConstantBounds

/-!
# An ultra-sharp structural lower Gram at the positive even endpoint

The clean and perturbative mixed-entry uncertainties are combined before a
Loewner defect is formed.  Thus the mixed uncertainty is paid once.  The
analytic perturbation remainder remains the single global profile estimate
from the degree-six pole-free model; no interval subdivision, sampling, or
finite certificate is used.
-/

private theorem sqrt_two_ultra_bounds :
    (14142135623 / 10000000000 : ℝ) < Real.sqrt 2 ∧
      Real.sqrt 2 < (14142135624 / 10000000000 : ℝ) := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith

private theorem log_two_div_sqrt_two_ultra_bounds :
    (4901290717 / 10000000000 : ℝ) < Real.log 2 / Real.sqrt 2 ∧
      Real.log 2 / Real.sqrt 2 < (4901290718 / 10000000000 : ℝ) := by
  have hlog := strict_log_two_fine_bounds
  have hs := sqrt_two_ultra_bounds
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [lt_div_iff₀ hspos, div_lt_iff₀ hspos]
  constructor <;> nlinarith

private theorem log_three_div_sqrt_three_ultra_bounds :
    (6342841 / 10000000 : ℝ) < Real.log 3 / Real.sqrt 3 ∧
      Real.log 3 / Real.sqrt 3 < (6342842 / 10000000 : ℝ) := by
  have hlog2 := strict_log_two_fine_bounds
  have hlog32 := strict_log_three_halves_fine_bounds
  have hlog3 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    calc
      Real.log 3 = Real.log (2 * (3 / 2 : ℝ)) := by norm_num
      _ = Real.log 2 + Real.log (3 / 2) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  have hsSq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsLower : (17320508 / 10000000 : ℝ) < Real.sqrt 3 := by
    nlinarith
  have hsUpper : Real.sqrt 3 < (17320509 / 10000000 : ℝ) := by
    nlinarith
  rw [lt_div_iff₀ hspos, div_lt_iff₀ hspos, hlog3]
  constructor <;> nlinarith

private theorem factorTwoPrimeRatio_ultra_bounds :
    (11699250014 / 10000000000 : ℝ) <
        factorTwoPrimeShift / yoshidaEndpointA ∧
      factorTwoPrimeShift / yoshidaEndpointA <
        (11699250015 / 10000000000 : ℝ) := by
  have hlog := strict_log_two_fine_bounds
  have hshift := strict_log_three_halves_fine_bounds
  constructor
  · rw [lt_div_iff₀ yoshidaEndpointA_pos]
    unfold factorTwoPrimeShift yoshidaEndpointA
    nlinarith
  · rw [div_lt_iff₀ yoshidaEndpointA_pos]
    unfold factorTwoPrimeShift yoshidaEndpointA
    nlinarith

private theorem evenPositivePolynomialMoment_ultra_bounds :
    (3906 / 10000000 : ℝ) < evenPositivePolynomialMoment00 ∧
      (79 / 10000000 : ℝ) < evenPositivePolynomialMoment02 ∧
      evenPositivePolynomialMoment02 < (8 / 1000000 : ℝ) ∧
      (104 / 10000000 : ℝ) < evenPositivePolynomialMoment22 := by
  let L : ℝ := 34657359027 / 100000000000
  let U : ℝ := 34657359029 / 100000000000
  have hAL : L ≤ yoshidaEndpointA := by
    dsimp only [L]
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.1]
  have hAU : yoshidaEndpointA ≤ U := by
    dsimp only [U]
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.2]
  have hL0 : 0 ≤ L := by norm_num [L]
  have hA0 : 0 ≤ yoshidaEndpointA := yoshidaEndpointA_pos.le
  have hLpow (n : ℕ) : L ^ n ≤ yoshidaEndpointA ^ n :=
    pow_le_pow_left₀ hL0 hAL n
  have hUpow (n : ℕ) : yoshidaEndpointA ^ n ≤ U ^ n :=
    pow_le_pow_left₀ hA0 hAU n
  have hL2 := hLpow 2
  have hU2 := hUpow 2
  have hL3 := hLpow 3
  have hU3 := hUpow 3
  have hL4 := hLpow 4
  have hU4 := hUpow 4
  have hL5 := hLpow 5
  have hU5 := hUpow 5
  have hL6 := hLpow 6
  have hU6 := hUpow 6
  have hL7 := hLpow 7
  have hU7 := hUpow 7
  unfold evenPositivePolynomialMoment00 evenPositivePolynomialMoment02
    evenPositivePolynomialMoment22 polynomialD0 polynomialD2 polynomialD4
    polynomialD6 poleFreeCoeff0 poleFreeCoeff2 poleFreeCoeff4 poleFreeCoeff6
  norm_num [L, U] at hL2 hU2 hL3 hU3 hL4 hU4 hL5 hU5 hL6 hU6 hL7 hU7 ⊢
  ring_nf at ⊢
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem primeRatio_evenCorrelation_ultra_bounds :
    evenStructuralCorrelation00
        (factorTwoPrimeShift / yoshidaEndpointA) < (830075 / 1000000 : ℝ) ∧
      (825092 / 10000000 : ℝ) <
        evenStructuralCorrelation02
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      evenStructuralCorrelation02
          (factorTwoPrimeShift / yoshidaEndpointA) < (825093 / 10000000 : ℝ) ∧
      (1336533 / 10000000 : ℝ) <
        -evenStructuralCorrelation22
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  let τ : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let L : ℝ := 11699250014 / 10000000000
  let U : ℝ := 11699250015 / 10000000000
  have hτ := factorTwoPrimeRatio_ultra_bounds
  have hL : L ≤ τ := by dsimp only [L, τ]; exact hτ.1.le
  have hU : τ ≤ U := by dsimp only [U, τ]; exact hτ.2.le
  have hL0 : 0 ≤ L := by norm_num [L]
  have hτ0 : 0 ≤ τ := hL0.trans hL
  have hLpow (n : ℕ) : L ^ n ≤ τ ^ n :=
    pow_le_pow_left₀ hL0 hL n
  have hUpow (n : ℕ) : τ ^ n ≤ U ^ n :=
    pow_le_pow_left₀ hτ0 hU n
  have hL2 := hLpow 2
  have hU2 := hUpow 2
  have hL3 := hLpow 3
  have hU3 := hUpow 3
  have hL4 := hLpow 4
  have hU4 := hUpow 4
  have hL5 := hLpow 5
  have hU5 := hUpow 5
  change evenStructuralCorrelation00 τ < (830075 / 1000000 : ℝ) ∧
    (825092 / 10000000 : ℝ) < evenStructuralCorrelation02 τ ∧
    evenStructuralCorrelation02 τ < (825093 / 10000000 : ℝ) ∧
    (1336533 / 10000000 : ℝ) < -evenStructuralCorrelation22 τ
  unfold evenStructuralCorrelation00 evenStructuralCorrelation02
    evenStructuralCorrelation22
  norm_num [L, U] at hL hU hL2 hU2 hL3 hU3 hL4 hU4 hL5 hU5 ⊢
  ring_nf at ⊢
  constructor
  · linarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem evenStructuralKernelBase_ultra_bounds :
    (-227723 / 1000000 : ℝ) < evenStructuralKernelBase00 ∧
      (-204818 / 1000000 : ℝ) < evenStructuralKernelBase02 ∧
      evenStructuralKernelBase02 < (-204817 / 1000000 : ℝ) ∧
      (-188537 / 1000000 : ℝ) < evenStructuralKernelBase22 := by
  have hlog := strict_log_two_fine_bounds
  have ha := log_two_div_sqrt_two_ultra_bounds
  have hb := log_three_div_sqrt_three_ultra_bounds
  have hc := primeRatio_evenCorrelation_ultra_bounds
  have hc00pos : 0 < evenStructuralCorrelation00
      (factorTwoPrimeShift / yoshidaEndpointA) := by
    linarith [primeRatio_evenCorrelation_bounds.1]
  have hc02pos : 0 < evenStructuralCorrelation02
      (factorTwoPrimeShift / yoshidaEndpointA) :=
    primeRatio_evenCorrelation_bounds.2.1
  have hp00 :
      (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation00
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (5265035 / 10000000 : ℝ) := by
    calc
      _ < (6342842 / 10000000 : ℝ) *
          evenStructuralCorrelation00
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hb.2 hc00pos
      _ < (6342842 / 10000000 : ℝ) * (830075 / 1000000) :=
        mul_lt_mul_of_pos_left hc.1 (by norm_num)
      _ < _ := by norm_num
  have hp02 : (261671 / 5000000 : ℝ) <
      (Real.log 3 / Real.sqrt 3) *
        evenStructuralCorrelation02
          (factorTwoPrimeShift / yoshidaEndpointA) := by
    calc
      _ < (6342841 / 10000000 : ℝ) * (825092 / 10000000) := by
        norm_num
      _ < (Real.log 3 / Real.sqrt 3) * (825092 / 10000000) :=
        mul_lt_mul_of_pos_right hb.1 (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hc.2.1 (by positivity)
  have hp02Upper :
      (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation02
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (523344 / 10000000 : ℝ) := by
    calc
      _ < (6342842 / 10000000 : ℝ) *
          evenStructuralCorrelation02
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hb.2 hc02pos
      _ < (6342842 / 10000000 : ℝ) * (825093 / 10000000) :=
        mul_lt_mul_of_pos_left hc.2.2.1 (by norm_num)
      _ < _ := by norm_num
  have hp22 : (847741 / 10000000 : ℝ) <
      (Real.log 3 / Real.sqrt 3) *
        (-evenStructuralCorrelation22
          (factorTwoPrimeShift / yoshidaEndpointA)) := by
    calc
      _ < (6342841 / 10000000 : ℝ) * (1336533 / 10000000) := by
        norm_num
      _ < (Real.log 3 / Real.sqrt 3) * (1336533 / 10000000) :=
        mul_lt_mul_of_pos_right hb.1 (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hc.2.2.2 (by positivity)
  unfold evenStructuralKernelBase00 evenStructuralKernelBase02
    evenStructuralKernelBase22
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem evenPositivePerturbationTaylor_ultra_bounds :
    (-228083 / 1000000 : ℝ) < evenPositivePerturbationTaylor00 ∧
      (-204811 / 1000000 : ℝ) < evenPositivePerturbationTaylor02 ∧
      evenPositivePerturbationTaylor02 < (-204809 / 1000000 : ℝ) ∧
      (-188677 / 1000000 : ℝ) < evenPositivePerturbationTaylor22 := by
  have hb := evenStructuralKernelBase_ultra_bounds
  have hm := evenPositivePolynomialMoment_ultra_bounds
  unfold evenPositivePerturbationTaylor00 evenPositivePerturbationTaylor02
    evenPositivePerturbationTaylor22
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

def evenPositiveEndpointUltraSharp00 : ℝ := 1383 / 10000

def evenPositiveEndpointUltraSharp02 : ℝ := 6769 / 50000

def evenPositiveEndpointUltraSharp22 : ℝ := 1381 / 10000

theorem evenPositiveEndpointUltraSharp_weak_mass :
    evenPositiveEndpointUltraSharp00 + evenPositiveEndpointUltraSharp22 -
        2 * evenPositiveEndpointUltraSharp02 = (141 / 25000 : ℝ) := by
  norm_num [evenPositiveEndpointUltraSharp00,
    evenPositiveEndpointUltraSharp02, evenPositiveEndpointUltraSharp22]

theorem evenPositiveEndpointUltraSharp_principal_minors_pos :
    0 < evenPositiveEndpointUltraSharp00 ∧
      0 < evenPositiveEndpointUltraSharp22 ∧
      (77 / 100000 : ℝ) <
        evenPositiveEndpointUltraSharp00 * evenPositiveEndpointUltraSharp22 -
          evenPositiveEndpointUltraSharp02 ^ 2 := by
  norm_num [evenPositiveEndpointUltraSharp00,
    evenPositiveEndpointUltraSharp02, evenPositiveEndpointUltraSharp22]

private def evenPositiveEndpointUltraDefect00 : ℝ :=
  yoshidaEndpointEvenLowGram00 + evenPositivePerturbationTaylor00 -
    evenPositiveEndpointUltraSharp00

private def evenPositiveEndpointUltraDefect02 : ℝ :=
  yoshidaEndpointEvenLowGram02 + evenPositivePerturbationTaylor02 -
    evenPositiveEndpointUltraSharp02

private def evenPositiveEndpointUltraDefect22 : ℝ :=
  yoshidaEndpointEvenLowGram22 + evenPositivePerturbationTaylor22 -
    evenPositiveEndpointUltraSharp22

private theorem evenPositiveEndpointUltraDefect_entry_bounds :
    (117 / 1000000 : ℝ) < evenPositiveEndpointUltraDefect00 ∧
      0 < evenPositiveEndpointUltraDefect02 ∧
      evenPositiveEndpointUltraDefect02 < (111 / 1000000 : ℝ) ∧
      (123 / 1000000 : ℝ) < evenPositiveEndpointUltraDefect22 := by
  have hc00 := intrinsicEven_cleanGram00_gt
  have hc02 := intrinsicEven_cleanGram02_bounds
  have hc22 := intrinsicEven_cleanGram22_gt
  have ht := evenPositivePerturbationTaylor_ultra_bounds
  unfold evenPositiveEndpointUltraDefect00 evenPositiveEndpointUltraDefect02
    evenPositiveEndpointUltraDefect22 evenPositiveEndpointUltraSharp00
    evenPositiveEndpointUltraSharp02 evenPositiveEndpointUltraSharp22
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem evenPositiveEndpointUltraDefect_det_pos :
    0 < evenPositiveEndpointUltraDefect00 *
          evenPositiveEndpointUltraDefect22 -
        evenPositiveEndpointUltraDefect02 ^ 2 := by
  rcases evenPositiveEndpointUltraDefect_entry_bounds with
    ⟨h00, h02pos, h02, h22⟩
  have h00pos : 0 < evenPositiveEndpointUltraDefect00 :=
    (by norm_num : (0 : ℝ) < 117 / 1000000).trans h00
  have hprod :
      (117 / 1000000 : ℝ) * (123 / 1000000) <
        evenPositiveEndpointUltraDefect00 *
          evenPositiveEndpointUltraDefect22 :=
    mul_lt_mul h00 h22.le (by norm_num) h00pos.le
  have hsq : evenPositiveEndpointUltraDefect02 ^ 2 <
      (111 / 1000000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ h02 h02pos.le (by norm_num)
  have hrational :
      (111 / 1000000 : ℝ) ^ 2 <
        (117 / 1000000) * (123 / 1000000) := by
    norm_num
  nlinarith

private theorem evenPositiveEndpointUltraSharp_quadratic_le_combinedModel
    (c d : ℝ) :
    evenPositiveEndpointUltraSharp00 * c ^ 2 +
        2 * evenPositiveEndpointUltraSharp02 * c * d +
        evenPositiveEndpointUltraSharp22 * d ^ 2 ≤
      (yoshidaEndpointEvenLowGram00 + evenPositivePerturbationTaylor00) * c ^ 2 +
        2 * (yoshidaEndpointEvenLowGram02 + evenPositivePerturbationTaylor02) *
          c * d +
        (yoshidaEndpointEvenLowGram22 + evenPositivePerturbationTaylor22) *
          d ^ 2 := by
  have h00 : 0 < evenPositiveEndpointUltraDefect00 := by
    linarith [evenPositiveEndpointUltraDefect_entry_bounds.1]
  have hdet := evenPositiveEndpointUltraDefect_det_pos
  have hquad : 0 ≤
      evenPositiveEndpointUltraDefect00 * c ^ 2 +
        2 * evenPositiveEndpointUltraDefect02 * c * d +
        evenPositiveEndpointUltraDefect22 * d ^ 2 := by
    by_cases hne : c ≠ 0 ∨ d ≠ 0
    · exact (real_twoByTwo_quadratic_pos
        evenPositiveEndpointUltraDefect00
        evenPositiveEndpointUltraDefect02
        evenPositiveEndpointUltraDefect22 c d h00 hdet hne).le
    · push_neg at hne
      rcases hne with ⟨rfl, rfl⟩
      norm_num
  unfold evenPositiveEndpointUltraDefect00 evenPositiveEndpointUltraDefect02
    evenPositiveEndpointUltraDefect22 at hquad
  nlinarith

/-- Ultra-sharp rational Loewner lower Gram for the complete intrinsic even
positive endpoint. -/
theorem evenPositiveEndpointUltraSharp_quadratic_le (c d : ℝ) :
    evenPositiveEndpointUltraSharp00 * c ^ 2 +
        2 * evenPositiveEndpointUltraSharp02 * c * d +
        evenPositiveEndpointUltraSharp22 * d ^ 2 ≤
      factorTwoIntrinsicStaticEvenQuadratic 1 c d := by
  have hmodel :=
    evenPositiveEndpointUltraSharp_quadratic_le_combinedModel c d
  have hpert := evenPositivePerturbationTaylor_quadratic_le c d
  have hclean :
      yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) =
        yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * d +
          yoshidaEndpointEvenLowGram22 * d ^ 2 := by
    rw [show factorTwoEvenStructuralLowProfile c d =
        (fun x ↦ c * centeredEvenP0 x + d * centeredEvenP2 x) by
      funext x
      unfold factorTwoEvenStructuralLowProfile centeredEvenP0
      ring,
      yoshidaEndpointEvenLowGram_quadratic_eq_clean]
  calc
    _ ≤ (yoshidaEndpointEvenLowGram00 + evenPositivePerturbationTaylor00) *
          c ^ 2 +
        2 * (yoshidaEndpointEvenLowGram02 + evenPositivePerturbationTaylor02) *
          c * d +
        (yoshidaEndpointEvenLowGram22 + evenPositivePerturbationTaylor22) *
          d ^ 2 := hmodel
    _ = (yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * d +
          yoshidaEndpointEvenLowGram22 * d ^ 2) +
        (evenPositivePerturbationTaylor00 * c ^ 2 +
          2 * evenPositivePerturbationTaylor02 * c * d +
          evenPositivePerturbationTaylor22 * d ^ 2) := by ring
    _ ≤ (yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * d +
          yoshidaEndpointEvenLowGram22 * d ^ 2) +
        factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile c d) :=
      by linarith
    _ = yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) +
        factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile c d) := by rw [hclean]
    _ = factorTwoEndpointPhaseDiagonal
          (factorTwoEvenStructuralLowProfile c d) 1 := by
      unfold factorTwoEndpointPhaseDiagonal
      ring
    _ = factorTwoIntrinsicStaticEvenQuadratic 1 c d :=
      (factorTwoIntrinsicStaticEvenQuadratic_eq_profile 1 c d).symm

/-- Direct corollary in the exact rational coordinates used by the Step01
coupled determinant calculation. -/
theorem evenPositiveEndpointStep01Target_quadratic_le (c d : ℝ) :
    (1381 / 10000 : ℝ) * c ^ 2 +
        2 * (6769 / 50000 : ℝ) * c * d +
        (13761 / 100000 : ℝ) * d ^ 2 ≤
      factorTwoIntrinsicStaticEvenQuadratic 1 c d := by
  have h := evenPositiveEndpointUltraSharp_quadratic_le c d
  unfold evenPositiveEndpointUltraSharp00 evenPositiveEndpointUltraSharp02
    evenPositiveEndpointUltraSharp22 at h
  nlinarith [sq_nonneg c, sq_nonneg d]

theorem evenPositiveEndpointStep01Target_weak_mass :
    (1381 / 10000 : ℝ) + (13761 / 100000 : ℝ) -
        2 * (6769 / 50000 : ℝ) = 99 / 20000 := by
  norm_num

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp
