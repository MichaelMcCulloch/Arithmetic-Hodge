import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive

noncomputable section

open YoshidaConstantBounds
open CenteredEndpointCorrelation
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseLowSchur

/-!
# The missing intrinsic even positive endpoint

The clean form is bounded below as one cancellation-preserving quadratic.
The symmetric perturbation is then inserted through its exact pole/prime
kernel expansion, while the global regular-kernel error is charged only once
to the complete profile energy.  Thus no sign is selected for the mixed
coefficient and no interval partition or finite-rank computation occurs.
-/

/-! ## Structural bounds for the fixed prime lag -/

theorem log_two_div_sqrt_two_kernel_upper :
    Real.log 2 / Real.sqrt 2 < (49014 / 100000 : ℝ) := by
  have hlog := strict_log_two_fine_bounds.2
  have hsqrt := sqrt_two_kernel_bounds.1
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_iff₀ hsqrtPos]
  nlinarith

theorem primeRatio_evenCorrelation00_upper :
    evenStructuralCorrelation00
        (factorTwoPrimeShift / yoshidaEndpointA) < (8301 / 10000 : ℝ) := by
  have ht := factorTwoPrimeRatio_kernel_bounds.1
  unfold evenStructuralCorrelation00
  linarith

theorem primeRatio_evenCorrelation02_lower :
    (8241 / 100000 : ℝ) <
      evenStructuralCorrelation02
        (factorTwoPrimeShift / yoshidaEndpointA) := by
  let t : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let a : ℝ := 11699 / 10000
  have ht := factorTwoPrimeRatio_kernel_bounds
  have ha : a < t := by simpa only [a, t] using ht.1
  have htUpper : t < (117 / 100 : ℝ) := by simpa only [t] using ht.2
  have hdiff :
      evenStructuralCorrelation02 t - evenStructuralCorrelation02 a =
        (t - a) *
          (-(t ^ 2 + t * a + a ^ 2) / 2 +
            (3 / 2 : ℝ) * (t + a) - 1) := by
    unfold evenStructuralCorrelation02
    ring
  have hbracket :
      0 < -(t ^ 2 + t * a + a ^ 2) / 2 +
        (3 / 2 : ℝ) * (t + a) - 1 := by
    dsimp only [a] at ha ⊢
    nlinarith [sq_nonneg (t - 11699 / 10000),
      sq_nonneg (117 / 100 - t)]
  have hdir : evenStructuralCorrelation02 a <
      evenStructuralCorrelation02 t := by
    nlinarith [mul_pos (sub_pos.mpr ha) hbracket]
  calc
    (8241 / 100000 : ℝ) < evenStructuralCorrelation02 a := by
      norm_num [a, evenStructuralCorrelation02]
    _ < evenStructuralCorrelation02 t := hdir

theorem primeRatio_evenCorrelation22_upper :
    evenStructuralCorrelation22
        (factorTwoPrimeShift / yoshidaEndpointA) < (-167 / 1250 : ℝ) := by
  let t : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let a : ℝ := 11699 / 10000
  let b : ℝ := 117 / 100
  have ht := factorTwoPrimeRatio_kernel_bounds
  have ha : a < t := by simpa only [a, t] using ht.1
  have hb : t < b := by simpa only [b, t] using ht.2
  have ha0 : 0 < a := by norm_num [a]
  have hb0 : 0 < b := by norm_num [b]
  have ht0 : 0 < t := ha0.trans ha
  have hsqLo : a ^ 2 < t ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr ha) (add_pos ht0 ha0)]
  have hsqHi : t ^ 2 < b ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hb) (add_pos hb0 ht0)]
  have hcubeHi : t ^ 3 < b ^ 3 := by
    have hsum : 0 < b ^ 2 + b * t + t ^ 2 := by positivity
    nlinarith [mul_pos (sub_pos.mpr hb) hsum]
  have hfourthHi : t ^ 4 < b ^ 4 := by
    have hsum : 0 < b ^ 2 + t ^ 2 := by positivity
    nlinarith [mul_pos (sub_pos.mpr hsqHi) hsum]
  have hb3t : b ^ 3 * t < b ^ 4 := by
    have h := mul_lt_mul_of_pos_left hb (by positivity : 0 < b ^ 3)
    nlinarith
  have hb2t2 : b ^ 2 * t ^ 2 < b ^ 4 := by
    have h := mul_lt_mul_of_pos_left hsqHi (by positivity : 0 < b ^ 2)
    nlinarith
  have hbt3 : b * t ^ 3 < b ^ 4 := by
    have h := mul_lt_mul_of_pos_left hcubeHi hb0
    nlinarith
  have hfourSum :
      b ^ 4 + b ^ 3 * t + b ^ 2 * t ^ 2 + b * t ^ 3 + t ^ 4 <
        5 * b ^ 4 := by
    nlinarith
  have hab : a < b := ha.trans hb
  have habSq : a ^ 2 < b ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hab) (add_pos hb0 ha0)]
  have habt : a ^ 2 < b * t := by
    have h1 : a * a < b * a := mul_lt_mul_of_pos_right hab ha0
    have h2 : b * a < b * t := mul_lt_mul_of_pos_left ha hb0
    nlinarith
  have htwoSum : 3 * a ^ 2 < b ^ 2 + b * t + t ^ 2 := by
    nlinarith
  have hbracket :
      0 < -(3 / 40 : ℝ) *
          (b ^ 4 + b ^ 3 * t + b ^ 2 * t ^ 2 + b * t ^ 3 + t ^ 4) +
        (1 / 2 : ℝ) * (b ^ 2 + b * t + t ^ 2) - 1 := by
    have hrational :
        0 < -(3 / 40 : ℝ) * (5 * b ^ 4) +
          (1 / 2 : ℝ) * (3 * a ^ 2) - 1 := by
      norm_num [a, b]
    have hfourScaled :
        -(3 / 40 : ℝ) * (5 * b ^ 4) <
          -(3 / 40 : ℝ) *
            (b ^ 4 + b ^ 3 * t + b ^ 2 * t ^ 2 + b * t ^ 3 + t ^ 4) :=
      mul_lt_mul_of_neg_left hfourSum (by norm_num)
    have htwoScaled :
        (1 / 2 : ℝ) * (3 * a ^ 2) <
          (1 / 2 : ℝ) * (b ^ 2 + b * t + t ^ 2) :=
      mul_lt_mul_of_pos_left htwoSum (by norm_num)
    linarith
  have hdiff :
      evenStructuralCorrelation22 b - evenStructuralCorrelation22 t =
        (b - t) *
          (-(3 / 40 : ℝ) *
              (b ^ 4 + b ^ 3 * t + b ^ 2 * t ^ 2 + b * t ^ 3 + t ^ 4) +
            (1 / 2 : ℝ) * (b ^ 2 + b * t + t ^ 2) - 1) := by
    unfold evenStructuralCorrelation22
    ring
  have hdir : evenStructuralCorrelation22 t <
      evenStructuralCorrelation22 b := by
    nlinarith [mul_pos (sub_pos.mpr hb) hbracket]
  calc
    evenStructuralCorrelation22
        (factorTwoPrimeShift / yoshidaEndpointA) =
        evenStructuralCorrelation22 t := rfl
    _ < evenStructuralCorrelation22 b := hdir
    _ < (-167 / 1250 : ℝ) := by
      norm_num [b, evenStructuralCorrelation22]

/-! ## Rational kernel coefficients -/

theorem evenStructuralKernelBase00_lower :
    (-4559 / 20000 : ℝ) < evenStructuralKernelBase00 := by
  have hlog := strict_log_two_fine_bounds.2
  have ha := log_two_div_sqrt_two_kernel_upper
  have hb := log_three_div_sqrt_three_kernel_bounds.2
  have hC := primeRatio_evenCorrelation00_upper
  have hCpos := primeRatio_evenCorrelation_bounds.1
  have hCpos' : 0 < evenStructuralCorrelation00
      (factorTwoPrimeShift / yoshidaEndpointA) := by linarith
  have hbpos : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  have hprod :
      (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation00
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (6343 / 10000 : ℝ) * (8301 / 10000 : ℝ) := by
    calc
      (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation00
            (factorTwoPrimeShift / yoshidaEndpointA) <
          (6343 / 10000 : ℝ) *
            evenStructuralCorrelation00
              (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hb hCpos'
      _ < (6343 / 10000 : ℝ) * (8301 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_left hC (by norm_num)
  unfold evenStructuralKernelBase00
  nlinarith

theorem evenStructuralKernelBase02_bounds :
    (-41 / 200 : ℝ) < evenStructuralKernelBase02 ∧
      evenStructuralKernelBase02 < (-819 / 4000 : ℝ) := by
  have hlog := strict_log_two_fine_bounds
  have hb := log_three_div_sqrt_three_kernel_bounds
  have hC := primeRatio_evenCorrelation_bounds.2.2.1
  have hCpos := primeRatio_evenCorrelation_bounds.2.1
  have hClower := primeRatio_evenCorrelation02_lower
  have hbpos : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  have hprodUpper :
      (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation02
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (6343 / 10000 : ℝ) * (1651 / 20000 : ℝ) := by
    calc
      (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation02
            (factorTwoPrimeShift / yoshidaEndpointA) <
          (6343 / 10000 : ℝ) *
            evenStructuralCorrelation02
              (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hb.2 hCpos
      _ < (6343 / 10000 : ℝ) * (1651 / 20000 : ℝ) :=
        mul_lt_mul_of_pos_left hC (by norm_num)
  have hprodLower :
      (63427 / 100000 : ℝ) * (8241 / 100000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation02
            (factorTwoPrimeShift / yoshidaEndpointA) := by
    calc
      (63427 / 100000 : ℝ) * (8241 / 100000 : ℝ) <
          (Real.log 3 / Real.sqrt 3) * (8241 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_right hb.1 (by norm_num)
      _ < (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation02
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_left hClower hbpos
  unfold evenStructuralKernelBase02
  constructor <;> nlinarith

theorem evenStructuralKernelBase22_lower :
    (-3781 / 20000 : ℝ) < evenStructuralKernelBase22 := by
  have hlog := strict_log_two_fine_bounds.2
  have ha := log_two_div_sqrt_two_kernel_upper
  have hb := log_three_div_sqrt_three_kernel_bounds.1
  have hC := primeRatio_evenCorrelation22_upper
  have hbpos : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  have hnegC : (167 / 1250 : ℝ) <
      -evenStructuralCorrelation22
        (factorTwoPrimeShift / yoshidaEndpointA) := by linarith
  have hprod :
      (63427 / 100000 : ℝ) * (167 / 1250 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          (-evenStructuralCorrelation22
            (factorTwoPrimeShift / yoshidaEndpointA)) := by
    calc
      (63427 / 100000 : ℝ) * (167 / 1250 : ℝ) <
          (Real.log 3 / Real.sqrt 3) * (167 / 1250 : ℝ) :=
        mul_lt_mul_of_pos_right hb (by norm_num)
      _ < (Real.log 3 / Real.sqrt 3) *
          (-evenStructuralCorrelation22
            (factorTwoPrimeShift / yoshidaEndpointA)) :=
        mul_lt_mul_of_pos_left hnegC hbpos
  unfold evenStructuralKernelBase22
  nlinarith

/-! ## The positive-endpoint matrix -/

def evenStructuralPlusKernel00 : ℝ :=
  (7329 / 20000 : ℝ) + evenStructuralKernelBase00 - 1 / 250

def evenStructuralPlusKernel02 : ℝ :=
  (1361 / 4000 : ℝ) + evenStructuralKernelBase02

def evenStructuralPlusKernel22 : ℝ :=
  (6537 / 20000 : ℝ) + evenStructuralKernelBase22 - 1 / 1250

theorem evenStructuralPlusKernel00_lower :
    (269 / 2000 : ℝ) < evenStructuralPlusKernel00 := by
  unfold evenStructuralPlusKernel00
  linarith [evenStructuralKernelBase00_lower]

theorem evenStructuralPlusKernel02_abs_upper :
    |evenStructuralPlusKernel02| < (271 / 2000 : ℝ) := by
  have h := evenStructuralKernelBase02_bounds
  have hpos : 0 < evenStructuralPlusKernel02 := by
    unfold evenStructuralPlusKernel02
    linarith [h.1]
  rw [abs_of_pos hpos]
  unfold evenStructuralPlusKernel02
  linarith [h.2]

theorem evenStructuralPlusKernel22_lower :
    (137 / 1000 : ℝ) < evenStructuralPlusKernel22 := by
  unfold evenStructuralPlusKernel22
  linarith [evenStructuralKernelBase22_lower]

theorem evenStructuralPlusKernel_principal_minors_pos :
    0 < evenStructuralPlusKernel00 ∧
      0 < evenStructuralPlusKernel00 * evenStructuralPlusKernel22 -
        evenStructuralPlusKernel02 ^ 2 := by
  have h00 := evenStructuralPlusKernel00_lower
  have h02 := evenStructuralPlusKernel02_abs_upper
  have h22 := evenStructuralPlusKernel22_lower
  have h00pos : 0 < evenStructuralPlusKernel00 :=
    (by norm_num : (0 : ℝ) < 269 / 2000).trans h00
  have h22pos : 0 < evenStructuralPlusKernel22 :=
    (by norm_num : (0 : ℝ) < 137 / 1000).trans h22
  have hprod :
      (269 / 2000 : ℝ) * (137 / 1000 : ℝ) <
        evenStructuralPlusKernel00 * evenStructuralPlusKernel22 :=
    mul_lt_mul h00 h22.le (by norm_num) h00pos.le
  have hsq : evenStructuralPlusKernel02 ^ 2 < (271 / 2000 : ℝ) ^ 2 := by
    have hright : 0 < (271 / 2000 : ℝ) +
        |evenStructuralPlusKernel02| :=
      add_pos_of_pos_of_nonneg (by norm_num) (abs_nonneg _)
    have hprod := mul_pos (sub_pos.mpr h02) hright
    nlinarith [sq_abs evenStructuralPlusKernel02]
  constructor
  · exact h00pos
  · have hrational : (271 / 2000 : ℝ) ^ 2 <
        (269 / 2000 : ℝ) * (137 / 1000 : ℝ) := by norm_num
    nlinarith

/-- The sharp clean lower form plus the exact kernel block dominates the
positive endpoint after charging the regular error once to the full energy. -/
theorem evenStructuralPlusKernel_quadratic_le_endpoint
    (c d : ℝ) :
    evenStructuralPlusKernel00 * c ^ 2 +
        2 * evenStructuralPlusKernel02 * c * d +
        evenStructuralPlusKernel22 * d ^ 2 ≤
      yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) +
        factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile c d) := by
  have hprofile : factorTwoEvenStructuralLowProfile c d =
      yoshidaEndpointEvenLowProfile c d := by
    funext x
    unfold factorTwoEvenStructuralLowProfile
      yoshidaEndpointEvenLowProfile centeredEvenP0
    ring
  have hclean := intrinsicEven_clean_profile_rationalQuadratic_le c d
  rw [← hprofile] at hclean
  have herr := abs_evenStructuralRegularError_profile_le c d
  have herrLower :
      -(1 / 500 : ℝ) * (2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2) ≤
        evenStructuralRegularError
          (centeredEndpointCorrelation
            (factorTwoEvenStructuralLowProfile c d)) :=
    by
      nlinarith [neg_le_of_abs_le herr]
  rw [factorTwoCenteredSymmetricPerturbation_even_profile_kernel_eq]
  unfold evenStructuralPlusKernel00 evenStructuralPlusKernel02
    evenStructuralPlusKernel22
  nlinarith

theorem factorTwoIntrinsicEven_plus_endpoint_structural_pos
    (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
    0 < yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) +
        factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile c d) := by
  have hmatrix := real_twoByTwo_quadratic_pos
    evenStructuralPlusKernel00 evenStructuralPlusKernel02
    evenStructuralPlusKernel22 c d
    evenStructuralPlusKernel_principal_minors_pos.1
    evenStructuralPlusKernel_principal_minors_pos.2 hne
  exact hmatrix.trans_le
    (evenStructuralPlusKernel_quadratic_le_endpoint c d)

/-- Both scalar Sylvester gates at symmetric phase `+1`. -/
theorem factorTwoIntrinsicEven_plus_endpoint_structural_gates :
    0 < factorTwoStructuralPhaseLow00 1 ∧
      0 < factorTwoIntrinsicEvenPhaseDet 1 := by
  apply factorTwoIntrinsicEven_endpoint_gates_of_profile_pos 1
  intro c d hne
  simpa only [one_mul] using
    factorTwoIntrinsicEven_plus_endpoint_structural_pos c d hne

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
