import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddPerturbationSharp

noncomputable section

open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive

/-!
# Sharp structural bounds for the odd symmetric perturbation

The global regular-kernel error is retained once in each exact entry, while
the dyadic and prime factors are enclosed on one analytic interval.  There
is no interval subdivision or sampled certificate.
-/

private theorem log_two_div_sqrt_two_kernel_upper :
    Real.log 2 / Real.sqrt 2 < (49014 / 100000 : ℝ) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_iff₀ hspos]
  have hlog := strict_log_two_fine_bounds.2
  have hs := sqrt_two_kernel_bounds.1
  nlinarith

private theorem hasDerivAt_oddStructuralCorrelation11_local (x : ℝ) :
    HasDerivAt oddStructuralCorrelation11 (-1 + x ^ 2 / 2) x := by
  rw [show oddStructuralCorrelation11 = fun t : ℝ ↦
      2 / 3 - t + t ^ 3 / 6 by
    funext t
    unfold oddStructuralCorrelation11
    ring]
  convert (((hasDerivAt_const x (2 / 3 : ℝ)).sub (hasDerivAt_id x)).add
    (((hasDerivAt_id x).pow 3).div_const 6)) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem hasDerivAt_oddStructuralCorrelation13_local (x : ℝ) :
    HasDerivAt oddStructuralCorrelation13
      (-1 + 5 * x - (9 / 2) * x ^ 2 + (5 / 8) * x ^ 4) x := by
  rw [show oddStructuralCorrelation13 = fun t : ℝ ↦
      -t + (5 / 2) * t ^ 2 - (3 / 2) * t ^ 3 + (1 / 8) * t ^ 5 by
    funext t
    unfold oddStructuralCorrelation13
    ring]
  convert ((((hasDerivAt_id x).neg.add
      (((hasDerivAt_id x).pow 2).const_mul (5 / 2))).sub
    (((hasDerivAt_id x).pow 3).const_mul (3 / 2))).add
      (((hasDerivAt_id x).pow 5).const_mul (1 / 8))) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem hasDerivAt_oddStructuralCorrelation33_local (x : ℝ) :
    HasDerivAt oddStructuralCorrelation33
      (-1 + 3 * x ^ 2 - (15 / 8) * x ^ 4 + (5 / 16) * x ^ 6) x := by
  rw [show oddStructuralCorrelation33 = fun t : ℝ ↦
      2 / 7 - t + t ^ 3 - (3 / 8) * t ^ 5 + (5 / 112) * t ^ 7 by
    funext t
    unfold oddStructuralCorrelation33
    ring]
  convert (((((hasDerivAt_const x (2 / 7 : ℝ)).sub
      (hasDerivAt_id x)).add ((hasDerivAt_id x).pow 3)).sub
    (((hasDerivAt_id x).pow 5).const_mul (3 / 8))).add
      (((hasDerivAt_id x).pow 7).const_mul (5 / 112))) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem oddStructuralCorrelation11_strictAntiOn_local :
    StrictAntiOn oddStructuralCorrelation11
      (Icc (11699 / 10000 : ℝ) (117 / 100)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (by unfold oddStructuralCorrelation11; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_oddStructuralCorrelation11_local x).deriv]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx2 := pow_lt_pow_left₀ hx.2 hx0 (by norm_num : (2 : ℕ) ≠ 0)
  norm_num at hx2 ⊢
  nlinarith

private theorem oddStructuralCorrelation13_strictAntiOn_local :
    StrictAntiOn oddStructuralCorrelation13
      (Icc (11699 / 10000 : ℝ) (117 / 100)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (by unfold oddStructuralCorrelation13; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_oddStructuralCorrelation13_local x).deriv]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx2lo := pow_lt_pow_left₀ hx.1
    (by norm_num : (0 : ℝ) ≤ 11699 / 10000)
    (by norm_num : (2 : ℕ) ≠ 0)
  have hx4hi := pow_lt_pow_left₀ hx.2 hx0 (by norm_num : (4 : ℕ) ≠ 0)
  norm_num at hx2lo hx4hi ⊢
  nlinarith

private theorem oddStructuralCorrelation33_strictMonoOn_local :
    StrictMonoOn oddStructuralCorrelation33
      (Icc (11699 / 10000 : ℝ) (117 / 100)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (by unfold oddStructuralCorrelation33; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_oddStructuralCorrelation33_local x).deriv]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx2lo := pow_lt_pow_left₀ hx.1
    (by norm_num : (0 : ℝ) ≤ 11699 / 10000)
    (by norm_num : (2 : ℕ) ≠ 0)
  have hx4hi := pow_lt_pow_left₀ hx.2 hx0 (by norm_num : (4 : ℕ) ≠ 0)
  have hx6lo := pow_lt_pow_left₀ hx.1
    (by norm_num : (0 : ℝ) ≤ 11699 / 10000)
    (by norm_num : (6 : ℕ) ≠ 0)
  norm_num at hx2lo hx4hi hx6lo ⊢
  nlinarith

theorem oddStructuralPrimeCorrelation_sharp_bounds :
    (-2364 / 10000 : ℝ) < oddStructuralCorrelation11
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      oddStructuralCorrelation11
        (factorTwoPrimeShift / yoshidaEndpointA) < (-2363 / 10000 : ℝ) ∧
    (1238 / 10000 : ℝ) < oddStructuralCorrelation13
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      oddStructuralCorrelation13
        (factorTwoPrimeShift / yoshidaEndpointA) < (124 / 1000 : ℝ) ∧
    (29 / 1000 : ℝ) < oddStructuralCorrelation33
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      oddStructuralCorrelation33
        (factorTwoPrimeShift / yoshidaEndpointA) < (146 / 5000 : ℝ) := by
  let τ : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  have hτ := factorTwoPrimeRatio_kernel_bounds
  have hlo : (11699 / 10000 : ℝ) ∈
      Icc (11699 / 10000 : ℝ) (117 / 100) := by norm_num
  have hhi : (117 / 100 : ℝ) ∈
      Icc (11699 / 10000 : ℝ) (117 / 100) := by norm_num
  have hτmem : τ ∈ Icc (11699 / 10000 : ℝ) (117 / 100) :=
    ⟨hτ.1.le, hτ.2.le⟩
  have h11lo := oddStructuralCorrelation11_strictAntiOn_local hτmem hhi hτ.2
  have h11hi := oddStructuralCorrelation11_strictAntiOn_local hlo hτmem hτ.1
  have h13lo := oddStructuralCorrelation13_strictAntiOn_local hτmem hhi hτ.2
  have h13hi := oddStructuralCorrelation13_strictAntiOn_local hlo hτmem hτ.1
  have h33lo := oddStructuralCorrelation33_strictMonoOn_local hlo hτmem hτ.1
  have h33hi := oddStructuralCorrelation33_strictMonoOn_local hτmem hhi hτ.2
  dsimp only [τ] at h11lo h11hi h13lo h13hi h33lo h33hi ⊢
  constructor
  · calc
      (-2364 / 10000 : ℝ) < oddStructuralCorrelation11 (117 / 100) := by
        norm_num [oddStructuralCorrelation11]
      _ < oddStructuralCorrelation11
          (factorTwoPrimeShift / yoshidaEndpointA) := h11lo
  constructor
  · calc
      oddStructuralCorrelation11 (factorTwoPrimeShift / yoshidaEndpointA) <
          oddStructuralCorrelation11 (11699 / 10000) := h11hi
      _ < (-2363 / 10000 : ℝ) := by
        norm_num [oddStructuralCorrelation11]
  constructor
  · calc
      (1238 / 10000 : ℝ) < oddStructuralCorrelation13 (117 / 100) := by
        norm_num [oddStructuralCorrelation13]
      _ < oddStructuralCorrelation13
          (factorTwoPrimeShift / yoshidaEndpointA) := h13lo
  constructor
  · calc
      oddStructuralCorrelation13 (factorTwoPrimeShift / yoshidaEndpointA) <
          oddStructuralCorrelation13 (11699 / 10000) := h13hi
      _ < (124 / 1000 : ℝ) := by
        norm_num [oddStructuralCorrelation13]
  constructor
  · calc
      (29 / 1000 : ℝ) < oddStructuralCorrelation33 (11699 / 10000) := by
        norm_num [oddStructuralCorrelation33]
      _ < oddStructuralCorrelation33
          (factorTwoPrimeShift / yoshidaEndpointA) := h33lo
  · calc
      oddStructuralCorrelation33 (factorTwoPrimeShift / yoshidaEndpointA) <
          oddStructuralCorrelation33 (117 / 100) := h33hi
      _ < (146 / 5000 : ℝ) := by
        norm_num [oddStructuralCorrelation33]

/-- Tight rational boxes for the three odd perturbation entries.  The
regular remainders are bounded globally, while all prime signs stay exact. -/
theorem oddStructuralLow_perturbation_sharp_bounds :
    ((14 / 1000 : ℝ) < factorTwoCenteredSymmetricPerturbation centeredP1 ∧
      factorTwoCenteredSymmetricPerturbation centeredP1 < (20 / 1000 : ℝ)) ∧
    ((-11 / 1000 : ℝ) <
        factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3 ∧
      factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3 <
        (-9 / 1000 : ℝ)) ∧
    ((-120 / 1000 : ℝ) <
        factorTwoCenteredSymmetricPerturbation centeredP3 ∧
      factorTwoCenteredSymmetricPerturbation centeredP3 <
        (-117 / 1000 : ℝ)) := by
  let α : ℝ := Real.log 2 / Real.sqrt 2
  let β : ℝ := Real.log 3 / Real.sqrt 3
  let c11 : ℝ := oddStructuralCorrelation11
    (factorTwoPrimeShift / yoshidaEndpointA)
  let c13 : ℝ := oddStructuralCorrelation13
    (factorTwoPrimeShift / yoshidaEndpointA)
  let c33 : ℝ := oddStructuralCorrelation33
    (factorTwoPrimeShift / yoshidaEndpointA)
  have hlog := strict_log_two_fine_bounds
  have hα : (12253 / 25000 : ℝ) < α ∧ α < (49014 / 100000 : ℝ) := by
    exact ⟨by simpa only [α] using log_two_div_sqrt_two_kernel_lower,
      by simpa only [α] using log_two_div_sqrt_two_kernel_upper⟩
  have hβ : (63427 / 100000 : ℝ) < β ∧ β < (6343 / 10000 : ℝ) := by
    simpa only [β] using log_three_div_sqrt_three_kernel_bounds
  have hc := oddStructuralPrimeCorrelation_sharp_bounds
  have hc11 : (-2364 / 10000 : ℝ) < c11 ∧
      c11 < (-2363 / 10000 : ℝ) := by
    simpa only [c11] using ⟨hc.1, hc.2.1⟩
  have hc13 : (1238 / 10000 : ℝ) < c13 ∧
      c13 < (124 / 1000 : ℝ) := by
    simpa only [c13] using ⟨hc.2.2.1, hc.2.2.2.1⟩
  have hc33 : (29 / 1000 : ℝ) < c33 ∧
      c33 < (146 / 5000 : ℝ) := by
    simpa only [c33] using ⟨hc.2.2.2.2.1, hc.2.2.2.2.2⟩
  have hp11Lower :
      (63427 / 100000 : ℝ) * (2363 / 10000) < -(β * c11) := by
    have hcneg : (2363 / 10000 : ℝ) < -c11 := by linarith [hc11.2]
    have := mul_lt_mul_of_nonneg hβ.1 hcneg (by norm_num) (by norm_num)
    nlinarith
  have hp11Upper :
      -(β * c11) < (6343 / 10000 : ℝ) * (2364 / 10000) := by
    have hcneg : -c11 < (2364 / 10000 : ℝ) := by linarith [hc11.1]
    have := mul_lt_mul_of_nonneg hβ.2 hcneg
      (by linarith [hc11.2]) (by linarith [hβ.1])
    nlinarith
  have hp13Lower :
      (63427 / 100000 : ℝ) * (1238 / 10000) < β * c13 :=
    mul_lt_mul_of_nonneg hβ.1 hc13.1 (by norm_num) (by norm_num)
  have hp13Upper :
      β * c13 < (6343 / 10000 : ℝ) * (124 / 1000) :=
    mul_lt_mul_of_nonneg hβ.2 hc13.2
      (by linarith [hc13.1]) (by linarith [hβ.1])
  have hp33Lower :
      (63427 / 100000 : ℝ) * (29 / 1000) < β * c33 :=
    mul_lt_mul_of_nonneg hβ.1 hc33.1 (by norm_num) (by norm_num)
  have hp33Upper :
      β * c33 < (6343 / 10000 : ℝ) * (146 / 5000) :=
    mul_lt_mul_of_nonneg hβ.2 hc33.2
      (by linarith [hc33.1]) (by linarith [hβ.1])
  have he11 := abs_le.mp
    (abs_oddStructuralRegularError11_le oddStructuralRegularKernelControl)
  have he13 := abs_lt.mp abs_oddStructuralRegularError13_lt
  have he33 := abs_le.mp
    (abs_oddStructuralRegularError33_le oddStructuralRegularKernelControl)
  constructor
  · constructor
    · rw [factorTwoCenteredSymmetricPerturbation_p1_structural_eq]
      change (14 / 1000 : ℝ) <
        oddStructuralRegularError oddStructuralCorrelation11 - 4 / 375 +
          (2 / 3 - (2 / 3 : ℝ) * Real.log 2) - α * (2 / 3) - β * c11
      linarith only [he11.1, hlog.2, hα.2, hp11Lower]
    · rw [factorTwoCenteredSymmetricPerturbation_p1_structural_eq]
      change oddStructuralRegularError oddStructuralCorrelation11 - 4 / 375 +
          (2 / 3 - (2 / 3 : ℝ) * Real.log 2) - α * (2 / 3) - β * c11 <
        (20 / 1000 : ℝ)
      linarith only [he11.2, hlog.1, hα.1, hp11Upper]
  constructor
  · constructor
    · rw [factorTwoCenteredSymmetricPerturbationBilinear_p1_p3_structural_eq]
      change (-11 / 1000 : ℝ) <
        oddStructuralRegularError oddStructuralCorrelation13 +
          (7 - 10 * Real.log 2) - β * c13
      linarith only [he13.1, hlog.2, hp13Upper]
    · rw [factorTwoCenteredSymmetricPerturbationBilinear_p1_p3_structural_eq]
      change oddStructuralRegularError oddStructuralCorrelation13 +
          (7 - 10 * Real.log 2) - β * c13 < (-9 / 1000 : ℝ)
      linarith only [he13.2, hlog.1, hp13Lower]
  · constructor
    · rw [factorTwoCenteredSymmetricPerturbation_p3_structural_eq]
      change (-120 / 1000 : ℝ) <
        oddStructuralRegularError oddStructuralCorrelation33 +
          (5 / 21 - (2 / 7 : ℝ) * Real.log 2) - α * (2 / 7) - β * c33
      linarith only [he33.1, hlog.2, hα.2, hp33Upper]
    · rw [factorTwoCenteredSymmetricPerturbation_p3_structural_eq]
      change oddStructuralRegularError oddStructuralCorrelation33 +
          (5 / 21 - (2 / 7 : ℝ) * Real.log 2) - α * (2 / 7) - β * c33 <
        (-117 / 1000 : ℝ)
      linarith only [he33.2, hlog.1, hα.1, hp33Lower]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddPerturbationSharp
