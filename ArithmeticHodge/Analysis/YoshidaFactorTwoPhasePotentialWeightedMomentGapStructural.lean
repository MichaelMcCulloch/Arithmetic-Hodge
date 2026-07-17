import ArithmeticHodge.Analysis.YoshidaEndpointPotentialIntegrable
import ArithmeticHodge.Analysis.YoshidaEndpointWeightedCauchy
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePotentialWeightedMomentGapStructural

open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointWeightedCauchy
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural

noncomputable section

/-!
# Potential-weighted moment-gap Cauchy

An odd low--tail representer that vanishes at the center factors as `x * S`.
Ordinary Cauchy--Schwarz then puts its `x^2 w^2` factor into the endpoint
potential, since `x^2 / 2 ≤ -log (1-x^2) / 2`.  This is the correct reserve
for the centered `P8` alternating forward row; an unweighted ninth-derivative
bound loses the decisive central zero.
-/

private theorem sq_intervalIntegral_mul_le
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ x : ℝ in -1..1, f x * g x) ^ 2 ≤
      (∫ x : ℝ in -1..1, f x ^ 2) *
        (∫ x : ℝ in -1..1, g x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have hgMeas : AEStronglyMeasurable g μ :=
    hg.aestronglyMeasurable.restrict
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hgLp : MemLp g 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hgMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖g x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hg.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have h := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1) f g
    (by simp) (by simpa using hfLp) (by simpa using hgLp)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa only [μ, div_one, one_mul] using h

/-- The quadratic part of the endpoint potential controls multiplication by
the centered coordinate. -/
theorem integral_centeredCoordinate_sq_le_two_intrinsicPotential
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in -1..1, (x * w x) ^ 2) ≤
      2 * factorTwoIntrinsicPotentialEnergy w := by
  have hleft : IntervalIntegrable
      (fun x : ℝ ↦ (1 / 2 : ℝ) * (x * w x) ^ 2)
      volume (-1) 1 := by
    exact (by fun_prop : Continuous
      (fun x : ℝ ↦ (1 / 2 : ℝ) * (x * w x) ^ 2)).intervalIntegrable _ _
  have hpotential := intervalIntegrable_endpointPotential_mul_sq w hw
  have hmono :
      (∫ x : ℝ in -1..1, (1 / 2 : ℝ) * (x * w x) ^ 2) ≤
        ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2 := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num) hleft hpotential
    intro x hx
    have hquartic := quartic_le_endpointPotential
      (show |x| < 1 by rw [abs_lt]; exact hx)
    have hscaled := mul_le_mul_of_nonneg_right hquartic (sq_nonneg (w x))
    unfold yoshidaEndpointQuartic at hscaled
    nlinarith [sq_nonneg x, sq_nonneg (w x), sq_nonneg (x ^ 2 * w x)]
  unfold factorTwoIntrinsicPotentialEnergy
  rw [intervalIntegral.integral_const_mul] at hmono
  nlinarith

/-- Factoring a representer through the centered coordinate charges its
pairing to endpoint-potential energy instead of plain `L²` energy. -/
theorem sq_intervalIntegral_mul_centeredFactor_le_potential
    (w S : ℝ → ℝ) (hw : Continuous w) (hS : Continuous S)
    (C : ℝ) (hC : 0 ≤ C)
    (hSmass : (∫ x : ℝ in -1..1, S x ^ 2) ≤ C) :
    (∫ x : ℝ in -1..1, w x * (x * S x)) ^ 2 ≤
      (2 * C) * factorTwoIntrinsicPotentialEnergy w := by
  have hcauchy := sq_intervalIntegral_mul_le
    (fun x : ℝ ↦ x * w x) S (by fun_prop) hS
  have hpair :
      (∫ x : ℝ in -1..1, w x * (x * S x)) =
        ∫ x : ℝ in -1..1, (x * w x) * S x := by
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hxmass : 0 ≤ ∫ x : ℝ in -1..1, (x * w x) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun x _hx ↦ sq_nonneg _
  have hpotential :=
    integral_centeredCoordinate_sq_le_two_intrinsicPotential w hw
  have hpot0 := factorTwoIntrinsicPotentialEnergy_nonneg w
  rw [hpair]
  calc
    (∫ x : ℝ in -1..1, (x * w x) * S x) ^ 2 ≤
        (∫ x : ℝ in -1..1, (x * w x) ^ 2) *
          (∫ x : ℝ in -1..1, S x ^ 2) := hcauchy
    _ ≤ (∫ x : ℝ in -1..1, (x * w x) ^ 2) * C :=
      mul_le_mul_of_nonneg_left hSmass hxmass
    _ ≤ (2 * factorTwoIntrinsicPotentialEnergy w) * C :=
      mul_le_mul_of_nonneg_right hpotential hC
    _ = (2 * C) * factorTwoIntrinsicPotentialEnergy w := by ring

/-- A degree-eight polynomial disappears against a nine-moment residual.
If the remaining representer factors through `x`, the pairing is controlled
by the endpoint-potential reserve and the squared mass of the quotient. -/
theorem sq_intervalIntegral_mul_le_potential_of_momentGap_factor
    (w F S : ℝ → ℝ)
    (hw : Continuous w) (hS : Continuous S)
    (hlow : centeredLegendreMomentsVanishBelow w 9)
    (Q : ℝ[X]) (hQ : Q.natDegree < 9)
    (hfactor : ∀ x ∈ Icc (-1 : ℝ) 1,
      F x = Q.eval ((x + 1) / 2) + x * S x)
    (C : ℝ) (hC : 0 ≤ C)
    (hSmass : (∫ x : ℝ in -1..1, S x ^ 2) ≤ C) :
    (∫ x : ℝ in -1..1, w x * F x) ^ 2 ≤
      (2 * C) * factorTwoIntrinsicPotentialEnergy w := by
  have hpoly :
      (∫ x : ℝ in -1..1, w x * Q.eval ((x + 1) / 2)) = 0 :=
    intervalIntegral_mul_shiftedPolynomial_eq_zero w hw hlow Q hQ
  have hwQ : IntervalIntegrable
      (fun x : ℝ ↦ w x * Q.eval ((x + 1) / 2))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hwS : IntervalIntegrable
      (fun x : ℝ ↦ w x * (x * S x)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hpair :
      (∫ x : ℝ in -1..1, w x * F x) =
        ∫ x : ℝ in -1..1, w x * (x * S x) := by
    calc
      (∫ x : ℝ in -1..1, w x * F x) =
          ∫ x : ℝ in -1..1,
            w x * Q.eval ((x + 1) / 2) + w x * (x * S x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hxIcc : x ∈ Icc (-1 : ℝ) 1 := by
          simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
        change w x * F x =
          w x * Q.eval ((x + 1) / 2) + w x * (x * S x)
        rw [hfactor x hxIcc]
        ring
      _ = (∫ x : ℝ in -1..1, w x * Q.eval ((x + 1) / 2)) +
          ∫ x : ℝ in -1..1, w x * (x * S x) := by
        rw [intervalIntegral.integral_add hwQ hwS]
      _ = _ := by rw [hpoly, zero_add]
  rw [hpair]
  exact sq_intervalIntegral_mul_centeredFactor_le_potential
    w S hw hS C hC hSmass

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePotentialWeightedMomentGapStructural
