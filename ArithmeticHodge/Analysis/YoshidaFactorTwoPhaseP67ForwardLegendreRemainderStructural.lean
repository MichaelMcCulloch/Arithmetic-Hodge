import ArithmeticHodge.Analysis.YoshidaEndpointOcticPotential
import ArithmeticHodge.Analysis.YoshidaEndpointWeightedCauchy
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardLegendreRemainderStructural

open ShiftedLegendreOrthogonality
open YoshidaEndpointWeightedCauchy
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural

noncomputable section

/-!
# A ninth-order centered-Legendre remainder bound

The monic ninth centered Legendre polynomial is the optimal nodal envelope
for degree-eight interpolation in centered `L²`.  This file packages its
exact squared mass and the resulting Cauchy bound against an arbitrary
profile whose first nine shifted-Legendre moments vanish.  The theorem is
structural: it consumes a single pointwise interpolation-remainder estimate
and never inspects individual higher modes.
-/

/-- The monic centered ninth Legendre polynomial, defined from the existing
shifted-Legendre family by the affine map from `[-1,1]` to `[0,1]`. -/
def centeredLegendreNineMonic (x : ℝ) : ℝ :=
  (-128 / 12155 : ℝ) *
    (shiftedLegendreReal 9).eval ((x + 1) / 2)

/-- Explicit form of the monic centered ninth Legendre polynomial.  This is
used only to normalize its one exact `L²` mass. -/
theorem centeredLegendreNineMonic_eq (x : ℝ) :
    centeredLegendreNineMonic x =
      x ^ 9 - (5148 / 2431 : ℝ) * x ^ 7 +
        (18018 / 12155 : ℝ) * x ^ 5 -
          (924 / 2431 : ℝ) * x ^ 3 +
            (63 / 2431 : ℝ) * x := by
  unfold centeredLegendreNineMonic
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Finset.sum_range_succ, Nat.choose]
  ring

theorem continuous_centeredLegendreNineMonic :
    Continuous centeredLegendreNineMonic := by
  unfold centeredLegendreNineMonic
  fun_prop

/-- Exact squared `L²([-1,1])` mass of the monic ninth Legendre polynomial. -/
theorem integral_centeredLegendreNineMonic_sq :
    (∫ x : ℝ in -1..1, centeredLegendreNineMonic x ^ 2) =
      (32768 / 2807136475 : ℝ) := by
  rw [show (fun x : ℝ ↦ centeredLegendreNineMonic x ^ 2) = fun x ↦
      (x ^ 9 - (5148 / 2431 : ℝ) * x ^ 7 +
        (18018 / 12155 : ℝ) * x ^ 5 -
          (924 / 2431 : ℝ) * x ^ 3 +
            (63 / 2431 : ℝ) * x) ^ 2 by
    funext x
    rw [centeredLegendreNineMonic_eq]]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num

/-- The same constant in its invariant weighted-derivative form. -/
theorem integral_one_sub_sq_pow_nine_div_factorial_eighteen :
    (∫ x : ℝ in -1..1, (1 - x ^ 2) ^ 9) /
        (Nat.factorial 18 : ℝ) =
      (2 / 22561587455281875 : ℝ) := by
  rw [show (∫ x : ℝ in -1..1, (1 - x ^ 2) ^ 9) =
      (131072 / 230945 : ℝ) by
    ring_nf
    repeat rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
    repeat rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
    repeat rw [intervalIntegral.integral_mul_const]
    repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
    norm_num]
  norm_num [Nat.factorial]

/-- A pointwise ninth-order Legendre interpolation envelope gives the exact
centered `L²` remainder constant
`integral (1-x²)^9 / 18! = 2 / 22561587455281875`.

The polynomial `Q` is intentionally arbitrary.  A later representer-specific
lemma can provide it by interpolation, while this theorem remains independent
of the four forward representers. -/
theorem integral_sq_sub_polynomial_le_legendreNineRemainder
    (F : ℝ → ℝ) (hF : Continuous F)
    (Q : ℝ[X]) (M : ℝ) (hM : 0 ≤ M)
    (hrem : ∀ x ∈ Icc (-1 : ℝ) 1,
      |F x - Q.eval ((x + 1) / 2)| ≤
        (M / 362880) * |centeredLegendreNineMonic x|) :
    (∫ x : ℝ in -1..1,
      (F x - Q.eval ((x + 1) / 2)) ^ 2) ≤
        (2 / 22561587455281875 : ℝ) * M ^ 2 := by
  have hR : Continuous (fun x : ℝ ↦
      (F x - Q.eval ((x + 1) / 2)) ^ 2) := by
    fun_prop
  have hP : Continuous (fun x : ℝ ↦
      (M / 362880) ^ 2 * centeredLegendreNineMonic x ^ 2) :=
    continuous_const.mul (continuous_centeredLegendreNineMonic.pow 2)
  have hmono :
      (∫ x : ℝ in -1..1,
        (F x - Q.eval ((x + 1) / 2)) ^ 2) ≤
      ∫ x : ℝ in -1..1,
        (M / 362880) ^ 2 * centeredLegendreNineMonic x ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hR.intervalIntegrable (-1) 1) (hP.intervalIntegrable (-1) 1)
    intro x hx
    have h := hrem x hx
    have hright :
        0 ≤ (M / 362880) * |centeredLegendreNineMonic x| := by
      positivity
    have hsquare := (sq_le_sq₀ (abs_nonneg _) hright).2 h
    rw [sq_abs] at hsquare
    calc
      (F x - Q.eval ((x + 1) / 2)) ^ 2 ≤
          ((M / 362880) * |centeredLegendreNineMonic x|) ^ 2 := hsquare
      _ = (M / 362880) ^ 2 * centeredLegendreNineMonic x ^ 2 := by
        rw [mul_pow, sq_abs]
  calc
    _ ≤ ∫ x : ℝ in -1..1,
        (M / 362880) ^ 2 * centeredLegendreNineMonic x ^ 2 := hmono
    _ = (M / 362880) ^ 2 *
        (∫ x : ℝ in -1..1, centeredLegendreNineMonic x ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (2 / 22561587455281875 : ℝ) * M ^ 2 := by
      rw [integral_centeredLegendreNineMonic_sq]
      ring

/-! ## Moment-gap pairing -/

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

/-- Ninth-order Legendre interpolation plus a nine-moment gap bounds the
entire representer pairing at once.  The low polynomial is removed exactly,
then the monic Legendre remainder and Cauchy--Schwarz give the sharp universal
constant. -/
theorem sq_intervalIntegral_mul_le_legendreNineRemainder
    (w F : ℝ → ℝ) (hw : Continuous w) (hF : Continuous F)
    (hlow : centeredLegendreMomentsVanishBelow w 9)
    (Q : ℝ[X]) (hQ : Q.natDegree < 9)
    (M : ℝ) (hM : 0 ≤ M)
    (hrem : ∀ x ∈ Icc (-1 : ℝ) 1,
      |F x - Q.eval ((x + 1) / 2)| ≤
        (M / 362880) * |centeredLegendreNineMonic x|) :
    (∫ x : ℝ in -1..1, w x * F x) ^ 2 ≤
      (2 / 22561587455281875 : ℝ) * M ^ 2 *
        factorTwoIntrinsicEnergy w := by
  let R : ℝ → ℝ := fun x ↦ F x - Q.eval ((x + 1) / 2)
  have hR : Continuous R := by
    dsimp only [R]
    fun_prop
  have hpoly :
      (∫ x : ℝ in -1..1, w x * Q.eval ((x + 1) / 2)) = 0 :=
    intervalIntegral_mul_shiftedPolynomial_eq_zero w hw hlow Q hQ
  have hwR : IntervalIntegrable (fun x : ℝ ↦ w x * R x)
      volume (-1) 1 := (hw.mul hR).intervalIntegrable (-1) 1
  have hwQ : IntervalIntegrable
      (fun x : ℝ ↦ w x * Q.eval ((x + 1) / 2))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hpair :
      (∫ x : ℝ in -1..1, w x * F x) =
        ∫ x : ℝ in -1..1, R x * w x := by
    calc
      (∫ x : ℝ in -1..1, w x * F x) =
          ∫ x : ℝ in -1..1,
            w x * R x + w x * Q.eval ((x + 1) / 2) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        dsimp only [R]
        ring
      _ = (∫ x : ℝ in -1..1, w x * R x) +
          ∫ x : ℝ in -1..1,
            w x * Q.eval ((x + 1) / 2) := by
        rw [intervalIntegral.integral_add hwR hwQ]
      _ = ∫ x : ℝ in -1..1, R x * w x := by
        rw [hpoly, add_zero]
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
  have hcauchy := sq_intervalIntegral_mul_le R w hR hw
  have hRmass :
      (∫ x : ℝ in -1..1, R x ^ 2) ≤
        (2 / 22561587455281875 : ℝ) * M ^ 2 := by
    simpa only [R] using
      integral_sq_sub_polynomial_le_legendreNineRemainder
        F hF Q M hM hrem
  have hwNonneg : 0 ≤ ∫ x : ℝ in -1..1, w x ^ 2 := by
    exact intervalIntegral.integral_nonneg (by norm_num) fun x _hx ↦ sq_nonneg (w x)
  rw [hpair]
  exact hcauchy.trans <| by
    unfold factorTwoIntrinsicEnergy
    exact mul_le_mul_of_nonneg_right hRmass hwNonneg

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardLegendreRemainderStructural
