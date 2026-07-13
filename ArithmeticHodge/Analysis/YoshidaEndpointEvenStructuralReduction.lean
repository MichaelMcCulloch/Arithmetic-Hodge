import ArithmeticHodge.Analysis.ShiftedLegendreCenteredLowModes
import ArithmeticHodge.Analysis.ShiftedLegendreCenteredParity
import ArithmeticHodge.Analysis.ShiftedLegendreFiniteEnergyGap
import ArithmeticHodge.Analysis.ShiftedLegendreL2HigherGap
import ArithmeticHodge.Analysis.UnitIntervalIntegralBridge

set_option autoImplicit false

open Finset Filter MeasureTheory Polynomial Real
open scoped BigOperators Topology unitInterval

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenStructuralReduction

open ShiftedLegendreCenteredLowModes
open ShiftedLegendreCenteredParity
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open ShiftedLegendreL2HigherGap
open ShiftedLegendreL2SpectralGap
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection

noncomputable section

/-!
# Structural endpoint reduction in the even sector

The endpoint-even logarithmic form has exactly two low modes: the constant
mode, with eigenvalue zero, and the centered degree-two Legendre mode, with
eigenvalue `2 H₂ = 3`.  Every remaining even mode starts at degree four and
is controlled at once by `2 H₄ = 25/6`.  This is an infinite spectral
reduction, not a finite mode cutoff.
-/

/-- Exact logarithmic weights on degrees zero and two, followed by the
uniform degree-four tail weight. -/
def evenZeroTwoTailWeight (n : ℕ) : ℝ :=
  if n = 0 then 0 else if n = 2 then 3 else 25 / 6

theorem evenZeroTwoTailWeight_mul_repr_sq_le
    (F : UnitIntervalL2)
    (hparity : ∀ n : ℕ, Odd n →
      shiftedLegendreHilbertBasis.repr F n = 0)
    (n : ℕ) :
    evenZeroTwoTailWeight n *
        (shiftedLegendreHilbertBasis.repr F n) ^ 2 ≤
      (2 * (harmonic n : ℝ)) *
        (shiftedLegendreHilbertBasis.repr F n) ^ 2 := by
  by_cases hn0 : n = 0
  · subst n
    simp [evenZeroTwoTailWeight]
  · by_cases hn2 : n = 2
    · subst n
      norm_num [evenZeroTwoTailWeight, harmonic, Finset.sum_range_succ]
    · by_cases hnodd : Odd n
      · rw [hparity n hnodd]
        simp
      · have hneven : Even n := Nat.not_odd_iff_even.mp hnodd
        have hn4 : 4 ≤ n := by
          rcases hneven with ⟨k, hk⟩
          omega
        have hH : (25 / 6 : ℝ) ≤ 2 * (harmonic n : ℝ) := by
          have hmono := harmonic_cast_mono hn4
          norm_num [harmonic, Finset.sum_range_succ] at hmono ⊢
          linarith
        rw [evenZeroTwoTailWeight, if_neg hn0, if_neg hn2]
        exact mul_le_mul_of_nonneg_right hH (sq_nonneg _)

theorem evenZeroTwoTail_partialWeight_le_partialSpectralEnergy
    (F : UnitIntervalL2)
    (hparity : ∀ n : ℕ, Odd n →
      shiftedLegendreHilbertBasis.repr F n = 0)
    (N : ℕ) :
    (∑ n ∈ Finset.range N,
        evenZeroTwoTailWeight n *
          (shiftedLegendreHilbertBasis.repr F n) ^ 2) ≤
      shiftedLegendrePartialSpectralEnergy F N := by
  rw [shiftedLegendrePartialSpectralEnergy]
  apply Finset.sum_le_sum
  intro n _hn
  exact evenZeroTwoTailWeight_mul_repr_sq_le F hparity n

theorem evenZeroTwoTail_partialWeight_eq
    (F : UnitIntervalL2) (N : ℕ) (hN : 3 ≤ N) :
    (∑ n ∈ Finset.range N,
        evenZeroTwoTailWeight n *
          (shiftedLegendreHilbertBasis.repr F n) ^ 2) =
      3 * (shiftedLegendreHilbertBasis.repr F 2) ^ 2 +
        (25 / 6 : ℝ) *
          (shiftedLegendrePartialNormSq F N -
            (shiftedLegendreHilbertBasis.repr F 0) ^ 2 -
            (shiftedLegendreHilbertBasis.repr F 2) ^ 2) := by
  have h0 : 0 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  have h2 : 2 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  rw [shiftedLegendrePartialNormSq]
  calc
    (∑ n ∈ Finset.range N,
        evenZeroTwoTailWeight n *
          (shiftedLegendreHilbertBasis.repr F n) ^ 2) =
        ∑ n ∈ Finset.range N,
          ((25 / 6 : ℝ) *
              (shiftedLegendreHilbertBasis.repr F n) ^ 2 +
            (if n = 0 then
              (-(25 / 6 : ℝ)) *
                (shiftedLegendreHilbertBasis.repr F n) ^ 2 else 0) +
            (if n = 2 then
              (3 - 25 / 6 : ℝ) *
                (shiftedLegendreHilbertBasis.repr F n) ^ 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro n _hn
      by_cases hn0 : n = 0
      · subst n
        simp [evenZeroTwoTailWeight]
      · by_cases hn2 : n = 2
        · subst n
          simp [evenZeroTwoTailWeight]
          ring
        · simp [evenZeroTwoTailWeight, hn0, hn2]
    _ = (25 / 6 : ℝ) *
          ∑ n ∈ Finset.range N,
            (shiftedLegendreHilbertBasis.repr F n) ^ 2 +
        (-(25 / 6 : ℝ)) *
          (shiftedLegendreHilbertBasis.repr F 0) ^ 2 +
        (3 - 25 / 6 : ℝ) *
          (shiftedLegendreHilbertBasis.repr F 2) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      simp [h0, h2]
    _ = _ := by ring

/-- The exact degree-zero/degree-two block and the full even tail are bounded
by any common upper bound for the finite spectral energies. -/
theorem even_zero_two_tail_norm_sq_le_of_partialSpectralEnergy_le
    (F : UnitIntervalL2)
    (hparity : ∀ n : ℕ, Odd n →
      shiftedLegendreHilbertBasis.repr F n = 0)
    (Q : ℝ)
    (hQ : ∀ N : ℕ, shiftedLegendrePartialSpectralEnergy F N ≤ Q) :
    3 * (shiftedLegendreHilbertBasis.repr F 2) ^ 2 +
        (25 / 6 : ℝ) *
          (‖F‖ ^ 2 - (shiftedLegendreHilbertBasis.repr F 0) ^ 2 -
            (shiftedLegendreHilbertBasis.repr F 2) ^ 2) ≤ Q := by
  let lower : ℕ → ℝ := fun N ↦
    3 * (shiftedLegendreHilbertBasis.repr F 2) ^ 2 +
      (25 / 6 : ℝ) *
        (shiftedLegendrePartialNormSq F N -
          (shiftedLegendreHilbertBasis.repr F 0) ^ 2 -
          (shiftedLegendreHilbertBasis.repr F 2) ^ 2)
  have hlower : Filter.Tendsto lower Filter.atTop
      (nhds
        (3 * (shiftedLegendreHilbertBasis.repr F 2) ^ 2 +
          (25 / 6 : ℝ) *
            (‖F‖ ^ 2 - (shiftedLegendreHilbertBasis.repr F 0) ^ 2 -
              (shiftedLegendreHilbertBasis.repr F 2) ^ 2))) := by
    dsimp only [lower]
    exact tendsto_const_nhds.add
      ((((tendsto_shiftedLegendrePartialNormSq F).sub tendsto_const_nhds).sub
        tendsto_const_nhds).const_mul (25 / 6 : ℝ))
  apply le_of_tendsto hlower
  filter_upwards [Filter.eventually_ge_atTop 3] with N hN
  dsimp only [lower]
  rw [← evenZeroTwoTail_partialWeight_eq F N hN]
  exact (evenZeroTwoTail_partialWeight_le_partialSpectralEnergy F hparity N).trans
    (hQ N)

/-- The two fixed centered even Legendre modes. -/
def centeredEvenP0 (_x : ℝ) : ℝ := 1

def centeredEvenP2 (x : ℝ) : ℝ := (3 * x ^ 2 - 1) / 2

/-- Orthogonal projection coefficients onto the fixed `P₀/P₂` block. -/
def centeredEvenP0Coefficient (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x

def centeredEvenP2Coefficient (w : ℝ → ℝ) : ℝ :=
  (5 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x * centeredEvenP2 x

/-- The genuinely infinite even tail after removing the fixed low block. -/
def centeredEvenZeroTwoResidual (w : ℝ → ℝ) : ℝ → ℝ := fun x ↦
  w x - centeredEvenP0Coefficient w * centeredEvenP0 x -
    centeredEvenP2Coefficient w * centeredEvenP2 x

theorem integral_centeredEvenP0_sq :
    (∫ x : ℝ in -1..1, centeredEvenP0 x ^ 2) = 2 := by
  simp [centeredEvenP0]
  norm_num

theorem integral_centeredEvenP0_mul_p2 :
    (∫ x : ℝ in -1..1, centeredEvenP0 x * centeredEvenP2 x) = 0 := by
  rw [show (fun x : ℝ ↦ centeredEvenP0 x * centeredEvenP2 x) =
      fun x ↦ (3 / 2 : ℝ) * x ^ 2 - 1 / 2 by
    funext x
    simp only [centeredEvenP0, centeredEvenP2]
    ring]
  rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
    intervalIntegral.integral_const_mul, integral_pow]
  norm_num

theorem integral_centeredEvenP2_sq :
    (∫ x : ℝ in -1..1, centeredEvenP2 x ^ 2) = 2 / 5 := by
  rw [show (fun x : ℝ ↦ centeredEvenP2 x ^ 2) =
      fun x ↦ (9 / 4 : ℝ) * x ^ 4 - (3 / 2 : ℝ) * x ^ 2 + 1 / 4 by
    funext x
    simp only [centeredEvenP2]
    ring]
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  norm_num

theorem integral_mul_centeredEvenP0_eq (w : ℝ → ℝ) :
    (∫ x : ℝ in -1..1, w x * centeredEvenP0 x) =
      2 * centeredEvenP0Coefficient w := by
  unfold centeredEvenP0 centeredEvenP0Coefficient
  simp only [mul_one]
  ring

theorem integral_mul_centeredEvenP2_eq (w : ℝ → ℝ) :
    (∫ x : ℝ in -1..1, w x * centeredEvenP2 x) =
      (2 / 5 : ℝ) * centeredEvenP2Coefficient w := by
  unfold centeredEvenP2Coefficient
  ring

theorem integral_centeredEvenZeroTwoResidual_sq
    (w : ℝ → ℝ) (hwcont : Continuous w) :
    (∫ x : ℝ in -1..1, centeredEvenZeroTwoResidual w x ^ 2) =
      (∫ x : ℝ in -1..1, w x ^ 2) -
        2 * centeredEvenP0Coefficient w ^ 2 -
        (2 / 5 : ℝ) * centeredEvenP2Coefficient w ^ 2 := by
  let a := centeredEvenP0Coefficient w
  let b := centeredEvenP2Coefficient w
  rw [show (fun x : ℝ ↦ centeredEvenZeroTwoResidual w x ^ 2) = fun x ↦
      w x ^ 2 + (-2 * a) * (w x * centeredEvenP0 x) +
        (-2 * b) * (w x * centeredEvenP2 x) +
        a ^ 2 * centeredEvenP0 x ^ 2 +
        (2 * a * b) * (centeredEvenP0 x * centeredEvenP2 x) +
        b ^ 2 * centeredEvenP2 x ^ 2 by
    funext x
    dsimp only [centeredEvenZeroTwoResidual, a, b]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    exact Continuous.intervalIntegrable (hwcont.pow 2) (-1) 1
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [centeredEvenP0, centeredEvenP2]
    fun_prop
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_mul_centeredEvenP0_eq, integral_mul_centeredEvenP2_eq,
    integral_centeredEvenP0_sq, integral_centeredEvenP0_mul_p2,
    integral_centeredEvenP2_sq]
  dsimp only [a, b]
  ring

theorem centeredEvenZeroTwoResidual_even
    (w : ℝ → ℝ) (hweven : Function.Even w) :
    Function.Even (centeredEvenZeroTwoResidual w) := by
  intro x
  unfold centeredEvenZeroTwoResidual centeredEvenP0 centeredEvenP2
  rw [hweven x]
  ring

theorem integral_centeredEvenResidual_mul_p0
    (w : ℝ → ℝ) (hwcont : Continuous w) :
    (∫ x : ℝ in -1..1,
      centeredEvenZeroTwoResidual w x * centeredEvenP0 x) = 0 := by
  let a := centeredEvenP0Coefficient w
  let b := centeredEvenP2Coefficient w
  rw [show (fun x : ℝ ↦
      centeredEvenZeroTwoResidual w x * centeredEvenP0 x) = fun x ↦
        w x * centeredEvenP0 x + (-a) * centeredEvenP0 x ^ 2 +
          (-b) * (centeredEvenP0 x * centeredEvenP2 x) by
    funext x
    dsimp only [centeredEvenZeroTwoResidual, a, b]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [centeredEvenP0, centeredEvenP2]
    fun_prop
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_mul_centeredEvenP0_eq, integral_centeredEvenP0_sq,
    integral_centeredEvenP0_mul_p2]
  dsimp only [a, b]
  ring

theorem integral_centeredEvenResidual_mul_p2
    (w : ℝ → ℝ) (hwcont : Continuous w) :
    (∫ x : ℝ in -1..1,
      centeredEvenZeroTwoResidual w x * centeredEvenP2 x) = 0 := by
  let a := centeredEvenP0Coefficient w
  let b := centeredEvenP2Coefficient w
  rw [show (fun x : ℝ ↦
      centeredEvenZeroTwoResidual w x * centeredEvenP2 x) = fun x ↦
        w x * centeredEvenP2 x +
          (-a) * (centeredEvenP0 x * centeredEvenP2 x) +
          (-b) * centeredEvenP2 x ^ 2 by
    funext x
    dsimp only [centeredEvenZeroTwoResidual, a, b]
    ring]
  repeat rw [intervalIntegral.integral_add]
  all_goals try
    apply Continuous.intervalIntegrable
    simp only [centeredEvenP0, centeredEvenP2]
    fun_prop
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_mul_centeredEvenP2_eq, integral_centeredEvenP0_mul_p2,
    integral_centeredEvenP2_sq]
  dsimp only [a, b]
  ring

private theorem eval_shiftedLegendreReal_two (t : ℝ) :
    (shiftedLegendreReal 2).eval t = 1 - 6 * t + 6 * t ^ 2 := by
  calc
    (shiftedLegendreReal 2).eval t =
        (shiftedLegendreReal 2).eval (((2 * t - 1) + 1) / 2) := by
      congr 1
      ring
    _ = (centeredShiftedLegendreReal 2).eval (2 * t - 1) :=
      (eval_centeredShiftedLegendreReal 2 (2 * t - 1)).symm
    _ = (3 * (2 * t - 1) ^ 2 - 1) / 2 :=
      eval_centeredShiftedLegendreReal_two _
    _ = 1 - 6 * t + 6 * t ^ 2 := by ring

theorem norm_shiftedLegendreL2_zero :
    ‖shiftedLegendreL2 0‖ = 1 := by
  have hsq : ‖shiftedLegendreL2 0‖ ^ 2 = (1 : ℝ) := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ
      (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ
        (polynomialToContinuous (shiftedLegendreReal 0)))
      (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ
        (polynomialToContinuous (shiftedLegendreReal 0))) = (1 : ℝ)
    have hinner := MeasureTheory.ContinuousMap.inner_toLp
      (𝕜 := ℝ) (volume : Measure unitInterval)
      (polynomialToContinuous (shiftedLegendreReal 0))
      (polynomialToContinuous (shiftedLegendreReal 0))
    calc
      _ = ∫ t : unitInterval,
          (polynomialToContinuous (shiftedLegendreReal 0)) t *
            starRingEnd ℝ
              ((polynomialToContinuous (shiftedLegendreReal 0)) t) := hinner
      _ = ∫ _t : unitInterval, (1 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [] with t
        simp [shiftedLegendreReal, Polynomial.shiftedLegendre]
      _ = 1 := by simp
  nlinarith [norm_nonneg (shiftedLegendreL2 0)]

theorem norm_sq_shiftedLegendreL2_two :
    ‖shiftedLegendreL2 2‖ ^ 2 = (1 / 5 : ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ
    (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ
      (polynomialToContinuous (shiftedLegendreReal 2)))
    (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ
      (polynomialToContinuous (shiftedLegendreReal 2))) = (1 / 5 : ℝ)
  have hinner := MeasureTheory.ContinuousMap.inner_toLp
    (𝕜 := ℝ) (volume : Measure unitInterval)
    (polynomialToContinuous (shiftedLegendreReal 2))
    (polynomialToContinuous (shiftedLegendreReal 2))
  calc
    _ = ∫ t : unitInterval,
        (polynomialToContinuous (shiftedLegendreReal 2)) t *
          starRingEnd ℝ
            ((polynomialToContinuous (shiftedLegendreReal 2)) t) := hinner
    _ = ∫ t : unitInterval,
        (shiftedLegendreReal 2).eval (t : ℝ) *
          (shiftedLegendreReal 2).eval (t : ℝ) := by
      rfl
    _ = ∫ t : ℝ in 0..1,
        (shiftedLegendreReal 2).eval t *
          (shiftedLegendreReal 2).eval t :=
      integral_unitInterval_eq_intervalIntegral
        (fun t : ℝ ↦
          (shiftedLegendreReal 2).eval t *
            (shiftedLegendreReal 2).eval t)
    _ = ∫ t : ℝ in 0..1, (1 - 6 * t + 6 * t ^ 2) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t _ht
      change (shiftedLegendreReal 2).eval t *
        (shiftedLegendreReal 2).eval t = (1 - 6 * t + 6 * t ^ 2) ^ 2
      rw [eval_shiftedLegendreReal_two]
      ring
    _ = ∫ t : ℝ in 0..1,
        (36 * t ^ 4 - 72 * t ^ 3 + 48 * t ^ 2 - 12 * t + 1) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      ring
    _ = (1 / 5 : ℝ) := by
      let A : ℝ → ℝ := fun t ↦
        (36 / 5 : ℝ) * t ^ 5 - 18 * t ^ 4 + 16 * t ^ 3 -
          6 * t ^ 2 + t
      have hderiv (t : ℝ) : HasDerivAt A
          (36 * t ^ 4 - 72 * t ^ 3 + 48 * t ^ 2 - 12 * t + 1) t := by
        dsimp only [A]
        convert (((((hasDerivAt_const t (36 / 5 : ℝ)).mul
            ((hasDerivAt_id t).pow 5)).sub
          ((hasDerivAt_const t (18 : ℝ)).mul
            ((hasDerivAt_id t).pow 4))).add
          ((hasDerivAt_const t (16 : ℝ)).mul
            ((hasDerivAt_id t).pow 3))).sub
          ((hasDerivAt_const t (6 : ℝ)).mul
            ((hasDerivAt_id t).pow 2))).add (hasDerivAt_id t) using 1
        simp only [id_eq]
        ring
      have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ht ↦ hderiv t)
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
      rw [hint]
      dsimp only [A]
      norm_num

theorem inv_norm_shiftedLegendreL2_two_sq :
    ‖shiftedLegendreL2 2‖⁻¹ ^ 2 = (5 : ℝ) := by
  rw [inv_pow, norm_sq_shiftedLegendreL2_two]
  norm_num

theorem repr_centeredPullback_zero_eq_coefficient
    (w : ℝ → ℝ)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2) :
    shiftedLegendreHilbertBasis.repr
        (hf.toLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ))) 0 =
      centeredEvenP0Coefficient w := by
  rw [shiftedLegendreHilbertBasis_repr_zero_eq,
    norm_shiftedLegendreL2_zero]
  simp only [inv_one, one_mul]
  rw [integral_unitInterval_eq_intervalIntegral]
  exact integral_comp_two_mul_sub_one w

private theorem repr_centeredPullback_two_eq
    (w : ℝ → ℝ)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2) :
    shiftedLegendreHilbertBasis.repr
        (hf.toLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ))) 2 =
      (1 / 5 : ℝ) * ‖shiftedLegendreL2 2‖⁻¹ *
        centeredEvenP2Coefficient w := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  have hrepr : shiftedLegendreHilbertBasis.repr (hf.toLp f) 2 =
      ‖shiftedLegendreL2 2‖⁻¹ *
        ∫ t : unitInterval, f t * (1 - 6 * (t : ℝ) + 6 * (t : ℝ) ^ 2) := by
    rw [shiftedLegendreHilbertBasis.repr_apply_apply,
      shiftedLegendreHilbertBasis_apply, normalizedShiftedLegendreL2,
      real_inner_smul_left, real_inner_comm, shiftedLegendreL2,
      ← integral_mul_polynomial_eq_inner f hf]
    apply congrArg (fun z : ℝ ↦ ‖shiftedLegendreL2 2‖⁻¹ * z)
    apply integral_congr_ae
    filter_upwards [] with t
    rw [eval_shiftedLegendreReal_two]
  have hint :
      (∫ t : unitInterval, f t *
          (1 - 6 * (t : ℝ) + 6 * (t : ℝ) ^ 2)) =
        (1 / 5 : ℝ) * centeredEvenP2Coefficient w := by
    calc
      _ = ∫ t : ℝ in 0..1,
          centeredPullback w t * (1 - 6 * t + 6 * t ^ 2) :=
        integral_unitInterval_eq_intervalIntegral _
      _ = ∫ t : ℝ in 0..1,
          (fun x : ℝ ↦ w x * centeredEvenP2 x) (2 * t - 1) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        simp only [centeredPullback, centeredEvenP2]
        ring
      _ = (1 / 2 : ℝ) *
          ∫ x : ℝ in -1..1, w x * centeredEvenP2 x :=
        integral_comp_two_mul_sub_one
          (fun x : ℝ ↦ w x * centeredEvenP2 x)
      _ = (1 / 5 : ℝ) * centeredEvenP2Coefficient w := by
        rw [integral_mul_centeredEvenP2_eq]
        ring
  dsimp only [f] at hrepr
  rw [hrepr, hint]
  ring

theorem repr_centeredPullback_two_sq_eq_coefficient
    (w : ℝ → ℝ)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2) :
    (shiftedLegendreHilbertBasis.repr
        (hf.toLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ))) 2) ^ 2 =
      (1 / 5 : ℝ) * centeredEvenP2Coefficient w ^ 2 := by
  rw [repr_centeredPullback_two_eq w hf]
  calc
    ((1 / 5 : ℝ) * ‖shiftedLegendreL2 2‖⁻¹ *
        centeredEvenP2Coefficient w) ^ 2 =
      (1 / 25 : ℝ) * ‖shiftedLegendreL2 2‖⁻¹ ^ 2 *
        centeredEvenP2Coefficient w ^ 2 := by ring
    _ = _ := by
      rw [inv_norm_shiftedLegendreL2_two_sq]
      ring

/-- Exact centered logarithmic reduction to `P₀/P₂` and the complete even
tail.  The tail coefficient `25/12` is `H₄` after the centered affine
normalization. -/
theorem centered_even_zero_two_tail_energy_le
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hweven : Function.Even w) :
    (3 / 5 : ℝ) * centeredEvenP2Coefficient w ^ 2 +
        (25 / 12 : ℝ) *
          (∫ x : ℝ in -1..1, centeredEvenZeroTwoResidual w x ^ 2) ≤
      centeredRawLogEnergy w / 4 := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  let F : UnitIntervalL2 := hf.toLp f
  have hparity : ∀ n : ℕ, Odd n →
      shiftedLegendreHilbertBasis.repr F n = 0 := by
    intro n hn
    dsimp only [F, f]
    exact centeredPullback_repr_eq_zero_of_even_of_odd w hf hweven n hn
  have hspectral := even_zero_two_tail_norm_sq_le_of_partialSpectralEnergy_le
    F hparity (unitIntervalLogEnergy f)
      (fun N ↦ partialSpectralEnergy_le_unitIntervalLogEnergy f hf henergy N)
  have hnorm : ‖F‖ ^ 2 =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x ^ 2 := by
    calc
      ‖F‖ ^ 2 = ∫ t : unitInterval, f t ^ 2 :=
        norm_sq_toLp_eq_integral_sq f hf
      _ = _ := integral_unitInterval_centeredPullback_sq w
  have hzero : (shiftedLegendreHilbertBasis.repr F 0) ^ 2 =
      centeredEvenP0Coefficient w ^ 2 := by
    dsimp only [F, f]
    rw [repr_centeredPullback_zero_eq_coefficient w hf]
  have htwo : (shiftedLegendreHilbertBasis.repr F 2) ^ 2 =
      (1 / 5 : ℝ) * centeredEvenP2Coefficient w ^ 2 := by
    dsimp only [F, f]
    exact repr_centeredPullback_two_sq_eq_coefficient w hf
  have hresidual := integral_centeredEvenZeroTwoResidual_sq w hwcont
  have henergyBridge := unitIntervalLogEnergy_centeredPullback w henergy
  rw [hnorm, hzero, htwo, henergyBridge] at hspectral
  rw [hresidual]
  norm_num at hspectral ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenStructuralReduction
