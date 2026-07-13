import ArithmeticHodge.Analysis.ShiftedLegendreL2HigherGap

set_option autoImplicit false

open Finset Filter
open scoped BigOperators Topology

namespace ArithmeticHodge.Analysis.ShiftedLegendreOddOneThreeTail

open ShiftedLegendreL2Basis
open ShiftedLegendreL2HigherGap
open ShiftedLegendreL2SpectralGap

noncomputable section

/-!
# Exact first and third odd modes with a uniform odd tail

The first and third odd shifted-Legendre modes retain their exact logarithmic
eigenvalues.  Every remaining odd mode begins at degree five and is bounded
uniformly by `2 * H₅ = 137 / 30`.  The complete statement follows from
finite spectral sums and Hilbert-basis norm convergence.
-/

/-- The exact logarithmic weights on degrees one and three, followed by the
uniform degree-five tail weight. -/
def oddOneThreeTailWeight (n : ℕ) : ℝ :=
  if n = 1 then 2 else if n = 3 then 11 / 3 else 137 / 30

/-- Every coefficient satisfies the retained-low-mode/tail lower bound.  On
even degrees this is parity cancellation; on all other degrees except one and
three, oddness forces the degree to be at least five. -/
theorem oddOneThreeTailWeight_mul_repr_sq_le
    (F : UnitIntervalL2)
    (hparity : ∀ n : ℕ, Even n →
      shiftedLegendreHilbertBasis.repr F n = 0)
    (n : ℕ) :
    oddOneThreeTailWeight n *
        (shiftedLegendreHilbertBasis.repr F n) ^ 2 ≤
      (2 * (harmonic n : ℝ)) *
        (shiftedLegendreHilbertBasis.repr F n) ^ 2 := by
  by_cases heven : Even n
  · rw [hparity n heven]
    simp
  · by_cases hn1 : n = 1
    · subst n
      norm_num [oddOneThreeTailWeight, harmonic, Finset.sum_range_succ]
    · by_cases hn3 : n = 3
      · subst n
        norm_num [oddOneThreeTailWeight, harmonic, Finset.sum_range_succ]
      · have hnodd : Odd n := Nat.not_even_iff_odd.mp heven
        have hn5 : 5 ≤ n := by
          rcases hnodd with ⟨k, hk⟩
          omega
        have hH : (137 / 30 : ℝ) ≤ 2 * (harmonic n : ℝ) := by
          have hmono := harmonic_cast_mono hn5
          norm_num [harmonic, Finset.sum_range_succ] at hmono ⊢
          linarith
        rw [oddOneThreeTailWeight, if_neg hn1, if_neg hn3]
        exact mul_le_mul_of_nonneg_right hH (sq_nonneg _)

/-- The retained exact modes and the uniform tail bound hold on every finite
spectral projection. -/
theorem oddOneThreeTail_partialWeight_le_partialSpectralEnergy
    (F : UnitIntervalL2)
    (hparity : ∀ n : ℕ, Even n →
      shiftedLegendreHilbertBasis.repr F n = 0)
    (N : ℕ) :
    (∑ n ∈ Finset.range N,
        oddOneThreeTailWeight n *
          (shiftedLegendreHilbertBasis.repr F n) ^ 2) ≤
      shiftedLegendrePartialSpectralEnergy F N := by
  rw [shiftedLegendrePartialSpectralEnergy]
  apply Finset.sum_le_sum
  intro n _hn
  exact oddOneThreeTailWeight_mul_repr_sq_le F hparity n

/-- Once the first four indices lie in the finite projection, its weighted
sum is the exact degree-one and degree-three contribution plus the uniform
degree-five tail applied to the remaining partial norm. -/
theorem oddOneThreeTail_partialWeight_eq
    (F : UnitIntervalL2) (N : ℕ) (hN : 4 ≤ N) :
    (∑ n ∈ Finset.range N,
        oddOneThreeTailWeight n *
          (shiftedLegendreHilbertBasis.repr F n) ^ 2) =
      2 * (shiftedLegendreHilbertBasis.repr F 1) ^ 2 +
        (11 / 3 : ℝ) * (shiftedLegendreHilbertBasis.repr F 3) ^ 2 +
        (137 / 30 : ℝ) *
          (shiftedLegendrePartialNormSq F N -
            (shiftedLegendreHilbertBasis.repr F 1) ^ 2 -
            (shiftedLegendreHilbertBasis.repr F 3) ^ 2) := by
  have h1 : 1 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  have h3 : 3 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  rw [shiftedLegendrePartialNormSq]
  calc
    (∑ n ∈ Finset.range N,
        oddOneThreeTailWeight n *
          (shiftedLegendreHilbertBasis.repr F n) ^ 2) =
        ∑ n ∈ Finset.range N,
          ((137 / 30 : ℝ) *
              (shiftedLegendreHilbertBasis.repr F n) ^ 2 +
            (if n = 1 then
              (2 - 137 / 30 : ℝ) *
                (shiftedLegendreHilbertBasis.repr F n) ^ 2 else 0) +
            (if n = 3 then
              (11 / 3 - 137 / 30 : ℝ) *
                (shiftedLegendreHilbertBasis.repr F n) ^ 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro n _hn
      by_cases hn1 : n = 1
      · subst n
        simp [oddOneThreeTailWeight]
        ring
      · by_cases hn3 : n = 3
        · subst n
          simp [oddOneThreeTailWeight]
          ring
        · simp [oddOneThreeTailWeight, hn1, hn3]
    _ = (137 / 30 : ℝ) *
          ∑ n ∈ Finset.range N,
            (shiftedLegendreHilbertBasis.repr F n) ^ 2 +
        (2 - 137 / 30 : ℝ) *
          (shiftedLegendreHilbertBasis.repr F 1) ^ 2 +
        (11 / 3 - 137 / 30 : ℝ) *
          (shiftedLegendreHilbertBasis.repr F 3) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      simp [h1, h3]
    _ = _ := by ring

theorem odd_one_three_tail_norm_sq_le_of_partialSpectralEnergy_le
    (F : UnitIntervalL2)
    (hparity : ∀ n : ℕ, Even n →
      shiftedLegendreHilbertBasis.repr F n = 0)
    (Q : ℝ)
    (hQ : ∀ N : ℕ, shiftedLegendrePartialSpectralEnergy F N ≤ Q) :
    2 * (shiftedLegendreHilbertBasis.repr F 1) ^ 2 +
        (11 / 3 : ℝ) * (shiftedLegendreHilbertBasis.repr F 3) ^ 2 +
        (137 / 30 : ℝ) *
          (‖F‖ ^ 2 - (shiftedLegendreHilbertBasis.repr F 1) ^ 2 -
            (shiftedLegendreHilbertBasis.repr F 3) ^ 2) ≤ Q := by
  let lower : ℕ → ℝ := fun N ↦
    2 * (shiftedLegendreHilbertBasis.repr F 1) ^ 2 +
      (11 / 3 : ℝ) * (shiftedLegendreHilbertBasis.repr F 3) ^ 2 +
      (137 / 30 : ℝ) *
        (shiftedLegendrePartialNormSq F N -
          (shiftedLegendreHilbertBasis.repr F 1) ^ 2 -
          (shiftedLegendreHilbertBasis.repr F 3) ^ 2)
  have hlower : Filter.Tendsto lower Filter.atTop
      (nhds
        (2 * (shiftedLegendreHilbertBasis.repr F 1) ^ 2 +
          (11 / 3 : ℝ) * (shiftedLegendreHilbertBasis.repr F 3) ^ 2 +
          (137 / 30 : ℝ) *
            (‖F‖ ^ 2 - (shiftedLegendreHilbertBasis.repr F 1) ^ 2 -
              (shiftedLegendreHilbertBasis.repr F 3) ^ 2))) := by
    dsimp only [lower]
    exact tendsto_const_nhds.add
      ((((tendsto_shiftedLegendrePartialNormSq F).sub tendsto_const_nhds).sub
        tendsto_const_nhds).const_mul (137 / 30 : ℝ))
  apply le_of_tendsto hlower
  filter_upwards [Filter.eventually_ge_atTop 4] with N hN
  dsimp only [lower]
  rw [← oddOneThreeTail_partialWeight_eq F N hN]
  exact (oddOneThreeTail_partialWeight_le_partialSpectralEnergy F hparity N).trans
    (hQ N)

end

end ArithmeticHodge.Analysis.ShiftedLegendreOddOneThreeTail
