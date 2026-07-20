import ArithmeticHodge.Analysis.YoshidaEndpointPotentialOddTailGramStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshCoupledCoreStructural

set_option autoImplicit false

open MeasureTheory Real Set Filter
open scoped BigOperators InnerProductSpace unitInterval

namespace ArithmeticHodge.Analysis.YoshidaEndpointPotentialOddTailParsevalStructural

noncomputable section

open ShiftedLegendreCenteredParity
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreL2Basis
open ShiftedLegendreL2SpectralGap
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialLegendreOffDiagonalStructural
open YoshidaEndpointPotentialOddTailGramStructural
open YoshidaFourCellEvenZeroCoshCoupledCoreStructural

/-!
# Parseval realization of the odd endpoint-potential tail Gram

The closed series in
`YoshidaEndpointPotentialOddTailGramStructural` is realized here as the
actual Hilbert Gram of the endpoint-potential projection above an arbitrary
odd cutoff.  The final theorem contracts that Gram against an arbitrary
finite coefficient vector; no retained mode is enumerated.
-/

/-- The centered odd Legendre degree with half-index `i`. -/
def oddLegendreIndex (i : ℕ) : ℕ := 2 * i + 1

/-- The actual unit-interval `L²` class of the endpoint potential multiplied
by the centered odd Legendre mode with half-index `i`. -/
def oddEndpointPotentialLegendreSourceL2 (i : ℕ) : UnitIntervalL2 :=
  cutoffEightPotentialLegendreSourceL2 (oddLegendreIndex i)

private theorem normalized_half_pair_product
    (z A B W : ℝ) (hz : z ^ 2 = W) :
    z * (1 / 2) * (2 / A) * (z * (1 / 2) * (2 / B)) =
      W / (A * B) := by
  have hhalf (C : ℝ) : z * (1 / 2) * (2 / C) = z / C := by
    calc
      z * (1 / 2) * (2 / C) = z / 2 * (2 / C) := by
        simp only [div_eq_mul_inv, one_mul]
      _ = z * 2 / (2 * C) := div_mul_div_comm z 2 2 C
      _ = 2 * z / (2 * C) := by rw [mul_comm z 2]
      _ = z / C := mul_div_mul_left z C (by norm_num : (2 : ℝ) ≠ 0)
  rw [hhalf A, hhalf B, div_mul_div_comm, ← pow_two, hz]

/-- A product of two actual endpoint-potential Hilbert coefficients above an
odd cutoff is exactly the corresponding positive-half Gram summand. -/
theorem repr_mul_repr_oddEndpointPotentialLegendreSourceL2
    (cutoff i j r : ℕ) (hi : i < cutoff) (hj : j < cutoff) :
    shiftedLegendreHilbertBasis.repr
          (oddEndpointPotentialLegendreSourceL2 i)
          (oddLegendreIndex (r + cutoff)) *
        shiftedLegendreHilbertBasis.repr
          (oddEndpointPotentialLegendreSourceL2 j)
          (oddLegendreIndex (r + cutoff)) =
      oddEndpointPotentialTailGramSummand cutoff i j r := by
  have hiHigh : oddLegendreIndex i < oddLegendreIndex (r + cutoff) := by
    unfold oddLegendreIndex
    omega
  have hjHigh : oddLegendreIndex j < oddLegendreIndex (r + cutoff) := by
    unfold oddLegendreIndex
    omega
  have hiEven : Even
      (oddLegendreIndex i + oddLegendreIndex (r + cutoff)) := by
    use i + r + cutoff + 1
    unfold oddLegendreIndex
    omega
  have hjEven : Even
      (oddLegendreIndex j + oddLegendreIndex (r + cutoff)) := by
    use j + r + cutoff + 1
    unfold oddLegendreIndex
    omega
  rw [oddEndpointPotentialLegendreSourceL2,
    oddEndpointPotentialLegendreSourceL2,
    repr_cutoffEightPotentialLegendreSourceL2,
    repr_cutoffEightPotentialLegendreSourceL2,
    integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
      hiHigh hiEven,
    integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
      hjHigh hjEven]
  have hnorm := inv_norm_shiftedLegendreL2_sq_closed
    (oddLegendreIndex (r + cutoff))
  let N : ℝ := oddLegendreDegree (r + cutoff)
  let M : ℝ := oddLegendreDegree i
  let K : ℝ := oddLegendreDegree j
  let z : ℝ := ‖shiftedLegendreL2
    (oddLegendreIndex (r + cutoff))‖⁻¹
  let A : ℝ := (N - M) * (N + M + 1)
  let B : ℝ := (N - K) * (N + K + 1)
  have hindex (a : ℕ) :
      ((oddLegendreIndex a : ℕ) : ℝ) = oddLegendreDegree a := by
    unfold oddLegendreIndex oddLegendreDegree
    push_cast
    rfl
  have hnormz : z ^ 2 = 2 * N + 1 := by
    simpa only [z, N, oddLegendreIndex, oddLegendreDegree,
      Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using hnorm
  unfold oddEndpointPotentialTailGramSummand
  simp_rw [hindex]
  change z * (1 / 2) * (2 / A) * (z * (1 / 2) * (2 / B)) =
    (2 * N + 1) /
      ((N - M) * (N + M + 1) * (N - K) * (N + K + 1))
  calc
    _ = (2 * N + 1) / (A * B) :=
      normalized_half_pair_product z A B (2 * N + 1) hnormz
    _ = _ := by simp only [A, B, mul_assoc]

/-- Hilbert coefficient of a finite shifted-Legendre projection. -/
theorem repr_shiftedLegendrePartialProjection
    (F : UnitIntervalL2) (N n : ℕ) :
    shiftedLegendreHilbertBasis.repr
        (shiftedLegendrePartialProjection F N) n =
      if n < N then shiftedLegendreHilbertBasis.repr F n else 0 := by
  rw [shiftedLegendreHilbertBasis.repr_apply_apply]
  unfold shiftedLegendrePartialProjection
  rw [inner_sum]
  by_cases hn : n < N
  · rw [if_pos hn]
    have hnmem : n ∈ Finset.range N := Finset.mem_range.mpr hn
    rw [Finset.sum_eq_single n]
    · rw [inner_smul_right,
        (orthonormal_iff_ite.mp
          shiftedLegendreHilbertBasis.orthonormal n n)]
      simp
    · intro b hb hbn
      rw [inner_smul_right,
        (orthonormal_iff_ite.mp
          shiftedLegendreHilbertBasis.orthonormal n b),
        if_neg (Ne.symm hbn)]
      simp
    · exact fun hnnot ↦ (hnnot hnmem).elim
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro b hb
    rw [inner_smul_right,
      (orthonormal_iff_ite.mp
        shiftedLegendreHilbertBasis.orthonormal n b)]
    rw [if_neg]
    · simp
    · intro hnb
      subst b
      exact hn (Finset.mem_range.mp hb)

/-- The actual endpoint-potential source after removing every Hilbert degree
strictly below the first omitted odd degree. -/
def oddEndpointPotentialLegendreTailL2
    (cutoff i : ℕ) : UnitIntervalL2 :=
  oddEndpointPotentialLegendreSourceL2 i -
    shiftedLegendrePartialProjection
      (oddEndpointPotentialLegendreSourceL2 i)
      (oddLegendreIndex cutoff)

theorem repr_oddEndpointPotentialLegendreTailL2
    (cutoff i n : ℕ) :
    shiftedLegendreHilbertBasis.repr
        (oddEndpointPotentialLegendreTailL2 cutoff i) n =
      if n < oddLegendreIndex cutoff then 0
      else shiftedLegendreHilbertBasis.repr
        (oddEndpointPotentialLegendreSourceL2 i) n := by
  unfold oddEndpointPotentialLegendreTailL2
  rw [shiftedLegendreHilbertBasis.repr_apply_apply, inner_sub_right,
    ← shiftedLegendreHilbertBasis.repr_apply_apply,
    ← shiftedLegendreHilbertBasis.repr_apply_apply,
    repr_shiftedLegendrePartialProjection]
  by_cases hn : n < oddLegendreIndex cutoff <;> simp [hn]

/-- An odd endpoint-potential source has no even Hilbert coefficients. -/
theorem repr_oddEndpointPotentialLegendreSourceL2_eq_zero_of_even
    (i n : ℕ) (hn : Even n) :
    shiftedLegendreHilbertBasis.repr
        (oddEndpointPotentialLegendreSourceL2 i) n = 0 := by
  rw [oddEndpointPotentialLegendreSourceL2,
    repr_cutoffEightPotentialLegendreSourceL2]
  rcases hn with ⟨u, hu⟩
  have hne : oddLegendreIndex i ≠ n := by
    intro heq
    unfold oddLegendreIndex at heq
    omega
  have hodd : Odd (oddLegendreIndex i + n) := by
    use i + u
    unfold oddLegendreIndex
    omega
  have hpair :
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x *
          (centeredShiftedLegendreReal (oddLegendreIndex i)).eval x *
          (centeredShiftedLegendreReal n).eval x) = 0 := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact
        integral_endpointPotential_mul_centeredShiftedLegendreReal_of_odd
          hlt hodd
    · have hodd' : Odd (n + oddLegendreIndex i) := by
        use i + u
        unfold oddLegendreIndex
        omega
      have h :=
        integral_endpointPotential_mul_centeredShiftedLegendreReal_of_odd
          hgt hodd'
      calc
        (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x *
            (centeredShiftedLegendreReal (oddLegendreIndex i)).eval x *
            (centeredShiftedLegendreReal n).eval x) =
            ∫ x : ℝ in -1..1,
              yoshidaEndpointPotential x *
                (centeredShiftedLegendreReal n).eval x *
                (centeredShiftedLegendreReal (oddLegendreIndex i)).eval x := by
          apply intervalIntegral.integral_congr
          intro x _hx
          ring
        _ = 0 := h
  rw [hpair, mul_zero]

/-- The odd tail residual likewise has no even Hilbert coefficients. -/
theorem repr_oddEndpointPotentialLegendreTailL2_eq_zero_of_even
    (cutoff i n : ℕ) (hn : Even n) :
    shiftedLegendreHilbertBasis.repr
        (oddEndpointPotentialLegendreTailL2 cutoff i) n = 0 := by
  rw [repr_oddEndpointPotentialLegendreTailL2]
  split_ifs
  · rfl
  · exact repr_oddEndpointPotentialLegendreSourceL2_eq_zero_of_even i n hn

/-- The closed scalar tail series is the actual Hilbert inner product of two
projected odd endpoint-potential sources. -/
theorem inner_oddEndpointPotentialLegendreTailL2_eq_gramValue
    (cutoff i j : ℕ) (hi : i < cutoff) (hj : j < cutoff) :
    inner ℝ (oddEndpointPotentialLegendreTailL2 cutoff i)
        (oddEndpointPotentialLegendreTailL2 cutoff j) =
      oddEndpointPotentialTailGramValue cutoff i j := by
  let a : ℕ → ℝ := fun n ↦
    shiftedLegendreHilbertBasis.repr
        (oddEndpointPotentialLegendreTailL2 cutoff i) n *
      shiftedLegendreHilbertBasis.repr
        (oddEndpointPotentialLegendreTailL2 cutoff j) n
  have hseries := hasSum_oddEndpointPotentialTailGram cutoff i j hi hj
  have hshift : HasSum
      (fun r : ℕ ↦ a (oddLegendreIndex (r + cutoff)))
      (oddEndpointPotentialTailGramValue cutoff i j) := by
    convert hseries using 1
    funext r
    dsimp only [a]
    have hhigh : ¬ oddLegendreIndex (r + cutoff) <
        oddLegendreIndex cutoff := by
      unfold oddLegendreIndex
      omega
    rw [repr_oddEndpointPotentialLegendreTailL2,
      if_neg hhigh,
      repr_oddEndpointPotentialLegendreTailL2,
      if_neg hhigh]
    exact repr_mul_repr_oddEndpointPotentialLegendreSourceL2
      cutoff i j r hi hj
  have hprefix :
      (∑ s ∈ Finset.range cutoff, a (oddLegendreIndex s)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have hlow : oddLegendreIndex s < oddLegendreIndex cutoff := by
      have hslt := Finset.mem_range.mp hs
      unfold oddLegendreIndex
      omega
    dsimp only [a]
    rw [repr_oddEndpointPotentialLegendreTailL2,
      if_pos hlow, zero_mul]
  have hodd : HasSum (fun s : ℕ ↦ a (oddLegendreIndex s))
      (oddEndpointPotentialTailGramValue cutoff i j) := by
    apply (hasSum_nat_add_iff' cutoff).1
    rw [hprefix, sub_zero]
    exact hshift
  have heven : HasSum (fun s : ℕ ↦ a (2 * s)) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0) using 1
    funext s
    dsimp only [a]
    rw [repr_oddEndpointPotentialLegendreTailL2_eq_zero_of_even
      cutoff i (2 * s) (by use s; omega), zero_mul]
  have hall : HasSum a
      (oddEndpointPotentialTailGramValue cutoff i j) := by
    simpa only [oddLegendreIndex, zero_add] using heven.even_add_odd hodd
  have hb := shiftedLegendreHilbertBasis.hasSum_inner_mul_inner
    (oddEndpointPotentialLegendreTailL2 cutoff i)
    (oddEndpointPotentialLegendreTailL2 cutoff j)
  have hb' : HasSum a
      (inner ℝ (oddEndpointPotentialLegendreTailL2 cutoff i)
        (oddEndpointPotentialLegendreTailL2 cutoff j)) := by
    convert hb using 1
    funext n
    dsimp only [a]
    rw [shiftedLegendreHilbertBasis.repr_apply_apply,
      shiftedLegendreHilbertBasis.repr_apply_apply,
      real_inner_comm (oddEndpointPotentialLegendreTailL2 cutoff i)]
  exact hb'.unique hall

/-! ## Finite odd profiles -/

/-- Actual endpoint-potential source of a finite odd Legendre profile. -/
def oddEndpointPotentialFiniteProfileSourceL2
    (cutoff : ℕ) (c : Fin cutoff → ℝ) : UnitIntervalL2 :=
  ∑ i : Fin cutoff, c i • oddEndpointPotentialLegendreSourceL2 i

/-- Its endpoint-potential projection onto all odd degrees at or above the
first omitted mode `P_(2*cutoff+1)`. -/
def oddEndpointPotentialFiniteProfileTailL2
    (cutoff : ℕ) (c : Fin cutoff → ℝ) : UnitIntervalL2 :=
  ∑ i : Fin cutoff, c i • oddEndpointPotentialLegendreTailL2 cutoff i

/-- Closed contraction of the odd endpoint-potential tail Gram against an
arbitrary finite coefficient vector. -/
def oddEndpointPotentialTailGramContraction
    (cutoff : ℕ) (c : Fin cutoff → ℝ) : ℝ :=
  ∑ i : Fin cutoff, ∑ j : Fin cutoff,
    c i * c j * oddEndpointPotentialTailGramValue cutoff i j

/-- The squared norm of the genuine finite-profile endpoint-potential tail
is exactly the closed Gram contraction. -/
theorem norm_sq_oddEndpointPotentialFiniteProfileTailL2_eq_contraction
    (cutoff : ℕ) (c : Fin cutoff → ℝ) :
    ‖oddEndpointPotentialFiniteProfileTailL2 cutoff c‖ ^ 2 =
      oddEndpointPotentialTailGramContraction cutoff c := by
  rw [← real_inner_self_eq_norm_sq]
  unfold oddEndpointPotentialFiniteProfileTailL2
    oddEndpointPotentialTailGramContraction
  simp only [sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [real_inner_comm (oddEndpointPotentialLegendreTailL2 cutoff i)
      (oddEndpointPotentialLegendreTailL2 cutoff j),
    inner_oddEndpointPotentialLegendreTailL2_eq_gramValue
    cutoff i j i.isLt j.isLt]
  ring

/-- The P53+ endpoint-potential tail of an arbitrary odd profile through
`P51`, represented by its 26 Legendre coefficients. -/
def oddEndpointPotentialP53PlusL2 (c : Fin 26 → ℝ) : UnitIntervalL2 :=
  oddEndpointPotentialFiniteProfileTailL2 26 c

/-- Closed scalar Gram contraction for the same P53+ tail. -/
def oddEndpointPotentialP53PlusGram (c : Fin 26 → ℝ) : ℝ :=
  oddEndpointPotentialTailGramContraction 26 c

theorem norm_sq_oddEndpointPotentialP53PlusL2_eq_gram
    (c : Fin 26 → ℝ) :
    ‖oddEndpointPotentialP53PlusL2 c‖ ^ 2 =
      oddEndpointPotentialP53PlusGram c := by
  exact norm_sq_oddEndpointPotentialFiniteProfileTailL2_eq_contraction 26 c

end

end ArithmeticHodge.Analysis.YoshidaEndpointPotentialOddTailParsevalStructural
