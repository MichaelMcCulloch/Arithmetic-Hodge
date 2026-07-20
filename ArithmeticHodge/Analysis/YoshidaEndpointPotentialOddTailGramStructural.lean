import ArithmeticHodge.Analysis.YoshidaEndpointPotentialLegendreOffDiagonalStructural
import Mathlib.NumberTheory.ZetaValues

set_option autoImplicit false

open Real Set Filter
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaEndpointPotentialOddTailGramStructural

noncomputable section

/-!
# Closed odd endpoint-potential tail Gram

The endpoint potential sends a centered Legendre source of degree `m` to
degree `n > m` with positive-half coefficient

`1 / (n(n+1) - m(m+1))`.

This file sums the resulting odd tail Gram structurally.  Off-diagonal
entries are finite stride-two telescopes; diagonal entries are differences
of shifted even and odd reciprocal-square tails.
-/

/-- The one-step stride-two reciprocal telescope. -/
theorem hasSum_strideTwo_reciprocalDifference
    (a : ℝ) (ha : 0 < a) :
    HasSum (fun r : ℕ ↦
      1 / (2 * (r : ℝ) + a) -
        1 / (2 * (r : ℝ) + a + 2)) (1 / a) := by
  have hnonneg : ∀ r : ℕ,
      0 ≤ 1 / (2 * (r : ℝ) + a) -
        1 / (2 * (r : ℝ) + a + 2) := by
    intro r
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg (1 / a)).2
  have hsum (n : ℕ) :
      (∑ r ∈ Finset.range n,
        (1 / (2 * (r : ℝ) + a) -
          1 / (2 * (r : ℝ) + a + 2))) =
        1 / a - 1 / (2 * (n : ℝ) + a) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  simp_rw [hsum]
  have hmul : Tendsto (fun n : ℕ ↦ 2 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ) < 2)
  have hden : Tendsto (fun n : ℕ ↦ 2 * (n : ℝ) + a) atTop atTop :=
    hmul.atTop_add tendsto_const_nhds
  have hinv : Tendsto (fun n : ℕ ↦
      1 / (2 * (n : ℝ) + a)) atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hden
  simpa using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ 1 / a)
      atTop (nhds (1 / a))).sub hinv)

/-- A finite stride-two displacement telescopes to the finite initial
reciprocal block. -/
theorem hasSum_strideTwo_reciprocalDifference_natShift
    (a : ℝ) (ha : 0 < a) (d : ℕ) :
    HasSum (fun r : ℕ ↦
      1 / (2 * (r : ℝ) + a) -
        1 / (2 * (r : ℝ) + a + 2 * d))
      (∑ s ∈ Finset.range d, 1 / (2 * (s : ℝ) + a)) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have ha' : 0 < a + 2 * (d : ℝ) := by positivity
      have hstep := hasSum_strideTwo_reciprocalDifference
        (a + 2 * (d : ℝ)) ha'
      have h := ih.add hstep
      convert h using 1
      · funext r
        push_cast
        ring
      · rw [Finset.sum_range_succ]
        ring

/-- Reciprocal squares on the even nonnegative integers.  The zero term is
zero under the field convention, so this is one quarter of `ζ(2)`. -/
theorem hasSum_even_reciprocalSquares :
    HasSum (fun r : ℕ ↦ 1 / (2 * (r : ℝ)) ^ 2)
      (Real.pi ^ 2 / 24) := by
  have h := HasSum.mul_left (1 / 4 : ℝ) hasSum_zeta_two
  convert h using 1
  · funext r
    rw [mul_pow]
    ring
  · ring

/-- Reciprocal squares on the positive odd integers. -/
theorem hasSum_odd_reciprocalSquares :
    HasSum (fun r : ℕ ↦ 1 / (2 * (r : ℝ) + 1) ^ 2)
      (Real.pi ^ 2 / 8) := by
  let f : ℕ → ℝ := fun n ↦ 1 / (n : ℝ) ^ 2
  have hz : Summable f := by
    simpa only [f] using hasSum_zeta_two.summable
  have he : Summable (fun r : ℕ ↦ f (2 * r)) :=
    hz.comp_injective (by
      intro a b h
      exact Nat.mul_left_cancel (by norm_num) h)
  have ho : Summable (fun r : ℕ ↦ f (2 * r + 1)) :=
    hz.comp_injective (by
      intro a b h
      exact Nat.mul_left_cancel (by norm_num) (Nat.add_right_cancel h))
  have hsplit := tsum_even_add_odd he ho
  have hEvenTsum : (∑' r : ℕ, f (2 * r)) = Real.pi ^ 2 / 24 := by
    simpa only [f, Nat.cast_mul, Nat.cast_ofNat] using
      hasSum_even_reciprocalSquares.tsum_eq
  have hZetaTsum : (∑' n : ℕ, f n) = Real.pi ^ 2 / 6 := by
    simpa only [f] using hasSum_zeta_two.tsum_eq
  have hOddTsum : (∑' r : ℕ, f (2 * r + 1)) = Real.pi ^ 2 / 8 := by
    rw [hEvenTsum, hZetaTsum] at hsplit
    linarith
  simpa only [f, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] using (ho.hasSum_iff).2 hOddTsum

/-- Closed shifted even reciprocal-square tail. -/
def evenReciprocalSquareTail (a : ℕ) : ℝ :=
  Real.pi ^ 2 / 24 -
    ∑ r ∈ Finset.range a, 1 / (2 * (r : ℝ)) ^ 2

/-- Closed shifted odd reciprocal-square tail. -/
def oddReciprocalSquareTail (a : ℕ) : ℝ :=
  Real.pi ^ 2 / 8 -
    ∑ r ∈ Finset.range a, 1 / (2 * (r : ℝ) + 1) ^ 2

theorem hasSum_even_reciprocalSquares_natAdd (a : ℕ) :
    HasSum (fun r : ℕ ↦ 1 / (2 * ((r + a : ℕ) : ℝ)) ^ 2)
      (evenReciprocalSquareTail a) := by
  simpa only [evenReciprocalSquareTail, Nat.cast_add,
    mul_add] using (hasSum_nat_add_iff' a).2 hasSum_even_reciprocalSquares

theorem hasSum_odd_reciprocalSquares_natAdd (a : ℕ) :
    HasSum (fun r : ℕ ↦
      1 / (2 * ((r + a : ℕ) : ℝ) + 1) ^ 2)
      (oddReciprocalSquareTail a) := by
  simpa only [oddReciprocalSquareTail, Nat.cast_add,
    mul_add] using (hasSum_nat_add_iff' a).2 hasSum_odd_reciprocalSquares

/-! ## Odd Legendre tail Gram -/

/-- Odd centered Legendre degree with half-index `i`. -/
def oddLegendreDegree (i : ℕ) : ℝ := 2 * (i : ℝ) + 1

/-- Positive-half endpoint-potential tail Gram summand.  The first omitted
odd degree has half-index `cutoff`; thus `cutoff = 26` is the `P53+` tail. -/
def oddEndpointPotentialTailGramSummand
    (cutoff i j r : ℕ) : ℝ :=
  let n := oddLegendreDegree (r + cutoff)
  let m := oddLegendreDegree i
  let k := oddLegendreDegree j
  (2 * n + 1) /
    ((n - m) * (n + m + 1) *
      (n - k) * (n + k + 1))

/-- Closed diagonal odd tail-Gram value for a source with half-index `i`
and a first omitted half-index `i + gap`. -/
def oddEndpointPotentialDiagonalTailValue (i gap : ℕ) : ℝ :=
  (1 / (4 * (i : ℝ) + 3)) *
    (evenReciprocalSquareTail gap -
      oddReciprocalSquareTail (2 * i + gap + 1))

/-- Closed off-diagonal odd tail-Gram value.  The two source half-indices
are `i` and `i + separation`, and the first omitted half-index is
`i + separation + gap`. -/
def oddEndpointPotentialOffDiagonalTailValue
    (i separation gap : ℕ) : ℝ :=
  let evenBlock := ∑ s ∈ Finset.range separation,
    1 / (2 * (s : ℝ) + 2 * gap)
  let oddBlock := ∑ s ∈ Finset.range separation,
    1 / (2 * (s : ℝ) +
      (2 * (2 * i + separation + gap + 1) + 1 : ℕ))
  (1 /
      ((2 * separation : ℕ) *
        (2 * (2 * i + separation) + 3) : ℕ)) *
    (evenBlock - oddBlock)

private theorem endpointPotentialDiagonalPartialFraction
    (n m : ℝ) (hm : 2 * m + 1 ≠ 0)
    (hlo : n - m ≠ 0) (hhi : n + m + 1 ≠ 0) :
    (2 * n + 1) /
        ((n - m) * (n + m + 1) * (n - m) * (n + m + 1)) =
      (1 / (2 * m + 1)) *
        (1 / (n - m) ^ 2 - 1 / (n + m + 1) ^ 2) := by
  field_simp [hm, hlo, hhi]
  ring

private theorem endpointPotentialOffDiagonalPartialFraction
    (n m k : ℝ)
    (hgap : k * (k + 1) - m * (m + 1) ≠ 0)
    (hnm0 : n - m ≠ 0) (hnm1 : n + m + 1 ≠ 0)
    (hnk0 : n - k ≠ 0) (hnk1 : n + k + 1 ≠ 0) :
    (2 * n + 1) /
        ((n - m) * (n + m + 1) * (n - k) * (n + k + 1)) =
      (1 / (k * (k + 1) - m * (m + 1))) *
        ((1 / (n - k) - 1 / (n - m)) -
          (1 / (n + m + 1) - 1 / (n + k + 1))) := by
  field_simp [hgap, hnm0, hnm1, hnk0, hnk1]
  ring

/-- Generic diagonal `HasSum` for every odd source strictly below the odd
cutoff. -/
theorem hasSum_oddEndpointPotentialTailGram_diagonal
    (i gap : ℕ) (hgap : 0 < gap) :
    HasSum
      (oddEndpointPotentialTailGramSummand (i + gap) i i)
      (oddEndpointPotentialDiagonalTailValue i gap) := by
  have he := hasSum_even_reciprocalSquares_natAdd gap
  have ho := hasSum_odd_reciprocalSquares_natAdd (2 * i + gap + 1)
  have hgapR : 0 < (gap : ℝ) := by exact_mod_cast hgap
  have h := HasSum.mul_left (1 / (4 * (i : ℝ) + 3)) (he.sub ho)
  convert h using 1
  · funext r
    have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    unfold oddEndpointPotentialTailGramSummand oddLegendreDegree
    rw [endpointPotentialDiagonalPartialFraction]
    · push_cast
      congr 1
      · ring
      · congr 1 <;> ring
    · positivity
    · push_cast
      nlinarith
    · push_cast
      positivity

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
/-- Generic off-diagonal `HasSum` for two odd sources strictly below the
odd cutoff. -/
theorem hasSum_oddEndpointPotentialTailGram_offDiagonal
    (i separation gap : ℕ)
    (hseparation : 0 < separation) (hgap : 0 < gap) :
    HasSum
      (oddEndpointPotentialTailGramSummand
        (i + separation + gap) i (i + separation))
      (oddEndpointPotentialOffDiagonalTailValue i separation gap) := by
  have he := hasSum_strideTwo_reciprocalDifference_natShift
    (2 * (gap : ℝ)) (by positivity) separation
  have ho := hasSum_strideTwo_reciprocalDifference_natShift
    (2 * (2 * (i : ℝ) + separation + gap + 1) + 1)
    (by positivity) separation
  let D : ℝ :=
    (2 * (separation : ℝ)) *
      (2 * (2 * (i : ℝ) + separation) + 3)
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have h := HasSum.mul_left (1 / D) (he.sub ho)
  convert h using 1
  · funext r
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    have hs : 0 < (separation : ℝ) := by exact_mod_cast hseparation
    have hg : 0 < (gap : ℝ) := by exact_mod_cast hgap
    unfold oddEndpointPotentialTailGramSummand oddLegendreDegree
    dsimp only [D]
    rw [endpointPotentialOffDiagonalPartialFraction]
    · push_cast
      congr 1
      · ring
      · apply congrArg₂ (fun x y : ℝ ↦ x - y)
        · apply congrArg₂ (fun x y : ℝ ↦ x - y) <;> congr 1 <;> ring
        · apply congrArg₂ (fun x y : ℝ ↦ x - y) <;> congr 1 <;> ring
    · push_cast
      nlinarith
    · push_cast
      nlinarith
    · push_cast
      positivity
    · push_cast
      nlinarith
    · push_cast
      positivity
  · unfold oddEndpointPotentialOffDiagonalTailValue
    dsimp only [D]
    push_cast
    congr 1

/-- The tail Gram summand is symmetric in its two source modes. -/
theorem oddEndpointPotentialTailGramSummand_comm
    (cutoff i j r : ℕ) :
    oddEndpointPotentialTailGramSummand cutoff i j r =
      oddEndpointPotentialTailGramSummand cutoff j i r := by
  unfold oddEndpointPotentialTailGramSummand
  ring

/-- Diagonal closed tail Gram at an arbitrary cutoff strictly above the
source half-index. -/
theorem hasSum_oddEndpointPotentialTailGram_diagonal_cutoff
    (cutoff i : ℕ) (hi : i < cutoff) :
    HasSum
      (oddEndpointPotentialTailGramSummand cutoff i i)
      (oddEndpointPotentialDiagonalTailValue i (cutoff - i)) := by
  have h := hasSum_oddEndpointPotentialTailGram_diagonal
    i (cutoff - i) (Nat.sub_pos_of_lt hi)
  simpa only [Nat.add_sub_of_le hi.le] using h

/-- Off-diagonal closed tail Gram at an arbitrary cutoff strictly above two
ordered source half-indices. -/
theorem hasSum_oddEndpointPotentialTailGram_offDiagonal_cutoff
    (cutoff i j : ℕ) (hij : i < j) (hj : j < cutoff) :
    HasSum
      (oddEndpointPotentialTailGramSummand cutoff i j)
      (oddEndpointPotentialOffDiagonalTailValue
        i (j - i) (cutoff - j)) := by
  have h := hasSum_oddEndpointPotentialTailGram_offDiagonal
    i (j - i) (cutoff - j)
      (Nat.sub_pos_of_lt hij) (Nat.sub_pos_of_lt hj)
  simpa only [Nat.add_sub_of_le hij.le, Nat.add_sub_of_le hj.le] using h

/-- Closed odd endpoint-potential tail Gram at an arbitrary cutoff.  The
piecewise expression is diagonal when the sources agree and otherwise uses
the ordered off-diagonal telescope. -/
def oddEndpointPotentialTailGramValue
    (cutoff i j : ℕ) : ℝ :=
  if i = j then
    oddEndpointPotentialDiagonalTailValue i (cutoff - i)
  else
    oddEndpointPotentialOffDiagonalTailValue
      (min i j) (max i j - min i j) (cutoff - max i j)

/-- Every odd endpoint-potential tail Gram strictly above its two source
modes has the closed value `oddEndpointPotentialTailGramValue`.  This theorem
contains no coefficient vector and no enumeration of the retained modes. -/
theorem hasSum_oddEndpointPotentialTailGram
    (cutoff i j : ℕ) (hi : i < cutoff) (hj : j < cutoff) :
    HasSum
      (oddEndpointPotentialTailGramSummand cutoff i j)
      (oddEndpointPotentialTailGramValue cutoff i j) := by
  by_cases heq : i = j
  · subst j
    simpa only [oddEndpointPotentialTailGramValue, if_pos rfl] using
      hasSum_oddEndpointPotentialTailGram_diagonal_cutoff cutoff i hi
  · rcases lt_or_gt_of_ne heq with hij | hji
    · simpa only [oddEndpointPotentialTailGramValue, if_neg heq,
        Nat.min_eq_left hij.le, Nat.max_eq_right hij.le] using
        hasSum_oddEndpointPotentialTailGram_offDiagonal_cutoff
          cutoff i j hij hj
    · have hsum :=
        hasSum_oddEndpointPotentialTailGram_offDiagonal_cutoff
          cutoff j i hji hi
      have hsum' :
          HasSum
            (oddEndpointPotentialTailGramSummand cutoff i j)
            (oddEndpointPotentialOffDiagonalTailValue
              j (i - j) (cutoff - i)) := by
        convert hsum using 1
        funext r
        exact oddEndpointPotentialTailGramSummand_comm cutoff i j r
      simpa only [oddEndpointPotentialTailGramValue, if_neg heq,
        Nat.min_eq_right hji.le, Nat.max_eq_left hji.le] using hsum'

end

end ArithmeticHodge.Analysis.YoshidaEndpointPotentialOddTailGramStructural
