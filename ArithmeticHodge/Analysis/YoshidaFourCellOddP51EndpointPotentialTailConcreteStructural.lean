import ArithmeticHodge.Analysis.YoshidaEndpointPotentialOddTailParsevalStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP51GalerkinRieszStructural

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators InnerProductSpace unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51EndpointPotentialTailConcreteStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreCenteredParity
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open ShiftedLegendreL2SpectralGap
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaEndpointOcticPotential
open YoshidaEndpointPotentialOddTailParsevalStructural
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFactorTwoPhaseHigherLegendreDecomposition

/-!
# Concrete endpoint-potential tail at the exact P51 solve

The production odd Legendre coordinates use the sign convention
`centeredP1 = -P1` and `fourCellOddFiniteRetainedBasis i = -P_(2i+3)`.
Thus the vector `(1, -a)` represents the exact Galerkin residual `q51` in
the production basis.  The generic endpoint-potential Parseval module is
written in the canonical `+P_(2i+1)` convention, so the actual
`(93/50) V q51` tail is its contraction against this vector followed by the
single global scalar `-93/50`.
-/

/-- The complete production-coordinate vector of the exact `q51` profile:
coefficient one at `P1`, followed by the negative retained solution through
`P51`. -/
def fourCellOddQ51OddLegendreCoefficients : Fin 26 → ℝ :=
  Fin.cases 1 (fun i : Fin 25 ↦ -fourCellOddP51RetainedSolution i)

@[simp] theorem fourCellOddQ51OddLegendreCoefficients_zero :
    fourCellOddQ51OddLegendreCoefficients 0 = 1 := by
  rfl

@[simp] theorem fourCellOddQ51OddLegendreCoefficients_succ (i : Fin 25) :
    fourCellOddQ51OddLegendreCoefficients i.succ =
      -fourCellOddP51RetainedSolution i := by
  rfl

/-- Interpret a 26-vector in the production-sign basis
`centeredP1,P3,...,P51`. -/
def fourCellOddP51ProductionProfile (c : Fin 26 → ℝ) : ℝ → ℝ :=
  fun x ↦ c 0 * centeredP1 x +
    fourCellOddP51RetainedProfile (fun i ↦ c i.succ) x

/-- The concrete 26-vector is exactly the inverse-solved `q51`; this is a
structural `Fin.succ` decomposition, with no coordinate enumeration. -/
theorem fourCellOddP51ProductionProfile_q51Coefficients :
    fourCellOddP51ProductionProfile
        fourCellOddQ51OddLegendreCoefficients =
      fourCellOddQ51 := by
  funext x
  rw [fourCellOddQ51_eq]
  unfold fourCellOddP51ProductionProfile
  simp only [fourCellOddQ51OddLegendreCoefficients_zero,
    fourCellOddQ51OddLegendreCoefficients_succ, one_mul]
  unfold fourCellOddP51RetainedProfile fourCellOddFiniteRetainedProfile
  simp only [Finset.sum_apply, neg_mul]
  rw [Finset.sum_neg_distrib]
  ring

/-- The complete production-sign basis `centeredP1,P3,...,P51`. -/
def fourCellOddP51ProductionBasis (i : Fin 26) : ℝ → ℝ :=
  Fin.cases centeredP1
    (fun j : Fin 25 ↦ fourCellOddFiniteRetainedBasis j) i

/-- Every production basis vector is the negative of the corresponding
canonical centered shifted-Legendre polynomial. -/
theorem fourCellOddP51ProductionBasis_eq_neg_canonical
    (i : Fin 26) (x : ℝ) :
    fourCellOddP51ProductionBasis i x =
      -(centeredShiftedLegendreReal (oddLegendreIndex i)).eval x := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [fourCellOddP51ProductionBasis, oddLegendreIndex, centeredP1]
  · unfold fourCellOddP51ProductionBasis fourCellOddFiniteRetainedBasis
      fourCellOddFiniteRetainedDegree oddLegendreIndex
    congr 2

/-- A sum in the complete production basis is the split `P1` plus retained
profile used by the Galerkin solve. -/
theorem sum_fourCellOddP51ProductionBasis_eq_profile
    (c : Fin 26 → ℝ) (x : ℝ) :
    (∑ i : Fin 26, c i * fourCellOddP51ProductionBasis i x) =
      fourCellOddP51ProductionProfile c x := by
  rw [Fin.sum_univ_succ]
  unfold fourCellOddP51ProductionBasis fourCellOddP51ProductionProfile
    fourCellOddP51RetainedProfile fourCellOddFiniteRetainedProfile
  rfl

/-- Interpret the same vector in the canonical `+P_(2i+1)` convention used
by the endpoint-potential Parseval construction. -/
def fourCellOddP51CanonicalOddLegendreProfile
    (c : Fin 26 → ℝ) : ℝ → ℝ :=
  fun x ↦ ∑ i : Fin 26,
    c i * (centeredShiftedLegendreReal (oddLegendreIndex i)).eval x

/-- The canonical-sign profile of the production coefficient vector is
exactly `-q51`.  This formally accounts for the sole global minus sign in
the concrete endpoint-potential tail below. -/
theorem fourCellOddP51CanonicalOddLegendreProfile_q51Coefficients :
    fourCellOddP51CanonicalOddLegendreProfile
        fourCellOddQ51OddLegendreCoefficients =
      fun x ↦ -fourCellOddQ51 x := by
  funext x
  unfold fourCellOddP51CanonicalOddLegendreProfile
  calc
    (∑ i : Fin 26, fourCellOddQ51OddLegendreCoefficients i *
        (centeredShiftedLegendreReal (oddLegendreIndex i)).eval x) =
        -∑ i : Fin 26, fourCellOddQ51OddLegendreCoefficients i *
          fourCellOddP51ProductionBasis i x := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [fourCellOddP51ProductionBasis_eq_neg_canonical]
      ring
    _ = -fourCellOddP51ProductionProfile
        fourCellOddQ51OddLegendreCoefficients x := by
      rw [sum_fourCellOddP51ProductionBasis_eq_profile]
    _ = -fourCellOddQ51 x := by
      rw [fourCellOddP51ProductionProfile_q51Coefficients]

/-- The actual scaled endpoint-potential `P53+` tail of `q51`, expressed in
the canonical Parseval coordinates.  The minus sign converts the production
`-P_(2i+1)` convention to the canonical `+P_(2i+1)` convention. -/
def fourCellOddQ51ScaledEndpointPotentialP53PlusL2 : UnitIntervalL2 :=
  (-(93 / 50 : ℝ)) •
    oddEndpointPotentialP53PlusL2
      fourCellOddQ51OddLegendreCoefficients

/-- Closed Gram scalar for the same scaled endpoint-potential tail. -/
def fourCellOddQ51ScaledEndpointPotentialP53PlusGram : ℝ :=
  (93 / 50 : ℝ) ^ 2 *
    oddEndpointPotentialP53PlusGram
      fourCellOddQ51OddLegendreCoefficients

/-- The genuine scaled `P53+` tail norm is exactly the closed odd endpoint
Gram contraction specialized to the inverse-defined `q51` coefficients. -/
theorem norm_sq_fourCellOddQ51ScaledEndpointPotentialP53PlusL2_eq_gram :
    ‖fourCellOddQ51ScaledEndpointPotentialP53PlusL2‖ ^ 2 =
      fourCellOddQ51ScaledEndpointPotentialP53PlusGram := by
  rw [fourCellOddQ51ScaledEndpointPotentialP53PlusL2,
    norm_smul, mul_pow,
    norm_sq_oddEndpointPotentialP53PlusL2_eq_gram]
  unfold fourCellOddQ51ScaledEndpointPotentialP53PlusGram
  norm_num [Real.norm_eq_abs]

/-- The complete scaled endpoint-potential source before removing its low
Legendre projection.  By the canonical profile identity above, this is the
`L²` source attached to `(93/50) V q51`. -/
def fourCellOddQ51ScaledEndpointPotentialSourceL2 : UnitIntervalL2 :=
  (-(93 / 50 : ℝ)) •
    oddEndpointPotentialFiniteProfileSourceL2 26
      fourCellOddQ51OddLegendreCoefficients

/-- Coordinate-free statement that a unit-interval `L²` vector belongs to
the genuine shifted-Legendre tail beginning at `P53`. -/
def OddP53PlusHilbertTail (R : UnitIntervalL2) : Prop :=
  ∀ n < 53, shiftedLegendreHilbertBasis.repr R n = 0

private theorem repr_centeredPullbackL2_eq_half_centered_moment
    (r : ℝ → ℝ) (hr : Continuous r) (n : ℕ) :
    shiftedLegendreHilbertBasis.repr (centeredPullbackL2 r hr) n =
      ‖shiftedLegendreL2 n‖⁻¹ * (1 / 2 : ℝ) *
        ∫ x : ℝ in -1..1,
          r x * (centeredShiftedLegendreReal n).eval x := by
  unfold centeredPullbackL2
  rw [shiftedLegendreHilbertBasis_repr_eq]
  rw [mul_assoc]
  apply congrArg (fun z : ℝ ↦ ‖shiftedLegendreL2 n‖⁻¹ * z)
  calc
    (∫ t : unitInterval,
        centeredPullback r (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ)) =
        ∫ t : ℝ in 0..1,
          centeredPullback r t * (shiftedLegendreReal n).eval t :=
      integral_unitInterval_eq_intervalIntegral
        (fun t : ℝ ↦ centeredPullback r t *
          (shiftedLegendreReal n).eval t)
    _ = ∫ t : ℝ in 0..1,
        (fun x : ℝ ↦
          r x * (centeredShiftedLegendreReal n).eval x) (2 * t - 1) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      unfold centeredPullback
      change r (2 * t - 1) * (shiftedLegendreReal n).eval t =
        r (2 * t - 1) *
          (centeredShiftedLegendreReal n).eval (2 * t - 1)
      congr 1
      rw [eval_centeredShiftedLegendreReal]
      congr 1
      ring
    _ = (1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        r x * (centeredShiftedLegendreReal n).eval x :=
      (integral_comp_two_mul_sub_one
        (fun x : ℝ ↦
          r x * (centeredShiftedLegendreReal n).eval x))

private theorem integral_centeredOddLegendre_eq_zero_of_P53Plus
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r)
    (k : ℕ) (hk : k < 26) :
    (∫ x : ℝ in -1..1,
      r x * (centeredShiftedLegendreReal (oddLegendreIndex k)).eval x) = 0 := by
  cases k with
  | zero =>
      have hmoment := htail.1
      unfold centeredOddP1Coefficient at hmoment
      have hP1 : (∫ x : ℝ in -1..1, r x * centeredP1 x) = 0 := by
        exact (mul_eq_zero.mp hmoment).resolve_left (by norm_num)
      rw [show (fun x : ℝ ↦ r x *
          (centeredShiftedLegendreReal (oddLegendreIndex 0)).eval x) =
          fun x ↦ -(r x * centeredP1 x) by
        funext x
        simp [oddLegendreIndex, centeredP1]]
      rw [intervalIntegral.integral_neg, hP1, neg_zero]
  | succ k =>
      have hk25 : k < 25 := by omega
      let i : Fin 25 := ⟨k, hk25⟩
      let p : ℝ → ℝ := fun x ↦
        (centeredShiftedLegendreReal (oddLegendreIndex (k + 1))).eval x
      have hdegree : fourCellOddFiniteRetainedDegree i =
          oddLegendreIndex (k + 1) := by
        simp only [fourCellOddFiniteRetainedDegree, oddLegendreIndex, i]
        omega
      have hbasis (x : ℝ) :
          fourCellOddFiniteRetainedBasis i x = -p x := by
        unfold fourCellOddFiniteRetainedBasis p
        rw [hdegree]
      have hpcont : Continuous p := by
        unfold p
        fun_prop
      have hpodd : Function.Odd p := by
        intro x
        unfold p
        rw [eval_centeredShiftedLegendreReal_neg]
        have hpow : (-1 : ℝ) ^ oddLegendreIndex (k + 1) = -1 := by
          unfold oddLegendreIndex
          rw [pow_add, pow_mul]
          norm_num
        rw [hpow]
        ring
      have hmom := htail.2 i
      have hpos : (∫ x : ℝ in 0..1, r x * p x) = 0 := by
        rw [show (fun x : ℝ ↦
            fourCellOddFiniteRetainedBasis i x * r x) =
            fun x ↦ -(r x * p x) by
          funext x
          rw [hbasis]
          ring,
          intervalIntegral.integral_neg] at hmom
        linarith
      let f : ℝ → ℝ := fun x ↦ r x * p x
      have hfeven : Function.Even f := by
        intro x
        dsimp only [f]
        rw [hodd x, hpodd x]
        ring
      have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
        f ((hr.mul hpcont).intervalIntegrable _ _) hfeven
      dsimp only [f] at hfold
      rw [hpos] at hfold
      simpa only [mul_zero] using hfold

/-- The smooth odd production moment conditions are exactly strong enough
to place the centered pullback in the Hilbert tail beginning at `P53`. -/
theorem oddP53PlusHilbertTail_centeredPullbackL2
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    OddP53PlusHilbertTail (centeredPullbackL2 r hr.continuous) := by
  intro n hn
  by_cases heven : Even n
  · simpa only [centeredPullbackL2] using
      centeredPullback_repr_eq_zero_of_odd_of_even
        r (centeredPullback_memLp_two r hr.continuous) hodd n heven
  · have hoddn : Odd n := Nat.not_even_iff_odd.mp heven
    rcases hoddn with ⟨k, rfl⟩
    have hk : k < 26 := by omega
    rw [show 2 * k + 1 = oddLegendreIndex k by
        unfold oddLegendreIndex; rfl,
      repr_centeredPullbackL2_eq_half_centered_moment,
      integral_centeredOddLegendre_eq_zero_of_P53Plus
        r hr.continuous hodd htail k hk]
    ring

/-- For an odd profile, the centered-pullback Hilbert norm is exactly its
positive-half squared mass. -/
theorem norm_sq_centeredPullbackL2_eq_zero_one_of_odd
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r) :
    ‖centeredPullbackL2 r hr‖ ^ 2 =
      ∫ x : ℝ in 0..1, r x ^ 2 := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback r (t : ℝ)
  have hf : MemLp f 2 := by
    simpa only [f] using centeredPullback_memLp_two r hr
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ r x ^ 2)
    ((hr.pow 2).intervalIntegrable _ _)
    (by
      intro x
      change r (-x) ^ 2 = r x ^ 2
      rw [hodd x]
      ring)
  calc
    ‖centeredPullbackL2 r hr‖ ^ 2 = ∫ t : unitInterval, f t ^ 2 := by
      simpa only [centeredPullbackL2, f] using
        norm_sq_toLp_eq_integral_sq f hf
    _ = (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, r x ^ 2 := by
      exact integral_unitInterval_centeredPullback_sq r
    _ = ∫ x : ℝ in 0..1, r x ^ 2 := by
      rw [hfold]
      ring

private theorem inner_shiftedLegendrePartialProjection_eq_zero_of_tail
    (F R : UnitIntervalL2) (hR : OddP53PlusHilbertTail R) :
    inner ℝ (shiftedLegendrePartialProjection F 53) R = 0 := by
  unfold shiftedLegendrePartialProjection
  rw [sum_inner]
  apply Finset.sum_eq_zero
  intro n hn
  rw [real_inner_smul_left,
    ← shiftedLegendreHilbertBasis.repr_apply_apply,
    hR n (Finset.mem_range.mp hn), mul_zero]

/-- Against a genuine `P53+` Hilbert tail, removing the first 53 degrees
from every endpoint-potential source does not change the pairing. -/
theorem inner_fourCellOddQ51ScaledEndpointPotentialP53PlusL2_eq_source
    (R : UnitIntervalL2) (hR : OddP53PlusHilbertTail R) :
    inner ℝ fourCellOddQ51ScaledEndpointPotentialP53PlusL2 R =
      inner ℝ fourCellOddQ51ScaledEndpointPotentialSourceL2 R := by
  unfold fourCellOddQ51ScaledEndpointPotentialP53PlusL2
    fourCellOddQ51ScaledEndpointPotentialSourceL2
    oddEndpointPotentialP53PlusL2
    oddEndpointPotentialFiniteProfileTailL2
    oddEndpointPotentialFiniteProfileSourceL2
  rw [real_inner_smul_left, real_inner_smul_left]
  congr 1
  rw [sum_inner, sum_inner]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [real_inner_smul_left, real_inner_smul_left]
  congr 1
  unfold oddEndpointPotentialLegendreTailL2
  rw [show oddLegendreIndex 26 = 53 by
      norm_num [oddLegendreIndex],
    inner_sub_left,
    inner_shiftedLegendrePartialProjection_eq_zero_of_tail _ R hR,
    sub_zero]

/-- Closed-Gram Cauchy bound for the full scaled endpoint-potential source
when tested against an arbitrary genuine `P53+` Hilbert tail. -/
theorem sq_inner_fourCellOddQ51ScaledEndpointPotentialSourceL2_le_gram
    (R : UnitIntervalL2) (hR : OddP53PlusHilbertTail R) :
    inner ℝ fourCellOddQ51ScaledEndpointPotentialSourceL2 R ^ 2 ≤
      fourCellOddQ51ScaledEndpointPotentialP53PlusGram * ‖R‖ ^ 2 := by
  rw [← inner_fourCellOddQ51ScaledEndpointPotentialP53PlusL2_eq_source
    R hR]
  have hinner := abs_real_inner_le_norm
    fourCellOddQ51ScaledEndpointPotentialP53PlusL2 R
  have hsquare := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinner
  rw [sq_abs, mul_pow,
    norm_sq_fourCellOddQ51ScaledEndpointPotentialP53PlusL2_eq_gram]
    at hsquare
  exact hsquare

/-- Concrete Cauchy bridge for every smooth odd production `P53+` test.
The right side is already in the positive-half mass normalization used by
the four-cell Galerkin budget. -/
theorem sq_inner_fourCellOddQ51ScaledEndpointPotentialSourceL2_centeredPullback_le
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    inner ℝ fourCellOddQ51ScaledEndpointPotentialSourceL2
        (centeredPullbackL2 r hr.continuous) ^ 2 ≤
      fourCellOddQ51ScaledEndpointPotentialP53PlusGram *
        (∫ x : ℝ in 0..1, r x ^ 2) := by
  have hbound :=
    sq_inner_fourCellOddQ51ScaledEndpointPotentialSourceL2_le_gram
      (centeredPullbackL2 r hr.continuous)
      (oddP53PlusHilbertTail_centeredPullbackL2 r hr hodd htail)
  rw [norm_sq_centeredPullbackL2_eq_zero_one_of_odd
    r hr.continuous hodd] at hbound
  exact hbound

/-- Hilbert-space Cauchy--Schwarz turns the closed Gram scalar directly into
a dual bound against an arbitrary unit-interval `L²` tail. -/
theorem sq_inner_fourCellOddQ51ScaledEndpointPotentialP53PlusL2_le_gram
    (R : UnitIntervalL2) :
    inner ℝ fourCellOddQ51ScaledEndpointPotentialP53PlusL2 R ^ 2 ≤
      fourCellOddQ51ScaledEndpointPotentialP53PlusGram * ‖R‖ ^ 2 := by
  have hinner := abs_real_inner_le_norm
    fourCellOddQ51ScaledEndpointPotentialP53PlusL2 R
  have hsquare := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinner
  rw [sq_abs, mul_pow,
    norm_sq_fourCellOddQ51ScaledEndpointPotentialP53PlusL2_eq_gram]
    at hsquare
  exact hsquare

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51EndpointPotentialTailConcreteStructural
