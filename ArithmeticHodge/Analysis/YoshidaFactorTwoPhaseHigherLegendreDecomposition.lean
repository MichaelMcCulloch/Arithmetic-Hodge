import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseFullProfile

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped BigOperators InnerProductSpace unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseHigherLegendreDecomposition

noncomputable section

open ShiftedLegendreCenteredParity
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open ShiftedLegendreL2SpectralGap
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicHigherResidual

/-!
# Canonical finite shifted-Legendre decomposition

A continuous centered profile is pulled back by `x = 2t - 1`, orthogonally
projected onto all shifted-Legendre degrees below an arbitrary cutoff, and
then transported back to the centered line.  The construction is basis
structural: no coefficient or degree is enumerated.
-/

/-- The centered pullback is continuous on the unit interval. -/
theorem continuous_centeredPullback_restrict
    (w : ℝ → ℝ) (hw : Continuous w) :
    Continuous (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) := by
  unfold centeredPullback
  fun_prop

/-- A continuous centered pullback gives its canonical `L²[0,1]` vector. -/
theorem centeredPullback_memLp_two
    (w : ℝ → ℝ) (hw : Continuous w) :
    MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2 :=
  (continuous_centeredPullback_restrict w hw).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The canonical `L²[0,1]` vector of a centered continuous profile. -/
def centeredPullbackL2
    (w : ℝ → ℝ) (hw : Continuous w) : UnitIntervalL2 :=
  (centeredPullback_memLp_two w hw).toLp
    (fun t : unitInterval ↦ centeredPullback w (t : ℝ))

/-- The finite shifted-Legendre projection polynomial through degrees `< k`. -/
def centeredLegendreProjectionPolynomial
    (w : ℝ → ℝ) (hw : Continuous w) (k : ℕ) : ℝ[X] :=
  shiftedLegendrePartialProjectionPolynomial (centeredPullbackL2 w hw) k

/-- Pull the finite unit-interval projection polynomial back to `[-1,1]`. -/
def centeredLegendreLowProjection
    (w : ℝ → ℝ) (hw : Continuous w) (k : ℕ) : ℝ → ℝ := fun x ↦
  (centeredLegendreProjectionPolynomial w hw k).eval ((x + 1) / 2)

/-- The exact profile left after removing all shifted-Legendre degrees `< k`. -/
def centeredLegendreHigherResidual
    (w : ℝ → ℝ) (hw : Continuous w) (k : ℕ) : ℝ → ℝ := fun x ↦
  w x - centeredLegendreLowProjection w hw k x

/-- The canonical low profile and its residual add back to the original
profile pointwise. -/
theorem centeredLegendreLowProjection_add_higherResidual
    (w : ℝ → ℝ) (hw : Continuous w) (k : ℕ) :
    centeredLegendreLowProjection w hw k +
        centeredLegendreHigherResidual w hw k = w := by
  funext x
  unfold centeredLegendreHigherResidual
  simp only [Pi.add_apply]
  ring

private theorem contDiff_centeredLegendreLowProjection
    (w : ℝ → ℝ) (hw : Continuous w) (k : ℕ) :
    ContDiff ℝ 1 (centeredLegendreLowProjection w hw k) := by
  let p := centeredLegendreProjectionPolynomial w hw k
  have hp : ContDiff ℝ 1 (fun y : ℝ ↦ p.eval y) := by
    simpa only [Polynomial.coe_aeval_eq_eval] using
      p.contDiff_aeval (𝕜 := ℝ) 1
  have haff : ContDiff ℝ 1 (fun x : ℝ ↦ (x + 1) / 2) := by
    fun_prop
  simpa only [centeredLegendreLowProjection, p, Function.comp_apply] using
    hp.comp haff

/-- The transported finite polynomial projection is continuous. -/
theorem continuous_centeredLegendreLowProjection
    (w : ℝ → ℝ) (hw : Continuous w) (k : ℕ) :
    Continuous (centeredLegendreLowProjection w hw k) :=
  (contDiff_centeredLegendreLowProjection w hw k).continuous

/-- The canonical higher residual of a continuous profile is continuous. -/
theorem continuous_centeredLegendreHigherResidual
    (w : ℝ → ℝ) (hw : Continuous w) (k : ℕ) :
    Continuous (centeredLegendreHigherResidual w hw k) := by
  unfold centeredLegendreHigherResidual
  exact hw.sub (continuous_centeredLegendreLowProjection w hw k)

/-- Every finite polynomial low projection is locally Lipschitz on the
centered interval. -/
theorem locallyLipschitzOn_centeredLegendreLowProjection
    (w : ℝ → ℝ) (hw : Continuous w) (k : ℕ) :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (centeredLegendreLowProjection w hw k) :=
  (contDiff_centeredLegendreLowProjection w hw k).locallyLipschitz
    |>.locallyLipschitzOn

/-- Removing the finite polynomial projection preserves local Lipschitz
regularity on the centered interval. -/
theorem locallyLipschitzOn_centeredLegendreHigherResidual
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w) (k : ℕ) :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (centeredLegendreHigherResidual w hw k) := by
  unfold centeredLegendreHigherResidual
  exact hlocal.sub (locallyLipschitzOn_centeredLegendreLowProjection w hw k)

/-! ## Exact annihilation of every coordinate below the cutoff -/

private theorem inner_partialProjection_shiftedLegendreL2_eq
    (F : UnitIntervalL2) (k n : ℕ) (hn : n < k) :
    inner ℝ (shiftedLegendrePartialProjection F k) (shiftedLegendreL2 n) =
      inner ℝ F (shiftedLegendreL2 n) := by
  have hnorm : ‖shiftedLegendreL2 n‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (shiftedLegendreL2_ne_zero n)
  have hraw :
      ‖shiftedLegendreL2 n‖ • shiftedLegendreHilbertBasis n =
        shiftedLegendreL2 n := by
    rw [shiftedLegendreHilbertBasis_apply, normalizedShiftedLegendreL2,
      smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  have hproj :
      inner ℝ (shiftedLegendrePartialProjection F k)
          (shiftedLegendreHilbertBasis n) =
        shiftedLegendreHilbertBasis.repr F n := by
    unfold shiftedLegendrePartialProjection
    simpa only [RCLike.star_def, RCLike.conj_to_real, map_id, id_eq] using
      shiftedLegendreHilbertBasis.orthonormal.inner_left_sum
        (fun j ↦ shiftedLegendreHilbertBasis.repr F j)
        (Finset.mem_range.mpr hn)
  have hfull :
      inner ℝ F (shiftedLegendreHilbertBasis n) =
        shiftedLegendreHilbertBasis.repr F n := by
    rw [real_inner_comm]
    exact (shiftedLegendreHilbertBasis.repr_apply_apply F n).symm
  rw [← hraw, real_inner_smul_right, real_inner_smul_right, hproj, hfull]

private theorem centeredPullback_higherResidual_eq_sub_projection
    (w : ℝ → ℝ) (hw : Continuous w) (k : ℕ) (t : unitInterval) :
    centeredPullback (centeredLegendreHigherResidual w hw k) (t : ℝ) =
      centeredPullback w (t : ℝ) -
        (centeredLegendreProjectionPolynomial w hw k).eval (t : ℝ) := by
  unfold centeredPullback centeredLegendreHigherResidual
    centeredLegendreLowProjection
  rw [show (2 * (t : ℝ) - 1 + 1) / 2 = (t : ℝ) by ring]

/-- The canonical residual annihilates every unnormalised shifted-Legendre
moment below the chosen cutoff. -/
theorem centeredLegendreHigherResidual_momentsVanishBelow
    (w : ℝ → ℝ) (hw : Continuous w) (k : ℕ) :
    centeredLegendreMomentsVanishBelow
      (centeredLegendreHigherResidual w hw k) k := by
  intro n hn
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  let F : UnitIntervalL2 := centeredPullbackL2 w hw
  let p : ℝ[X] := centeredLegendreProjectionPolynomial w hw k
  let q : ℝ[X] := shiftedLegendreReal n
  have hf : MemLp f 2 := by
    simpa only [f] using centeredPullback_memLp_two w hw
  have hfcont : Continuous f := by
    simpa only [f] using continuous_centeredPullback_restrict w hw
  have hpcontR : Continuous (fun x : ℝ ↦ p.eval x) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (p.hasDerivAt x).continuousAt
  have hpcont : Continuous (fun t : unitInterval ↦ p.eval (t : ℝ)) :=
    hpcontR.comp continuous_subtype_val
  have hqcont : Continuous (fun t : unitInterval ↦ q.eval (t : ℝ)) := by
    have hqcontR : Continuous (fun x : ℝ ↦ q.eval x) := by
      rw [continuous_iff_continuousAt]
      intro x
      exact (q.hasDerivAt x).continuousAt
    exact hqcontR.comp continuous_subtype_val
  have hfq : Integrable (fun t : unitInterval ↦ f t * q.eval (t : ℝ)) :=
    (hfcont.mul hqcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpq : Integrable
      (fun t : unitInterval ↦ p.eval (t : ℝ) * q.eval (t : ℝ)) :=
    (hpcont.mul hqcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hintegrand :
      (fun t : unitInterval ↦
        centeredPullback (centeredLegendreHigherResidual w hw k) (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ)) =
      fun t ↦ f t * q.eval (t : ℝ) -
        p.eval (t : ℝ) * q.eval (t : ℝ) := by
    funext t
    rw [centeredPullback_higherResidual_eq_sub_projection w hw k t]
    simp only [f, p, q]
    ring
  have hfpair :
      (∫ t : unitInterval, f t * q.eval (t : ℝ)) =
        inner ℝ F (shiftedLegendreL2 n) := by
    have h := integral_mul_polynomial_eq_inner f hf q
    simpa only [f, F, centeredPullbackL2, q, shiftedLegendreL2] using h
  have hpL2 : polynomialToL2 p = shiftedLegendrePartialProjection F k := by
    simpa only [p, F, centeredLegendreProjectionPolynomial] using
      polynomialToL2_shiftedLegendrePartialProjectionPolynomial F k
  have hppair :
      (∫ t : unitInterval, p.eval (t : ℝ) * q.eval (t : ℝ)) =
        inner ℝ (shiftedLegendrePartialProjection F k)
          (shiftedLegendreL2 n) := by
    rw [integral_polynomial_mul_eq_inner, hpL2]
    rfl
  rw [hintegrand, integral_sub hfq hpq, hfpair, hppair,
    inner_partialProjection_shiftedLegendreL2_eq F k n hn, sub_self]

/-! ## Structural parity of the canonical projections -/

private theorem shiftedLegendreReal_eval_one_sub
    (n : ℕ) (x : ℝ) :
    (shiftedLegendreReal n).eval (1 - x) =
      (-1 : ℝ) ^ n * (shiftedLegendreReal n).eval x := by
  simp only [shiftedLegendreReal, Polynomial.eval_map]
  change Polynomial.aeval (1 - x) (Polynomial.shiftedLegendre n) =
    (-1 : ℝ) ^ n * Polynomial.aeval x (Polynomial.shiftedLegendre n)
  simpa using Polynomial.shiftedLegendre_eval_symm n (1 - x)

private theorem normalizedShiftedLegendrePolynomial_eval_one_sub
    (n : ℕ) (x : ℝ) :
    (normalizedShiftedLegendrePolynomial n).eval (1 - x) =
      (-1 : ℝ) ^ n *
        (normalizedShiftedLegendrePolynomial n).eval x := by
  unfold normalizedShiftedLegendrePolynomial
  simp only [Polynomial.eval_smul, smul_eq_mul]
  rw [shiftedLegendreReal_eval_one_sub]
  ring

private theorem centeredLegendreProjectionPolynomial_eval_one_sub_of_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w)
    (k : ℕ) (x : ℝ) :
    (centeredLegendreProjectionPolynomial w hw k).eval (1 - x) =
      (centeredLegendreProjectionPolynomial w hw k).eval x := by
  unfold centeredLegendreProjectionPolynomial
    shiftedLegendrePartialProjectionPolynomial
  rw [Polynomial.eval_finset_sum, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [normalizedShiftedLegendrePolynomial_eval_one_sub]
  by_cases hneven : Even n
  · rw [hneven.neg_one_pow]
    ring
  · have hnodd : Odd n := Nat.not_even_iff_odd.mp hneven
    have hcoeff := centeredPullback_repr_eq_zero_of_even_of_odd
      w (centeredPullback_memLp_two w hw) heven n hnodd
    change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 w hw) n = 0
      at hcoeff
    rw [hcoeff]
    ring

private theorem centeredLegendreProjectionPolynomial_eval_one_sub_of_odd
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w)
    (k : ℕ) (x : ℝ) :
    (centeredLegendreProjectionPolynomial w hw k).eval (1 - x) =
      -(centeredLegendreProjectionPolynomial w hw k).eval x := by
  unfold centeredLegendreProjectionPolynomial
    shiftedLegendrePartialProjectionPolynomial
  rw [Polynomial.eval_finset_sum, Polynomial.eval_finset_sum,
    ← Finset.sum_neg_distrib]
  simp only [Polynomial.eval_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [normalizedShiftedLegendrePolynomial_eval_one_sub]
  by_cases hnodd : Odd n
  · rw [hnodd.neg_one_pow]
    ring
  · have hneven : Even n := Nat.not_odd_iff_even.mp hnodd
    have hcoeff := centeredPullback_repr_eq_zero_of_odd_of_even
      w (centeredPullback_memLp_two w hw) hodd n hneven
    change shiftedLegendreHilbertBasis.repr (centeredPullbackL2 w hw) n = 0
      at hcoeff
    rw [hcoeff]
    ring

/-- Every canonical finite low projection of an even profile is even. -/
theorem centeredLegendreLowProjection_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) (k : ℕ) :
    Function.Even (centeredLegendreLowProjection w hw k) := by
  intro x
  unfold centeredLegendreLowProjection
  rw [show (-x + 1) / 2 = 1 - (x + 1) / 2 by ring,
    centeredLegendreProjectionPolynomial_eval_one_sub_of_even
      w hw heven k]

/-- Every canonical finite residual of an even profile is even. -/
theorem centeredLegendreHigherResidual_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) (k : ℕ) :
    Function.Even (centeredLegendreHigherResidual w hw k) := by
  intro x
  unfold centeredLegendreHigherResidual
  rw [heven x, centeredLegendreLowProjection_even w hw heven k x]

/-- Every canonical finite low projection of an odd profile is odd. -/
theorem centeredLegendreLowProjection_odd
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) (k : ℕ) :
    Function.Odd (centeredLegendreLowProjection w hw k) := by
  intro x
  unfold centeredLegendreLowProjection
  rw [show (-x + 1) / 2 = 1 - (x + 1) / 2 by ring,
    centeredLegendreProjectionPolynomial_eval_one_sub_of_odd
      w hw hodd k]

/-- Every canonical finite residual of an odd profile is odd. -/
theorem centeredLegendreHigherResidual_odd
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) (k : ℕ) :
    Function.Odd (centeredLegendreHigherResidual w hw k) := by
  intro x
  unfold centeredLegendreHigherResidual
  rw [hodd x, centeredLegendreLowProjection_odd w hw hodd k x]
  ring

/-- The cutoff-nine even decomposition preserves parity in both blocks. -/
theorem centeredLegendre_cutoffNine_even_parity
    (e : ℝ → ℝ) (hec : Continuous e) (heven : Function.Even e) :
    Function.Even (centeredLegendreLowProjection e hec 9) ∧
      Function.Even (centeredLegendreHigherResidual e hec 9) :=
  ⟨centeredLegendreLowProjection_even e hec heven 9,
    centeredLegendreHigherResidual_even e hec heven 9⟩

/-- The cutoff-ten odd decomposition preserves parity in both blocks. -/
theorem centeredLegendre_cutoffTen_odd_parity
    (o : ℝ → ℝ) (hoc : Continuous o) (hodd : Function.Odd o) :
    Function.Odd (centeredLegendreLowProjection o hoc 10) ∧
      Function.Odd (centeredLegendreHigherResidual o hoc 10) :=
  ⟨centeredLegendreLowProjection_odd o hoc hodd 10,
    centeredLegendreHigherResidual_odd o hoc hodd 10⟩

/-! ## Exact low--mixed--residual phase polarization -/

/-- Exact channel polarization for arbitrary even- and odd-side cutoffs.
Every clean, symmetric, alternating, and prime contribution remains inside
the existing full-profile polarization API. -/
theorem factorTwoEndpointChannelPhase_eq_legendreLow_mixed_residual
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (ke ko : ℕ) (a b : ℝ) :
    factorTwoEndpointChannelPhase e o a b =
      factorTwoEndpointChannelPhase
          (centeredLegendreLowProjection e hec ke)
          (centeredLegendreLowProjection o hoc ko) a b +
        2 * factorTwoEndpointLowTailMixed
          (centeredLegendreLowProjection e hec ke)
          (centeredLegendreHigherResidual e hec ke)
          (centeredLegendreLowProjection o hoc ko)
          (centeredLegendreHigherResidual o hoc ko) a b +
        factorTwoEndpointChannelPhase
          (centeredLegendreHigherResidual e hec ke)
          (centeredLegendreHigherResidual o hoc ko) a b := by
  have heLow := continuous_centeredLegendreLowProjection e hec ke
  have heResidual := continuous_centeredLegendreHigherResidual e hec ke
  have hoLow := continuous_centeredLegendreLowProjection o hoc ko
  have hoResidual := continuous_centeredLegendreHigherResidual o hoc ko
  have hsplit := factorTwoEndpointChannelPhase_add_add_eq_low_mixed_tail
    (centeredLegendreLowProjection e hec ke)
    (centeredLegendreHigherResidual e hec ke)
    (centeredLegendreLowProjection o hoc ko)
    (centeredLegendreHigherResidual o hoc ko)
    heLow heResidual hoLow hoResidual a b
  rw [centeredLegendreLowProjection_add_higherResidual e hec ke,
    centeredLegendreLowProjection_add_higherResidual o hoc ko] at hsplit
  exact hsplit

/-- The canonical higher-gap cutoffs give the exact low--mixed--residual
decomposition needed by the ninth-even/tenth-odd residual theorem. -/
theorem factorTwoEndpointChannelPhase_eq_nine_ten_legendre_decomposition
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (a b : ℝ) :
    factorTwoEndpointChannelPhase e o a b =
      factorTwoEndpointChannelPhase
          (centeredLegendreLowProjection e hec 9)
          (centeredLegendreLowProjection o hoc 10) a b +
        2 * factorTwoEndpointLowTailMixed
          (centeredLegendreLowProjection e hec 9)
          (centeredLegendreHigherResidual e hec 9)
          (centeredLegendreLowProjection o hoc 10)
          (centeredLegendreHigherResidual o hoc 10) a b +
        factorTwoEndpointChannelPhase
          (centeredLegendreHigherResidual e hec 9)
          (centeredLegendreHigherResidual o hoc 10) a b :=
  factorTwoEndpointChannelPhase_eq_legendreLow_mixed_residual
    e o hec hoc 9 10 a b

/-- Both canonical higher residuals have precisely the moment gaps used by
the higher-residual positivity theorem. -/
theorem nine_ten_higherResidual_moment_gaps
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o) :
    centeredLegendreMomentsVanishBelow
        (centeredLegendreHigherResidual e hec 9) 9 ∧
      centeredLegendreMomentsVanishBelow
        (centeredLegendreHigherResidual o hoc 10) 10 :=
  ⟨centeredLegendreHigherResidual_momentsVanishBelow e hec 9,
    centeredLegendreHigherResidual_momentsVanishBelow o hoc 10⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseHigherLegendreDecomposition
