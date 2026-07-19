import ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotonePropagationLogDefectStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotonePropagationReserveStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction ComplexConjugate

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutoffCommutatorStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealLogKernelStructural
open MultiplicativeWeilRealMonotonePropagationLogDefectStructural
open MultiplicativeWeilRealMonotonePropagationReserveStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open YoshidaBombieriCrossDistribution
open YoshidaCauchyPairing

/-!
# The complete logarithmic commutator of a monotone cutoff

For the boundary multiplier `m`, the elementary identity

`2 m(x) m(y) = m(x)^2 + m(y)^2 - (m(x) - m(y))^2`

turns the quadratic value of `m * parent` into a symmetrized ground-state
term minus a carré-du-champ commutator.  The identity is exact for the
production monotone cutoff and the complete Bombieri logarithmic kernel.

The resulting commutator is not a Dirichlet form.  Its archimedean part is
followed by subtraction of the symmetric Mangoldt atoms, and already the
atom at `+- log 2` has a strictly negative complete-kernel coefficient.  In
addition, the nonnegative carré multiplier still multiplies the signed
parent correlation.  Consequently the commutator has no pointwise sign from
monotonicity alone.  The exact one-step propagation target is an upper bound
on this signed commutator, not the assertion that it is nonnegative.
-/

/-- The monotone boundary multiplier in critical logarithmic coordinates. -/
def monotoneQuarterCutoffLogMultiplier (k : ℤ) (t : ℝ) : ℝ :=
  monotoneQuarterStep k (Real.exp (-t))

/-- The carré-du-champ multiplier at logarithmic lag `u`. -/
def monotoneQuarterCutoffCarreMultiplier
    (k : ℤ) (u t : ℝ) : ℝ :=
  (monotoneQuarterCutoffLogMultiplier k t -
    monotoneQuarterCutoffLogMultiplier k (u + t)) ^ 2

/-- Exact symmetrized multiplier identity behind the commutator. -/
theorem two_mul_monotoneQuarterCutoffLogMultiplier_eq_squares_sub_carre
    (k : ℤ) (u t : ℝ) :
    2 * monotoneQuarterCutoffLogMultiplier k t *
        monotoneQuarterCutoffLogMultiplier k (u + t) =
      monotoneQuarterCutoffLogMultiplier k t ^ 2 +
        monotoneQuarterCutoffLogMultiplier k (u + t) ^ 2 -
          monotoneQuarterCutoffCarreMultiplier k u t := by
  unfold monotoneQuarterCutoffCarreMultiplier
  ring

/-- The carré multiplier itself is pointwise nonnegative. -/
theorem monotoneQuarterCutoffCarreMultiplier_nonnegative
    (k : ℤ) (u t : ℝ) :
    0 ≤ monotoneQuarterCutoffCarreMultiplier k u t := by
  exact sq_nonneg _

/-- Applying the same boundary cutoff twice realizes the `m^2` ground-state
factor as an actual Bombieri test. -/
def monotoneQuarterSquaredCutoff
    (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  monotoneQuarterCutoff (monotoneQuarterCutoff parent k) k

@[simp] theorem monotoneQuarterSquaredCutoff_apply
    (parent : BombieriTest) (k : ℤ) (x : ℝ) :
    monotoneQuarterSquaredCutoff parent k x =
      ((monotoneQuarterStep k x : ℝ) : ℂ) ^ 2 * parent x := by
  simp only [monotoneQuarterSquaredCutoff, monotoneQuarterCutoff_apply]
  ring

/-- The carré correlation is the parent correlation multiplied by the exact
square difference of the two boundary values. -/
def monotoneQuarterCutoffCarreCorrelation
    (parent : BombieriTest) (k : ℤ) (u : ℝ) : ℂ :=
  ∫ t : ℝ,
    ((monotoneQuarterCutoffCarreMultiplier k u t : ℝ) : ℂ) *
      monotoneQuarterParentLogProduct parent u t

/-- One carré integrand retains the sign of the parent correlation despite
the nonnegative multiplier. -/
theorem monotoneQuarterCutoffCarreIntegrand_re
    (parent : BombieriTest) (k : ℤ) (u t : ℝ) :
    (((monotoneQuarterCutoffCarreMultiplier k u t : ℝ) : ℂ) *
        monotoneQuarterParentLogProduct parent u t).re =
      monotoneQuarterCutoffCarreMultiplier k u t *
        (monotoneQuarterParentLogProduct parent u t).re := by
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-- A strictly negative parent correlation gives a strictly negative carré
integrand wherever the cutoff actually changes across the lag. -/
theorem monotoneQuarterCutoffCarreIntegrand_re_negative
    (parent : BombieriTest) (k : ℤ) (u t : ℝ)
    (hcarre : 0 < monotoneQuarterCutoffCarreMultiplier k u t)
    (hparent : (monotoneQuarterParentLogProduct parent u t).re < 0) :
    (((monotoneQuarterCutoffCarreMultiplier k u t : ℝ) : ℂ) *
        monotoneQuarterParentLogProduct parent u t).re < 0 := by
  rw [monotoneQuarterCutoffCarreIntegrand_re]
  exact mul_neg_of_pos_of_neg hcarre hparent

private theorem monotoneQuarterCutoff_logarithmicPullbackSchwartz
    (parent : BombieriTest) (k : ℤ) (t : ℝ) :
    (monotoneQuarterCutoff parent k).logarithmicPullbackSchwartz (1 / 2) t =
      ((monotoneQuarterCutoffLogMultiplier k t : ℝ) : ℂ) *
        parent.logarithmicPullbackSchwartz (1 / 2) t := by
  simp only [BombieriTest.logarithmicPullbackSchwartz_apply,
    BombieriTest.logarithmicPullback, monotoneQuarterCutoff_apply,
    monotoneQuarterCutoffLogMultiplier]
  push_cast
  ring

private theorem monotoneQuarterSquaredCutoff_logarithmicPullbackSchwartz
    (parent : BombieriTest) (k : ℤ) (t : ℝ) :
    (monotoneQuarterSquaredCutoff parent k).logarithmicPullbackSchwartz
        (1 / 2) t =
      (((monotoneQuarterCutoffLogMultiplier k t : ℝ) : ℂ) ^ 2) *
        parent.logarithmicPullbackSchwartz (1 / 2) t := by
  unfold monotoneQuarterSquaredCutoff
  rw [monotoneQuarterCutoff_logarithmicPullbackSchwartz,
    monotoneQuarterCutoff_logarithmicPullbackSchwartz]
  ring

private theorem monotoneQuarterCutoffCarreIntegrand_integrable
    (parent : BombieriTest) (k : ℤ) (u : ℝ) :
    Integrable (fun t : ℝ ↦
      ((monotoneQuarterCutoffCarreMultiplier k u t : ℝ) : ℂ) *
        monotoneQuarterParentLogProduct parent u t) := by
  have hcont : Continuous (fun t : ℝ ↦
      ((monotoneQuarterCutoffCarreMultiplier k u t : ℝ) : ℂ) *
        monotoneQuarterParentLogProduct parent u t) := by
    have hm : Continuous (monotoneQuarterCutoffLogMultiplier k) := by
      unfold monotoneQuarterCutoffLogMultiplier
      exact (monotoneQuarterStep_contDiff k).continuous.comp (by fun_prop)
    have hmshift : Continuous (fun t : ℝ ↦
        monotoneQuarterCutoffLogMultiplier k (u + t)) :=
      hm.comp (by fun_prop)
    have hcarre : Continuous (monotoneQuarterCutoffCarreMultiplier k u) := by
      unfold monotoneQuarterCutoffCarreMultiplier
      exact (hm.sub hmshift).pow 2
    have hparent : Continuous (monotoneQuarterParentLogProduct parent u) := by
      unfold monotoneQuarterParentLogProduct
      exact (parent.logarithmicPullbackSchwartz (1 / 2)).continuous.star.mul
        ((parent.logarithmicPullbackSchwartz (1 / 2)).continuous.comp
          (by fun_prop))
    exact (Complex.continuous_ofReal.comp hcarre).mul hparent
  have hcompact : HasCompactSupport (fun t : ℝ ↦
      ((monotoneQuarterCutoffCarreMultiplier k u t : ℝ) : ℂ) *
        monotoneQuarterParentLogProduct parent u t) := by
    have hp : HasCompactSupport (fun t : ℝ ↦
        starRingEnd ℂ
          (parent.logarithmicPullbackSchwartz (1 / 2) t)) := by
      exact (parent.logarithmicPullback_hasCompactSupport (1 / 2)).comp_left
        (by simp)
    unfold monotoneQuarterParentLogProduct
    exact hp.mul_right.mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

private theorem bombieriCriticalCrossIntegrand_integrable'
    (f g : BombieriTest) (u : ℝ) :
    Integrable (fun t : ℝ ↦
      starRingEnd ℂ (f.logarithmicPullbackSchwartz (1 / 2) t) *
        g.logarithmicPullbackSchwartz (1 / 2) (u + t)) := by
  have hcont : Continuous (fun t : ℝ ↦
      starRingEnd ℂ (f.logarithmicPullbackSchwartz (1 / 2) t) *
        g.logarithmicPullbackSchwartz (1 / 2) (u + t)) := by
    exact (f.logarithmicPullbackSchwartz (1 / 2)).continuous.star.mul
      ((g.logarithmicPullbackSchwartz (1 / 2)).continuous.comp (by fun_prop))
  have hcompact : HasCompactSupport (fun t : ℝ ↦
      starRingEnd ℂ (f.logarithmicPullbackSchwartz (1 / 2) t) *
        g.logarithmicPullbackSchwartz (1 / 2) (u + t)) := by
    have hf : HasCompactSupport (fun t : ℝ ↦
        starRingEnd ℂ (f.logarithmicPullbackSchwartz (1 / 2) t)) := by
      exact (f.logarithmicPullback_hasCompactSupport (1 / 2)).comp_left
        (by simp)
    exact hf.mul_right
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- Correlation-level commutator identity.  This is the integrated production
form of `2 m(x)m(y) = m(x)^2 + m(y)^2 - (m(x)-m(y))^2`. -/
theorem two_mul_bombieriCriticalCrossCorrelation_cutoff_self
    (parent : BombieriTest) (k : ℤ) (u : ℝ) :
    2 * bombieriCriticalCrossCorrelation
        (monotoneQuarterCutoff parent k)
        (monotoneQuarterCutoff parent k) u =
      bombieriCriticalCrossCorrelation
          (monotoneQuarterSquaredCutoff parent k) parent u +
        bombieriCriticalCrossCorrelation
          parent (monotoneQuarterSquaredCutoff parent k) u -
        monotoneQuarterCutoffCarreCorrelation parent k u := by
  rw [bombieriCriticalCrossCorrelation, crossCorrelation_apply,
    bombieriCriticalCrossCorrelation, crossCorrelation_apply,
    bombieriCriticalCrossCorrelation, crossCorrelation_apply]
  unfold monotoneQuarterCutoffCarreCorrelation
  let cut := monotoneQuarterCutoff parent k
  let sqCut := monotoneQuarterSquaredCutoff parent k
  let P : ℝ → ℂ := parent.logarithmicPullbackSchwartz (1 / 2)
  let Fcut : ℝ → ℂ := cut.logarithmicPullbackSchwartz (1 / 2)
  let Fsq : ℝ → ℂ := sqCut.logarithmicPullbackSchwartz (1 / 2)
  let A : ℝ → ℂ := fun t ↦ starRingEnd ℂ (Fcut t) * Fcut (u + t)
  let B : ℝ → ℂ := fun t ↦ starRingEnd ℂ (Fsq t) * P (u + t)
  let C : ℝ → ℂ := fun t ↦ starRingEnd ℂ (P t) * Fsq (u + t)
  let G : ℝ → ℂ := fun t ↦
    ((monotoneQuarterCutoffCarreMultiplier k u t : ℝ) : ℂ) *
      monotoneQuarterParentLogProduct parent u t
  have hA : Integrable A := by
    simpa only [A, Fcut, cut] using
      bombieriCriticalCrossIntegrand_integrable' cut cut u
  have hB : Integrable B := by
    simpa only [B, Fsq, P, sqCut] using
      bombieriCriticalCrossIntegrand_integrable' sqCut parent u
  have hC : Integrable C := by
    simpa only [C, Fsq, P, sqCut] using
      bombieriCriticalCrossIntegrand_integrable' parent sqCut u
  have hG : Integrable G := by
    simpa only [G] using
      monotoneQuarterCutoffCarreIntegrand_integrable parent k u
  change 2 * ∫ t : ℝ, A t =
    (∫ t : ℝ, B t) + (∫ t : ℝ, C t) - ∫ t : ℝ, G t
  calc
    2 * ∫ t : ℝ, A t = ∫ t : ℝ, (2 : ℂ) * A t := by
      exact (MeasureTheory.integral_const_mul (2 : ℂ) A).symm
    _ = ∫ t : ℝ, (B t + C t) - G t := by
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp only [A, B, C, G, Fcut, Fsq, P, cut, sqCut]
      rw [monotoneQuarterCutoff_logarithmicPullbackSchwartz,
        monotoneQuarterCutoff_logarithmicPullbackSchwartz,
        monotoneQuarterSquaredCutoff_logarithmicPullbackSchwartz,
        monotoneQuarterSquaredCutoff_logarithmicPullbackSchwartz]
      unfold monotoneQuarterParentLogProduct
        monotoneQuarterCutoffCarreMultiplier
        monotoneQuarterCutoffLogMultiplier
      simp only [map_mul, map_pow, Complex.conj_ofReal]
      push_cast
      ring
    _ = (∫ t : ℝ, B t) + (∫ t : ℝ, C t) - ∫ t : ℝ, G t := by
      calc
        (∫ t : ℝ, (B t + C t) - G t) =
            (∫ t : ℝ, (B + C) t) - ∫ t : ℝ, G t := by
          simpa only [Pi.add_apply, Pi.sub_apply] using
            (integral_sub (hB.add hC) hG)
        _ = (∫ t : ℝ, B t) + (∫ t : ℝ, C t) - ∫ t : ℝ, G t := by
          rw [show (∫ t : ℝ, (B + C) t) =
              (∫ t : ℝ, B t) + ∫ t : ℝ, C t by
            simpa only [Pi.add_apply] using integral_add hB hC]

/-- The archimedean carré commutator, before the arithmetic atoms are
subtracted. -/
def monotoneQuarterCutoffArchimedeanCommutator
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  bombieriRealLogArchimedeanCross
      (monotoneQuarterSquaredCutoff parent k) parent +
    bombieriRealLogArchimedeanCross
      parent (monotoneQuarterSquaredCutoff parent k) -
    2 * bombieriRealLogArchimedeanCross
      (monotoneQuarterCutoff parent k) (monotoneQuarterCutoff parent k)

/-- The symmetric Mangoldt carré commutator.  It enters the complete kernel
with a minus sign. -/
def monotoneQuarterCutoffMangoldtCommutator
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  bombieriRealLogPrimeAtomCross
      (monotoneQuarterSquaredCutoff parent k) parent +
    bombieriRealLogPrimeAtomCross
      parent (monotoneQuarterSquaredCutoff parent k) -
    2 * bombieriRealLogPrimeAtomCross
      (monotoneQuarterCutoff parent k) (monotoneQuarterCutoff parent k)

/-- The exact complete commutator: archimedean distribution minus Mangoldt
atoms. -/
def monotoneQuarterCutoffCompleteCommutator
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  monotoneQuarterCutoffArchimedeanCommutator parent k -
    monotoneQuarterCutoffMangoldtCommutator parent k

/-- Named form of the signed-kernel split.  The arithmetic carré term is
subtracted, so nonnegativity of the square-difference multiplier does not
make the complete commutator a Dirichlet form. -/
theorem monotoneQuarterCutoffCompleteCommutator_eq_archimedean_sub_mangoldt
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterCutoffCompleteCommutator parent k =
      monotoneQuarterCutoffArchimedeanCommutator parent k -
        monotoneQuarterCutoffMangoldtCommutator parent k := rfl

theorem monotoneQuarterCutoffCompleteCommutator_eq_completeKernel
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterCutoffCompleteCommutator parent k =
      bombieriCompleteRealLogKernelCross
          (monotoneQuarterSquaredCutoff parent k) parent +
        bombieriCompleteRealLogKernelCross
          parent (monotoneQuarterSquaredCutoff parent k) -
        2 * bombieriCompleteRealLogKernelCross
          (monotoneQuarterCutoff parent k)
          (monotoneQuarterCutoff parent k) := by
  unfold monotoneQuarterCutoffCompleteCommutator
    monotoneQuarterCutoffArchimedeanCommutator
    monotoneQuarterCutoffMangoldtCommutator
    bombieriCompleteRealLogKernelCross
  ring

private theorem bombieriCompleteRealLogKernelCross_comm
    (f g : BombieriTest) :
    bombieriCompleteRealLogKernelCross f g =
      bombieriCompleteRealLogKernelCross g f := by
  rw [bombieriCompleteRealLogKernelCross_eq_globalCross_re,
    bombieriCompleteRealLogKernelCross_eq_globalCross_re]
  have h := bombieriTwoBlockGlobalCrossSymbol_conj_swap f g
  have hre := congrArg Complex.re h
  simpa only [Complex.star_def, Complex.conj_re] using hre.symm

/-- Ground-state/carré-du-champ identity for the complete Bombieri form. -/
theorem two_mul_bombieriQuadratic_cutoff_eq_ground_sub_commutator
    (parent : BombieriTest) (k : ℤ) :
    2 * (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterCutoff parent k))).re =
      2 * bombieriCompleteRealLogKernelCross
        (monotoneQuarterSquaredCutoff parent k) parent -
      monotoneQuarterCutoffCompleteCommutator parent k := by
  rw [monotoneQuarterCutoffCompleteCommutator_eq_completeKernel,
    bombieriCompleteRealLogKernelCross_comm
      parent (monotoneQuarterSquaredCutoff parent k),
    ← bombieriFunctional_quadratic_re_eq_completeRealLogKernel]
  ring

/-- Thus positivity of this cutoff is exactly an upper bound on the signed
commutator.  A favorable sign alone would not suffice without control of the
ground-state cross on the right. -/
theorem bombieriQuadratic_cutoff_nonnegative_iff_commutator_le_ground
    (parent : BombieriTest) (k : ℤ) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterCutoff parent k))).re ↔
      monotoneQuarterCutoffCompleteCommutator parent k ≤
        2 * bombieriCompleteRealLogKernelCross
          (monotoneQuarterSquaredCutoff parent k) parent := by
  have h := two_mul_bombieriQuadratic_cutoff_eq_ground_sub_commutator
    parent k
  constructor <;> intro hsign <;> linarith

/-- The existing one-step cross target is precisely the same signed
commutator upper bound. -/
theorem monotoneQuarterHeadSuffix_cross_bound_iff_commutator_le_ground
    (parent : BombieriTest) (k : ℤ) :
    -2 * monotoneQuarterHeadSuffixCrossValue parent k ≤
        monotoneQuarterHeadQuadraticValue parent k +
          monotoneQuarterSuffixQuadraticValue parent k ↔
      monotoneQuarterCutoffCompleteCommutator parent k ≤
        2 * bombieriCompleteRealLogKernelCross
          (monotoneQuarterSquaredCutoff parent k) parent := by
  have hsplit :=
    bombieriRealQuadraticValue_monotoneQuarterCutoff_eq_head_suffix_cross
      parent k
  have hcomm := two_mul_bombieriQuadratic_cutoff_eq_ground_sub_commutator
    parent k
  unfold bombieriRealQuadraticValue at hsplit
  constructor <;> intro hbound <;> linarith

/-- The contribution associated to one symmetric Mangoldt atom after the
carre multiplier is exposed at the correlation level. -/
def monotoneQuarterCutoffCarreMangoldtAtom
    (parent : BombieriTest) (k : ℤ) (j : ℕ) : ℝ :=
  bombieriLogPrimeAtomWeight j *
    ((monotoneQuarterCutoffCarreCorrelation parent k
        (-Real.log (((j + 1 : ℕ) : ℝ)))).re +
      (monotoneQuarterCutoffCarreCorrelation parent k
        (Real.log (((j + 1 : ℕ) : ℝ)))).re)

/-- The displayed carré atom is exactly the symmetrized `m² + m² - 2m m`
combination of the corresponding real Mangoldt correlation summands. -/
theorem monotoneQuarterCutoffCarreMangoldtAtom_eq_symmetrized
    (parent : BombieriTest) (k : ℤ) (j : ℕ) :
    monotoneQuarterCutoffCarreMangoldtAtom parent k j =
      bombieriLogPrimeAtomWeight j *
        (((bombieriCriticalCrossCorrelation
              (monotoneQuarterSquaredCutoff parent k) parent
              (-Real.log (((j + 1 : ℕ) : ℝ)))).re +
            (bombieriCriticalCrossCorrelation
              (monotoneQuarterSquaredCutoff parent k) parent
              (Real.log (((j + 1 : ℕ) : ℝ)))).re) +
          ((bombieriCriticalCrossCorrelation
              parent (monotoneQuarterSquaredCutoff parent k)
              (-Real.log (((j + 1 : ℕ) : ℝ)))).re +
            (bombieriCriticalCrossCorrelation
              parent (monotoneQuarterSquaredCutoff parent k)
              (Real.log (((j + 1 : ℕ) : ℝ)))).re) -
          2 *
            ((bombieriCriticalCrossCorrelation
              (monotoneQuarterCutoff parent k)
              (monotoneQuarterCutoff parent k)
              (-Real.log (((j + 1 : ℕ) : ℝ)))).re +
            (bombieriCriticalCrossCorrelation
              (monotoneQuarterCutoff parent k)
              (monotoneQuarterCutoff parent k)
              (Real.log (((j + 1 : ℕ) : ℝ)))).re)) := by
  have hminus := congrArg Complex.re
    (two_mul_bombieriCriticalCrossCorrelation_cutoff_self parent k
      (-Real.log (((j + 1 : ℕ) : ℝ))))
  have hplus := congrArg Complex.re
    (two_mul_bombieriCriticalCrossCorrelation_cutoff_self parent k
      (Real.log (((j + 1 : ℕ) : ℝ))))
  norm_num [Complex.mul_re] at hminus hplus
  unfold monotoneQuarterCutoffCarreMangoldtAtom
  have hj : (((j + 1 : ℕ) : ℝ)) = (j : ℝ) + 1 := by norm_num
  simp only [hj] at hminus hplus ⊢
  congr 1
  linarith

/-- In the complete kernel the first nontrivial carré atom has the strictly
negative coefficient `-log 2 / sqrt 2`. -/
theorem complete_logTwo_carre_coefficient_lt_zero :
    -bombieriLogPrimeAtomWeight 1 < 0 :=
  neg_bombieriLogPrimeAtomWeight_one_lt_zero

theorem complete_logTwo_carre_coefficient_eq :
    -bombieriLogPrimeAtomWeight 1 =
      -(Real.log 2 / Real.sqrt 2) := by
  rw [bombieriLogPrimeAtomWeight_one]

/-- Whenever the symmetric log-two carré correlation is positive, its
individual contribution to the complete commutator is strictly negative. -/
theorem neg_logTwo_carre_atom_negative_of_positive
    (parent : BombieriTest) (k : ℤ)
    (hpositive : 0 <
      (monotoneQuarterCutoffCarreCorrelation parent k (-Real.log 2)).re +
        (monotoneQuarterCutoffCarreCorrelation parent k (Real.log 2)).re) :
    -monotoneQuarterCutoffCarreMangoldtAtom parent k 1 < 0 := by
  unfold monotoneQuarterCutoffCarreMangoldtAtom
  norm_num only [Nat.cast_ofNat]
  have hweight : 0 < bombieriLogPrimeAtomWeight 1 := by
    rw [bombieriLogPrimeAtomWeight_one]
    exact div_pos (Real.log_pos (by norm_num)) (by positivity)
  exact neg_neg_of_pos (mul_pos hweight hpositive)

/-- Four quarter steps are exactly the log-two separation, and at a boundary
point the carré multiplier is maximal rather than zero. -/
theorem monotoneQuarterCutoffCarreMultiplier_logTwo_boundary
    (k : ℤ) :
    monotoneQuarterCutoffCarreMultiplier k (Real.log 2)
        (-Real.log (quarterLogLatticePoint (k + 1))) = 1 := by
  have hx : 0 < quarterLogLatticePoint (k + 1) :=
    quarterLogLatticePoint_pos _
  have hhalf : quarterLogLatticePoint (k + 1) / 2 =
      quarterLogLatticePoint (k - 3) := by
    have hfour := quarterLogLatticePoint_add_four (k - 3)
    rw [show k - 3 + 4 = k + 1 by ring] at hfour
    linarith
  have hfirst :
      Real.exp (-(-Real.log (quarterLogLatticePoint (k + 1)))) =
        quarterLogLatticePoint (k + 1) := by
    rw [neg_neg, Real.exp_log hx]
  have hsecond :
      Real.exp (-(Real.log 2 +
          -Real.log (quarterLogLatticePoint (k + 1)))) =
        quarterLogLatticePoint (k - 3) := by
    rw [show -(Real.log 2 +
        -Real.log (quarterLogLatticePoint (k + 1))) =
          Real.log (quarterLogLatticePoint (k + 1)) - Real.log 2 by ring,
      Real.exp_sub, Real.exp_log hx,
      Real.exp_log (by norm_num : (0 : ℝ) < 2), hhalf]
  unfold monotoneQuarterCutoffCarreMultiplier
    monotoneQuarterCutoffLogMultiplier
  rw [hfirst, hsecond,
    monotoneQuarterStep_eq_one_of_le k (le_rfl),
    monotoneQuarterStep_eq_zero_of_le k
      (quarterLogLatticePoint_mono (by omega : k - 3 ≤ k))]
  norm_num

/-- At the maximally separated log-two boundary point, the real carré
integrand is exactly the signed parent product. -/
theorem monotoneQuarterCutoffCarreIntegrand_logTwo_boundary_re
    (parent : BombieriTest) (k : ℤ) :
    (((monotoneQuarterCutoffCarreMultiplier k (Real.log 2)
          (-Real.log (quarterLogLatticePoint (k + 1))) : ℝ) : ℂ) *
        monotoneQuarterParentLogProduct parent (Real.log 2)
          (-Real.log (quarterLogLatticePoint (k + 1)))).re =
      (monotoneQuarterParentLogProduct parent (Real.log 2)
        (-Real.log (quarterLogLatticePoint (k + 1)))).re := by
  rw [monotoneQuarterCutoffCarreIntegrand_re,
    monotoneQuarterCutoffCarreMultiplier_logTwo_boundary]
  simp

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutoffCommutatorStructural
