import ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotonePropagationCriterionStructural

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutoffEnergyMonotonicityObstructionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# Obstruction to monotonicity of monotone-cutoff energy

The tempting strengthening of one-step sign propagation is

`Q(C_(k+1)(parent)) <= Q(C_k(parent))`.

The exact difference is not a diagonal quantity.  Writing the outer cutoff
as its ratio-two head cell plus the inner suffix gives

`Q(C_k) - Q(C_(k+1)) = Q(cell_k) + 2 Re B(cell_k, C_(k+1))`.

The first term is unconditionally nonnegative, but the second is a signed
global cross.  More sharply, after multiplying the suffix by a real scalar
`a`, the same energy increment is affine in `a`; if the cross is nonzero, an
explicit opposite scalar makes it negative.  Thus nested pointwise cutoff
multipliers do not yield operator monotonicity.

The fixed scalar `a = 1` claim is not refuted here.  Its universal real-parent
form already implies RH, and failure of RH gives an actual adjacent cutoff
counterexample.  Hence cutoff-energy monotonicity is an endgame-strength
claim, not a weaker replacement for the known one-step propagation target.
-/

/-- Energy lost when passing from one outer cutoff to the next inner cutoff. -/
def monotoneCutoffEnergyDrop (parent : BombieriTest) (k : ℤ) : ℝ :=
  bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) -
    bombieriRealQuadraticValue (monotoneQuarterCutoff parent (k + 1))

/-- The relevant universal monotonicity claim, restricted to the
coefficient-conjugation-fixed parents which already suffice for RH. -/
def BombieriRealMonotoneCutoffEnergyDominance : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ, 0 ≤ monotoneCutoffEnergyDrop parent k

/-- A concrete violation of adjacent cutoff-energy monotonicity. -/
def BombieriRealMonotoneCutoffEnergyDominanceFailure : Prop :=
  ∃ (parent : BombieriTest) (k : ℤ),
    bombieriConjugateTest parent = parent ∧
      bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) <
        bombieriRealQuadraticValue
          (monotoneQuarterCutoff parent (k + 1))

/-- The outer cutoff is exactly head cell plus inner suffix. -/
theorem monotoneQuarterCutoff_eq_cell_add_next
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterCutoff parent k =
      monotoneQuarterCell parent k +
        monotoneQuarterCutoff parent (k + 1) := by
  rw [monotoneQuarterCell_eq_cutoff_sub]
  abel

/-- Exact energy-drop formula.  The inner diagonal cancels, leaving the
ratio-two head diagonal and the signed head--suffix global cross. -/
theorem monotoneCutoffEnergyDrop_eq_head_add_two_cross
    (parent : BombieriTest) (k : ℤ) :
    monotoneCutoffEnergyDrop parent k =
      bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
        2 * (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent k)
          (monotoneQuarterCutoff parent (k + 1))).re := by
  unfold monotoneCutoffEnergyDrop bombieriRealQuadraticValue
  rw [monotoneQuarterCutoff_eq_cell_add_next]
  have hexpand := bombieriFunctional_twoBlock_re
    (monotoneQuarterCell parent k)
    (monotoneQuarterCutoff parent (k + 1)) (1 : ℂ)
  have hexpand' :
      (bombieriFunctional
        (bombieriQuadraticTest
          (monotoneQuarterCell parent k +
            monotoneQuarterCutoff parent (k + 1)))).re =
        (bombieriFunctional
          (bombieriQuadraticTest
            (monotoneQuarterCell parent k))).re +
        (bombieriFunctional
          (bombieriQuadraticTest
            (monotoneQuarterCutoff parent (k + 1)))).re +
        2 * (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent k)
          (monotoneQuarterCutoff parent (k + 1))).re := by
    simpa only [one_smul, Complex.normSq_one, one_mul] using hexpand
  rw [hexpand']
  ring

/-- Therefore the fixed monotonicity claim is exactly a one-sided lower bound
on the global cross; head-diagonal positivity alone is insufficient. -/
theorem monotoneCutoffEnergyDrop_nonnegative_iff_cross_lower_bound
    (parent : BombieriTest) (k : ℤ) :
    0 ≤ monotoneCutoffEnergyDrop parent k ↔
      -(bombieriRealQuadraticValue
          (monotoneQuarterCell parent k)) / 2 ≤
        (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent k)
          (monotoneQuarterCutoff parent (k + 1))).re := by
  rw [monotoneCutoffEnergyDrop_eq_head_add_two_cross]
  constructor <;> intro h <;> linarith

/-- The diagonal term in the required cross bound is unconditionally
nonnegative by ratio-two support. -/
theorem bombieriRealQuadraticValue_monotoneQuarterCell_nonnegative
    (parent : BombieriTest) (k : ℤ) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterCell parent k) := by
  unfold bombieriRealQuadraticValue
  exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell
    (monotoneQuarterCell parent k) (monotoneQuarterCell_ratioTwo parent k)

/-! ## The sign-reversible scalar pencil -/

/-- Energy increment from adding the fixed head cell to a real multiple of
the whole suffix. -/
def monotoneHeadSuffixEnergyIncrement
    (parent : BombieriTest) (k : ℤ) (a : ℝ) : ℝ :=
  bombieriRealQuadraticValue
      (monotoneQuarterCell parent k +
        (a : ℂ) • monotoneQuarterCutoff parent (k + 1)) -
    bombieriRealQuadraticValue
      ((a : ℂ) • monotoneQuarterCutoff parent (k + 1))

/-- Exact cancellation of the suffix diagonal: the increment is affine in
the real suffix scalar, with slope twice the signed global cross. -/
theorem monotoneHeadSuffixEnergyIncrement_eq_head_add_two_mul_cross
    (parent : BombieriTest) (k : ℤ) (a : ℝ) :
    monotoneHeadSuffixEnergyIncrement parent k a =
      bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
        2 * a * (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent k)
          (monotoneQuarterCutoff parent (k + 1))).re := by
  unfold monotoneHeadSuffixEnergyIncrement bombieriRealQuadraticValue
  rw [bombieriFunctional_twoBlock_re,
    bombieriFunctional_quadratic_smul]
  norm_num [Complex.normSq_apply, Complex.mul_re]
  ring

/-- The proposed adjacent cutoff monotonicity is precisely the scalar
increment at `a = 1`. -/
theorem monotoneHeadSuffixEnergyIncrement_one_eq_cutoffEnergyDrop
    (parent : BombieriTest) (k : ℤ) :
    monotoneHeadSuffixEnergyIncrement parent k 1 =
      monotoneCutoffEnergyDrop parent k := by
  rw [monotoneHeadSuffixEnergyIncrement_eq_head_add_two_mul_cross,
    monotoneCutoffEnergyDrop_eq_head_add_two_cross]
  ring

/-- If the real head--suffix cross is nonzero, an explicit opposite suffix
scalar makes addition of the head strictly decrease energy. -/
theorem exists_monotoneHeadSuffixEnergyIncrement_negative_of_cross_ne_zero
    (parent : BombieriTest) (k : ℤ)
    (hcross : (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (monotoneQuarterCutoff parent (k + 1))).re ≠ 0) :
    ∃ a : ℝ, monotoneHeadSuffixEnergyIncrement parent k a < 0 := by
  let A : ℝ := bombieriRealQuadraticValue (monotoneQuarterCell parent k)
  let B : ℝ := (bombieriTwoBlockGlobalCrossSymbol
    (monotoneQuarterCell parent k)
    (monotoneQuarterCutoff parent (k + 1))).re
  refine ⟨-(A + 1) / (2 * B), ?_⟩
  rw [monotoneHeadSuffixEnergyIncrement_eq_head_add_two_mul_cross]
  change A + 2 * (-(A + 1) / (2 * B)) * B < 0
  have hB : B ≠ 0 := hcross
  have heq : A + 2 * (-(A + 1) / (2 * B)) * B = -1 := by
    field_simp [hB]
    ring
  rw [heq]
  norm_num

/-- Thus uniform energy monotonicity under every real relative suffix scalar
is equivalent to vanishing of the real head--suffix cross.  This is the exact
sign-reversal obstruction to proving monotonicity merely from nested masks. -/
theorem all_monotoneHeadSuffixEnergyIncrements_nonnegative_iff_cross_eq_zero
    (parent : BombieriTest) (k : ℤ) :
    (∀ a : ℝ, 0 ≤ monotoneHeadSuffixEnergyIncrement parent k a) ↔
      (bombieriTwoBlockGlobalCrossSymbol
        (monotoneQuarterCell parent k)
        (monotoneQuarterCutoff parent (k + 1))).re = 0 := by
  constructor
  · intro hall
    by_contra hcross
    obtain ⟨a, ha⟩ :=
      exists_monotoneHeadSuffixEnergyIncrement_negative_of_cross_ne_zero
        parent k hcross
    exact (not_lt_of_ge (hall a)) ha
  · intro hcross a
    rw [monotoneHeadSuffixEnergyIncrement_eq_head_add_two_mul_cross,
      hcross]
    simpa using
      bombieriRealQuadraticValue_monotoneQuarterCell_nonnegative parent k

/-! ## Logical strength of the fixed cutoff claim -/

/-- Energy dominance implies the already sufficient one-step sign
propagation property. -/
theorem bombieriRealMonotoneCutPropagation_of_cutoffEnergyDominance
    (henergy : BombieriRealMonotoneCutoffEnergyDominance) :
    BombieriRealMonotoneCutPropagation := by
  intro parent hparent k hinner
  have hdrop := henergy parent hparent k
  unfold monotoneCutoffEnergyDrop at hdrop
  linarith

/-- Consequently universal real cutoff-energy dominance already proves RH. -/
theorem riemannHypothesis_of_bombieriRealMonotoneCutoffEnergyDominance
    (zeros : ZetaZeroEnumeration)
    (henergy : BombieriRealMonotoneCutoffEnergyDominance) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_bombieriRealMonotoneCutPropagation zeros
    (bombieriRealMonotoneCutPropagation_of_cutoffEnergyDominance henergy)

/-- If RH fails, the existing adjacent propagation witness is automatically
an actual strict failure of cutoff-energy dominance. -/
theorem realMonotoneCutoffEnergyDominanceFailure_of_not_riemannHypothesis
    (zeros : ZetaZeroEnumeration) (hRH : ¬ RiemannHypothesis) :
    BombieriRealMonotoneCutoffEnergyDominanceFailure := by
  have hfailure :=
    (not_riemannHypothesis_iff_realMonotoneCutPropagationFailure zeros).1 hRH
  obtain ⟨parent, k, hparent, hinner, houter⟩ := hfailure
  refine ⟨parent, k, hparent, ?_⟩
  exact houter.trans_le hinner

/-- In particular RH failure refutes the universal energy-dominance claim. -/
theorem not_bombieriRealMonotoneCutoffEnergyDominance_of_not_riemannHypothesis
    (zeros : ZetaZeroEnumeration) (hRH : ¬ RiemannHypothesis) :
    ¬ BombieriRealMonotoneCutoffEnergyDominance := by
  intro henergy
  exact hRH
    (riemannHypothesis_of_bombieriRealMonotoneCutoffEnergyDominance
      zeros henergy)

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutoffEnergyMonotonicityObstructionStructural
