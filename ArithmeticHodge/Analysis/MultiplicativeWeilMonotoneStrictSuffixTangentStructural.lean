import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneNullSuffixVariationStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotonePropagationReserveStructural

set_option autoImplicit false

open Complex Filter Real Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneStrictSuffixTangentStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneNullSuffixVariationStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open MultiplicativeWeilRealMonotonePropagationReserveStructural

/-!
# Tangent geometry of the strict monotone suffix region

At a monotone boundary let `S = C_(k+1)(parent)`.  The remaining propagation
problem is concentrated on the open region `Q(S) > 0`.  This file computes the
first and second symmetric variations of `Q(S)` along every genuine parent
line.

The resulting tangent cone is the whole parent space: strict positivity of
`Q(S)` persists for sufficiently small real parameters in every direction.
Consequently tangency supplies no inequality involving the head--suffix cross
`X`.  Ratio-two positivity controls only the head--head variation block.  A
small real algebraic model records that these facts do not imply the needed
arithmetic-mean bound `-2 X <= H + T`.

There is also a geometric reason that one cannot manufacture the missing
cross by declaring the head fixed and scaling the suffix independently.  A
genuine parent variation with those two properties forces the original parent
to vanish throughout the open overlap of the head and suffix multipliers.
-/

/-! ## Exact first and second suffix variations -/

/-- Inner suffix energy along a genuine real affine parent line. -/
def monotoneQuarterInnerVariationEnergy
    (parent variation : BombieriTest) (k : ℤ) (a : ℝ) : ℝ :=
  bombieriRealQuadraticValue
    (monotoneQuarterCutoff
      (monotoneQuarterParentVariationLine parent variation a) (k + 1))

/-- Exact quadratic polynomial for the inner suffix energy. -/
theorem monotoneQuarterInnerVariationEnergy_eq
    (parent variation : BombieriTest) (k : ℤ) (a : ℝ) :
    monotoneQuarterInnerVariationEnergy parent variation k a =
      monotoneQuarterSuffixQuadraticValue parent k +
        a ^ 2 * bombieriRealQuadraticValue
          (monotoneQuarterCutoff variation (k + 1)) +
        2 * a * (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCutoff parent (k + 1))
          (monotoneQuarterCutoff variation (k + 1))).re := by
  exact bombieriRealQuadraticValue_cutoff_parentVariationLine_eq
    parent variation (k + 1) a

/-- The symmetric first difference is exactly four times the real suffix
cross, with no remainder term. -/
theorem monotoneQuarterInnerVariationEnergy_sub_neg
    (parent variation : BombieriTest) (k : ℤ) (a : ℝ) :
    monotoneQuarterInnerVariationEnergy parent variation k a -
        monotoneQuarterInnerVariationEnergy parent variation k (-a) =
      4 * a * (bombieriTwoBlockGlobalCrossSymbol
        (monotoneQuarterCutoff parent (k + 1))
        (monotoneQuarterCutoff variation (k + 1))).re := by
  rw [monotoneQuarterInnerVariationEnergy_eq,
    monotoneQuarterInnerVariationEnergy_eq]
  ring

/-- The symmetric second difference sees only the suffix-direction diagonal. -/
theorem monotoneQuarterInnerVariationEnergy_add_neg_sub_two
    (parent variation : BombieriTest) (k : ℤ) (a : ℝ) :
    monotoneQuarterInnerVariationEnergy parent variation k a +
        monotoneQuarterInnerVariationEnergy parent variation k (-a) -
        2 * monotoneQuarterInnerVariationEnergy parent variation k 0 =
      2 * a ^ 2 * bombieriRealQuadraticValue
        (monotoneQuarterCutoff variation (k + 1)) := by
  rw [monotoneQuarterInnerVariationEnergy_eq,
    monotoneQuarterInnerVariationEnergy_eq,
    monotoneQuarterInnerVariationEnergy_eq]
  ring

/-- Membership in the genuine strict-suffix tangent cone: the inner suffix
stays strictly positive on some two-sided interval around the parent. -/
def MonotoneQuarterStrictSuffixTangentDirection
    (parent variation : BombieriTest) (k : ℤ) : Prop :=
  ∃ epsilon : ℝ, 0 < epsilon ∧
    ∀ a : ℝ, |a| < epsilon →
      0 < monotoneQuarterInnerVariationEnergy parent variation k a

/-- A real quadratic which is positive at zero remains positive on a
two-sided interval, with no restriction on its linear or quadratic
coefficients. -/
theorem real_quadratic_strict_tangent_full
    {T : ℝ} (hT : 0 < T) (R Y : ℝ) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ a : ℝ, |a| < epsilon →
        0 < T + a ^ 2 * R + 2 * a * Y := by
  let p : ℝ → ℝ := fun a ↦ T + a ^ 2 * R + 2 * a * Y
  have hpContinuous : Continuous p := by
    dsimp only [p]
    fun_prop
  have hpZero : 0 < p 0 := by
    simpa [p] using hT
  have heventually : ∀ᶠ a in 𝓝 (0 : ℝ), 0 < p a :=
    hpContinuous.continuousAt.eventually_const_lt hpZero
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp heventually
  refine ⟨epsilon, hepsilon, ?_⟩
  intro a ha
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  exact ha

/-- At a strictly positive suffix every genuine parent variation is tangent.
Thus the tangent cone is the full Bombieri-test space, rather than a half-space
which could impose a sign on the head--suffix cross. -/
theorem every_variation_is_strictSuffixTangent
    (parent variation : BombieriTest) (k : ℤ)
    (hstrict : 0 < monotoneQuarterSuffixQuadraticValue parent k) :
    MonotoneQuarterStrictSuffixTangentDirection parent variation k := by
  let R : ℝ := bombieriRealQuadraticValue
    (monotoneQuarterCutoff variation (k + 1))
  let Y : ℝ := (bombieriTwoBlockGlobalCrossSymbol
    (monotoneQuarterCutoff parent (k + 1))
    (monotoneQuarterCutoff variation (k + 1))).re
  obtain ⟨epsilon, hepsilon, hpositive⟩ :=
    real_quadratic_strict_tangent_full hstrict R Y
  refine ⟨epsilon, hepsilon, ?_⟩
  intro a ha
  rw [monotoneQuarterInnerVariationEnergy_eq]
  exact hpositive a ha

/-- Sharp tangent-cone classification at one fixed direction.  Because the
defining interval contains parameter zero, tangency is equivalent to strict
positivity of the original suffix and is completely independent of the
chosen variation. -/
theorem strictSuffixTangentDirection_iff_suffix_pos
    (parent variation : BombieriTest) (k : ℤ) :
    MonotoneQuarterStrictSuffixTangentDirection parent variation k ↔
      0 < monotoneQuarterSuffixQuadraticValue parent k := by
  constructor
  · rintro ⟨epsilon, hepsilon, hpositive⟩
    have hzero := hpositive 0 (by simpa only [abs_zero] using hepsilon)
    rw [monotoneQuarterInnerVariationEnergy_eq] at hzero
    simpa using hzero
  · exact every_variation_is_strictSuffixTangent parent variation k

/-! ## What the head second variation actually controls -/

/-- Head energy along the same genuine parent line. -/
def monotoneQuarterHeadVariationEnergy
    (parent variation : BombieriTest) (k : ℤ) (a : ℝ) : ℝ :=
  bombieriRealQuadraticValue
    (monotoneQuarterCell
      (monotoneQuarterParentVariationLine parent variation a) k)

/-- Exact quadratic polynomial for the ratio-two head energy. -/
theorem monotoneQuarterHeadVariationEnergy_eq
    (parent variation : BombieriTest) (k : ℤ) (a : ℝ) :
    monotoneQuarterHeadVariationEnergy parent variation k a =
      monotoneQuarterHeadQuadraticValue parent k +
        a ^ 2 * bombieriRealQuadraticValue
          (monotoneQuarterCell variation k) +
        2 * a * (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell variation k)).re := by
  unfold monotoneQuarterHeadVariationEnergy
  rw [monotoneQuarterCell_parentVariationLine_eq]
  unfold bombieriRealQuadraticValue
  rw [bombieriFunctional_twoBlock_re]
  simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.mul_re, mul_zero, sub_zero, pow_two,
    mul_assoc, monotoneQuarterHeadQuadraticValue]
  rfl

/-- The head second variation is nonnegative in every direction because it
remains a single ratio-two cell. -/
theorem monotoneQuarterHeadVariationEnergy_nonnegative
    (parent variation : BombieriTest) (k : ℤ) (a : ℝ) :
    0 ≤ monotoneQuarterHeadVariationEnergy parent variation k a := by
  exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell
    (monotoneQuarterCell
      (monotoneQuarterParentVariationLine parent variation a) k)
    (monotoneQuarterCell_ratioTwo
      (monotoneQuarterParentVariationLine parent variation a) k)

/-- Hence the complete head-line information is the head--head determinant
bound.  Notice that its cross contains the varied head, not the inner suffix. -/
theorem strictSuffix_headHead_discriminant
    (parent variation : BombieriTest) (k : ℤ) :
    (bombieriTwoBlockGlobalCrossSymbol
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell variation k)).re ^ 2 ≤
      monotoneQuarterHeadQuadraticValue parent k *
        bombieriRealQuadraticValue (monotoneQuarterCell variation k) := by
  exact monotoneQuarterCell_variation_discriminant parent variation k

/-! ## Algebraic separation from the propagation target -/

/-- Strict suffix openness together with nonnegative head Hessian and the
sharp head discriminant does not imply the arithmetic-mean head--suffix
bound.  The displayed witness has `H = T = P = 1`, zero head first variation,
and `X = -2`; every suffix quadratic direction is locally admissible, while
`-2 X <= H + T` fails strictly. -/
theorem strict_tangent_head_geometry_not_force_propagation_bound :
    ∃ H T X P Z : ℝ,
      0 ≤ H ∧ 0 < T ∧ 0 ≤ P ∧ Z ^ 2 ≤ H * P ∧
      (∀ R Y : ℝ,
        ∃ epsilon : ℝ, 0 < epsilon ∧
          ∀ a : ℝ, |a| < epsilon →
            0 < T + a ^ 2 * R + 2 * a * Y) ∧
      ¬ (-2 * X ≤ H + T) := by
  refine ⟨1, 1, -2, 1, 0, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_, by norm_num⟩
  intro R Y
  exact real_quadratic_strict_tangent_full (by norm_num) R Y

/-! ## An independent suffix direction is not generally realizable -/

/-- A genuine parent direction preserves the head exactly when its boundary
cell vanishes. -/
def MonotoneQuarterHeadPreservingVariation
    (variation : BombieriTest) (k : ℤ) : Prop :=
  monotoneQuarterCell variation k = 0

/-- The head multiplier is strictly positive throughout the open overlap of
the head and next suffix. -/
theorem monotoneQuarterWeight_pos_on_headSuffix_overlap
    (k : ℤ) {x : ℝ}
    (hleft : quarterLogLatticePoint (k + 1) < x)
    (hright : x < quarterLogLatticePoint (k + 2)) :
    0 < monotoneQuarterWeight k x := by
  unfold monotoneQuarterWeight
  rw [monotoneQuarterStep_eq_one_of_le k hleft.le]
  apply sub_pos.mpr
  unfold monotoneQuarterStep
  apply Real.smoothTransition.lt_one_of_lt_one
  rw [div_lt_one (quarterLogLatticePoint_gap_pos (k + 1))]
  have hindex : k + 1 + 1 = k + 2 := by ring
  rw [hindex]
  linarith

/-- If a genuine parent direction fixes the head and scales the suffix by a
nonzero scalar, the original parent must vanish pointwise on the entire open
head--suffix overlap. -/
theorem parent_eq_zero_on_overlap_of_headPreserving_suffixScaling
    (parent variation : BombieriTest) (k : ℤ) (c : ℂ)
    (hhead : MonotoneQuarterHeadPreservingVariation variation k)
    (hscale : monotoneQuarterCutoff variation (k + 1) =
      c • monotoneQuarterCutoff parent (k + 1))
    (hc : c ≠ 0)
    {x : ℝ}
    (hleft : quarterLogLatticePoint (k + 1) < x)
    (hright : x < quarterLogLatticePoint (k + 2)) :
    parent x = 0 := by
  have hvariation : variation x = c * parent x :=
    (cutoff_eq_smul_suffix_iff_eq_right parent variation k c).1
      hscale x hleft
  have hpoint := congrArg (fun f : BombieriTest ↦ f x) hhead
  simp only [monotoneQuarterCell_apply, TestFunction.coe_zero,
    Pi.zero_apply] at hpoint
  have hweight : (monotoneQuarterWeight k x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (monotoneQuarterWeight_pos_on_headSuffix_overlap k hleft hright).ne'
  have hvariationZero : variation x = 0 :=
    (mul_eq_zero.mp hpoint).resolve_left hweight
  rw [hvariation] at hvariationZero
  exact (mul_eq_zero.mp hvariationZero).resolve_left hc

/-- Therefore a parent which is nonzero anywhere in the overlap admits no
head-fixed, independently suffix-scaling tangent direction.  The formal
scalar pencil `H + a S` is not a genuine cutoff variation in this generic
case. -/
theorem no_headPreserving_suffixScalingVariation_of_overlap_nonzero
    (parent : BombieriTest) (k : ℤ) (c : ℂ) (hc : c ≠ 0)
    {x : ℝ}
    (hleft : quarterLogLatticePoint (k + 1) < x)
    (hright : x < quarterLogLatticePoint (k + 2))
    (hparent : parent x ≠ 0) :
    ¬ ∃ variation : BombieriTest,
      MonotoneQuarterHeadPreservingVariation variation k ∧
        monotoneQuarterCutoff variation (k + 1) =
          c • monotoneQuarterCutoff parent (k + 1) := by
  rintro ⟨variation, hhead, hscale⟩
  exact hparent
    (parent_eq_zero_on_overlap_of_headPreserving_suffixScaling
      parent variation k c hhead hscale hc hleft hright)

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneStrictSuffixTangentStructural
