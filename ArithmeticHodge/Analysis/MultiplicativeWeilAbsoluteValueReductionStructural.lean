import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutSignDecompositionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilApproximateIdentity
import ArithmeticHodge.Analysis.MultiplicativeWeilPrimeDilationKernelPositive
import ArithmeticHodge.Analysis.MultiplicativeWeilRealLogKernelStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction

namespace ArithmeticHodge.Analysis.MultiplicativeWeilAbsoluteValueReductionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneRealCutSignDecompositionStructural
open MultiplicativeWeilRealLogKernelStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# The exact obstruction to an absolute-value reduction

Pointwise absolute value does not preserve smoothness at a general zero, so
there is no honest operation `BombieriTest -> BombieriTest` obtained by
bundling `x |-> |g x|`.  For two smooth pointwise-disjoint blocks `p,n`,
however, the two genuine Bombieri tests `p - n` and `p + n` have exactly the
same pointwise modulus.  Thus `p - n -> p + n` is the complete realizable
two-block model of what absolute value would do.

The energy gap is four times the full real Bombieri cross.  In logarithmic
coordinates this is four times the archimedean distribution minus the
symmetric Mangoldt atoms.  Consequently either proposed Markov direction is
*exactly* a universal sign assertion for the complete cross; pointwise
lattice geometry supplies no such sign.

The final section records a fully smooth, pointwise-nonnegative, disjoint
factor-two pair for which the first subtracted prime summand is strictly
positive.  This realizes the negative atomic part of the complete kernel and
rules out discarding the Mangoldt atoms in an absolute-value argument.
-/

/-- Two Bombieri tests are pointwise disjoint when at least one vanishes at
every physical point. -/
def BombieriPointwiseDisjoint (p n : BombieriTest) : Prop :=
  forall x : Real, p x = 0 ∨ n x = 0

/-- The smooth signed two-block representative. -/
def bombieriSmoothSignedPair (p n : BombieriTest) : BombieriTest :=
  p - n

/-- The smooth unsigned two-block representative. -/
def bombieriSmoothUnsignedPair (p n : BombieriTest) : BombieriTest :=
  p + n

/-- On pointwise-disjoint blocks, the signed and unsigned smooth
representatives have identical pointwise complex modulus.  No nonsmooth
absolute-value test is introduced. -/
theorem norm_bombieriSmoothSignedPair_eq_norm_unsigned_of_disjoint
    (p n : BombieriTest) (hdisjoint : BombieriPointwiseDisjoint p n)
    (x : Real) :
    ‖bombieriSmoothSignedPair p n x‖ =
      ‖bombieriSmoothUnsignedPair p n x‖ := by
  rcases hdisjoint x with hx | hx
  · simp [bombieriSmoothSignedPair, bombieriSmoothUnsignedPair, hx]
  · simp [bombieriSmoothSignedPair, bombieriSmoothUnsignedPair, hx]

/-- The same realizable modulus identity in squared-modulus form. -/
theorem normSq_bombieriSmoothSignedPair_eq_unsigned_of_disjoint
    (p n : BombieriTest) (hdisjoint : BombieriPointwiseDisjoint p n)
    (x : Real) :
    normSq (bombieriSmoothSignedPair p n x) =
      normSq (bombieriSmoothUnsignedPair p n x) := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    norm_bombieriSmoothSignedPair_eq_norm_unsigned_of_disjoint
      p n hdisjoint x]

/-! ## Exact complete-kernel gap -/

/-- Replacing the signed disjoint two-block representative by its unsigned
counterpart changes the real Bombieri quadratic by exactly four complete
crosses. -/
theorem bombieriRealQuadraticValue_unsigned_sub_signed_eq_four_cross
    (p n : BombieriTest) :
    bombieriRealQuadraticValue (bombieriSmoothUnsignedPair p n) -
        bombieriRealQuadraticValue (bombieriSmoothSignedPair p n) =
      4 * (bombieriTwoBlockGlobalCrossSymbol p n).re := by
  change
    (bombieriFunctional (bombieriQuadraticTest (p + n))).re -
        (bombieriFunctional (bombieriQuadraticTest (p - n))).re = _
  rw [show p + n = p + (1 : Complex) • n by simp,
    bombieriFunctional_twoBlock_re]
  rw [show p - n = p + (-1 : Complex) • n by
      apply TestFunction.ext
      intro x
      simp only [TestFunction.coe_sub, Pi.sub_apply, TestFunction.coe_add,
        Pi.add_apply, TestFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring,
    bombieriFunctional_twoBlock_re]
  norm_num [Complex.mul_re]
  ring

/-- The same gap displayed in the complete real logarithmic kernel. -/
theorem bombieriRealQuadraticValue_unsigned_sub_signed_eq_completeLogKernel
    (p n : BombieriTest) :
    bombieriRealQuadraticValue (bombieriSmoothUnsignedPair p n) -
        bombieriRealQuadraticValue (bombieriSmoothSignedPair p n) =
      4 * bombieriCompleteRealLogKernelCross p n := by
  rw [bombieriRealQuadraticValue_unsigned_sub_signed_eq_four_cross,
    bombieriCompleteRealLogKernelCross_eq_globalCross_re]

/-- Expanded form of the gap: the archimedean logarithmic distribution and
the symmetric Mangoldt atoms enter with opposite signs. -/
theorem bombieriRealQuadraticValue_unsigned_sub_signed_eq_arch_sub_prime
    (p n : BombieriTest) :
    bombieriRealQuadraticValue (bombieriSmoothUnsignedPair p n) -
        bombieriRealQuadraticValue (bombieriSmoothSignedPair p n) =
      4 * (bombieriRealLogArchimedeanCross p n -
        bombieriRealLogPrimeAtomCross p n) := by
  rw [bombieriRealQuadraticValue_unsigned_sub_signed_eq_completeLogKernel]
  rfl

/-- A contraction `Q(unsigned) <= Q(signed)` is exactly nonpositivity of the
complete real cross. -/
theorem bombieriRealQuadraticValue_unsigned_le_signed_iff_cross_nonpos
    (p n : BombieriTest) :
    bombieriRealQuadraticValue (bombieriSmoothUnsignedPair p n) <=
        bombieriRealQuadraticValue (bombieriSmoothSignedPair p n) ↔
      bombieriCompleteRealLogKernelCross p n <= 0 := by
  have hgap :=
    bombieriRealQuadraticValue_unsigned_sub_signed_eq_completeLogKernel p n
  constructor <;> intro h <;> linarith

/-- The reverse inequality is exactly nonnegativity of the complete real
cross.  Hence neither direction follows merely from equality of pointwise
moduli. -/
theorem bombieriRealQuadraticValue_signed_le_unsigned_iff_cross_nonneg
    (p n : BombieriTest) :
    bombieriRealQuadraticValue (bombieriSmoothSignedPair p n) <=
        bombieriRealQuadraticValue (bombieriSmoothUnsignedPair p n) ↔
      0 <= bombieriCompleteRealLogKernelCross p n := by
  have hgap :=
    bombieriRealQuadraticValue_unsigned_sub_signed_eq_completeLogKernel p n
  constructor <;> intro h <;> linarith

/-! ## A smooth disjoint pair carrying a strict negative prime cost -/

/-- A sufficiently separated factor-two dilation is pointwise disjoint from
the original smooth block. -/
theorem bombieriPointwiseDisjoint_normalizedDilation_two
    (g : BombieriTest) {a b : Real}
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hsep : b < 2 * a) :
    BombieriPointwiseDisjoint g
      (normalizedDilation 2 (by norm_num) g) := by
  intro x
  by_cases hx : g x = 0
  · exact Or.inl hx
  · right
    rw [normalizedDilation_apply]
    have hxmem : x ∈ Set.Icc a b :=
      hsupport (subset_tsupport g (Function.mem_support.mpr hx))
    have htwo : g (2 * x) = 0 := by
      by_contra hne
      have htwomem : 2 * x ∈ Set.Icc a b :=
        hsupport (subset_tsupport g (Function.mem_support.mpr hne))
      have htwoa : 2 * a ≤ 2 * x :=
        mul_le_mul_of_nonneg_left hxmem.1 (by norm_num)
      exact (not_le_of_gt hsep) (htwoa.trans htwomem.2)
    rw [htwo, mul_zero]

/-- Normalized dilation preserves the real pointwise-nonnegative cone. -/
theorem bombieriPointwiseNonnegative_normalizedDilation
    (lambda : Real) (hlambda : 0 < lambda) (g : BombieriTest)
    (hg : BombieriPointwiseNonnegative g) :
    BombieriPointwiseNonnegative (normalizedDilation lambda hlambda g) := by
  constructor
  · apply TestFunction.ext
    intro x
    have hvalue := congrArg (fun q : BombieriTest => q (lambda * x)) hg.1
    simp only [bombieriConjugateTest_apply] at hvalue
    simp only [bombieriConjugateTest_apply, normalizedDilation_apply,
      map_mul, Complex.conj_ofReal]
    rw [hvalue]
  · intro x
    rw [normalizedDilation_apply]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (hg.2 (lambda * x))

/-- The first Mangoldt summand in the mixed prime test of a nonzero
factor-two pair is strictly positive.  Since the full Bombieri form subtracts
the prime functional, its contribution to the unsigned-minus-signed gap is
strictly negative. -/
theorem neg_two_mul_firstPrimeSummand_re_lt_zero
    (g : BombieriTest) {a b : Real}
    (hg : g ≠ 0) (ha : 0 < a)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a <= 2) :
    -2 * (vonMangoldtPrimeSummand
      (bombieriQuadraticCrossTest g
        (normalizedDilation 2 (by norm_num) g)) 1).re < 0 := by
  have hkernel :=
    primeKernel_bombieriQuadraticCrossTest_dilation_two_re_pos
      g hg ha hsupport hratio
  have hlog : 0 < ArithmeticFunction.vonMangoldt 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime
      (by norm_num : Nat.Prime 2)]
    exact Real.log_pos (by norm_num)
  unfold vonMangoldtPrimeSummand
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  nlinarith

/-- Any nonzero nonnegative smooth block of support ratio strictly below two
therefore gives a genuine smooth modulus flip with a strict negative `n=2`
arithmetic contribution. -/
theorem smooth_disjoint_absoluteFlip_has_negative_firstPrimeCost
    (g : BombieriTest) {a b : Real}
    (hg : g ≠ 0) (ha : 0 < a)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hsep : b < 2 * a)
    (hnonneg : BombieriPointwiseNonnegative g) :
    BombieriPointwiseNonnegative g ∧
      BombieriPointwiseNonnegative
        (normalizedDilation 2 (by norm_num) g) ∧
      BombieriPointwiseDisjoint g
        (normalizedDilation 2 (by norm_num) g) ∧
      (forall x : Real,
        ‖bombieriSmoothSignedPair g
          (normalizedDilation 2 (by norm_num) g) x‖ =
        ‖bombieriSmoothUnsignedPair g
          (normalizedDilation 2 (by norm_num) g) x‖) ∧
      -2 * (vonMangoldtPrimeSummand
        (bombieriQuadraticCrossTest g
          (normalizedDilation 2 (by norm_num) g)) 1).re < 0 := by
  have hdisjoint :=
    bombieriPointwiseDisjoint_normalizedDilation_two g hsupport hsep
  have hratio : b / a <= 2 := by
    rw [div_le_iff₀ ha]
    exact hsep.le
  exact ⟨hnonneg,
    bombieriPointwiseNonnegative_normalizedDilation
      2 (by norm_num) g hnonneg,
    hdisjoint,
    norm_bombieriSmoothSignedPair_eq_norm_unsigned_of_disjoint
      g (normalizedDilation 2 (by norm_num) g) hdisjoint,
    neg_two_mul_firstPrimeSummand_re_lt_zero
      g hg ha hsupport hratio⟩

/-- Such smooth disjoint nonnegative modulus flips really exist.  A narrow
standard Bombieri bump near one and its factor-two normalized dilation give
an unconditional witness to every hypothesis of the preceding theorem. -/
theorem exists_smooth_disjoint_absoluteFlip_with_negative_firstPrimeCost :
    ∃ (g : BombieriTest) (a b : ℝ),
      g ≠ 0 ∧ 0 < a ∧
      tsupport g ⊆ Set.Icc a b ∧ b < 2 * a ∧
      BombieriPointwiseNonnegative g ∧
      BombieriPointwiseNonnegative
        (normalizedDilation 2 (by norm_num) g) ∧
      BombieriPointwiseDisjoint g
        (normalizedDilation 2 (by norm_num) g) ∧
      (∀ x : ℝ,
        ‖bombieriSmoothSignedPair g
          (normalizedDilation 2 (by norm_num) g) x‖ =
        ‖bombieriSmoothUnsignedPair g
          (normalizedDilation 2 (by norm_num) g) x‖) ∧
      -2 * (vonMangoldtPrimeSummand
        (bombieriQuadraticCrossTest g
          (normalizedDilation 2 (by norm_num) g)) 1).re < 0 := by
  let epsilon : ℝ := 1 / 1000
  have hepsilon : 0 < epsilon := by norm_num [epsilon]
  obtain ⟨g, hgOne, hsupportOpen, hreal⟩ :=
    exists_bombieri_bump_log_near_one epsilon hepsilon
  let a : ℝ := Real.exp (-epsilon)
  let b : ℝ := Real.exp epsilon
  have ha : 0 < a := Real.exp_pos _
  have hsupport : tsupport g ⊆ Set.Icc a b := by
    exact hsupportOpen.trans Set.Ioo_subset_Icc_self
  have hexpUpper : Real.exp epsilon ≤ 1 / (1 - epsilon) :=
    Real.exp_bound_div_one_sub_of_interval hepsilon.le (by
      norm_num [epsilon])
  have hexpNegLower : 1 - epsilon ≤ Real.exp (-epsilon) :=
    Real.one_sub_le_exp_neg epsilon
  have hsep : b < 2 * a := by
    calc
      b = Real.exp epsilon := rfl
      _ ≤ 1 / (1 - epsilon) := hexpUpper
      _ < 2 * (1 - epsilon) := by norm_num [epsilon]
      _ ≤ 2 * Real.exp (-epsilon) := by linarith
      _ = 2 * a := rfl
  have hg : g ≠ 0 := by
    intro hzero
    have hvalue := congrArg (fun q : BombieriTest ↦ q 1) hzero
    change g 1 = (0 : BombieriTest) 1 at hvalue
    rw [hgOne] at hvalue
    simp at hvalue
  have hfixed : bombieriConjugateTest g = g := by
    apply TestFunction.ext
    intro x
    simp only [bombieriConjugateTest_apply]
    apply Complex.ext
    · simp
    · rw [starRingEnd_apply]
      simp only [Complex.star_def, Complex.conj_im]
      rw [(hreal x).2.2]
      simp
  have hnonneg : BombieriPointwiseNonnegative g :=
    ⟨hfixed, fun x ↦ (hreal x).1⟩
  have hwitness := smooth_disjoint_absoluteFlip_has_negative_firstPrimeCost
    g hg ha hsupport hsep hnonneg
  exact ⟨g, a, b, hg, ha, hsupport, hsep, hwitness⟩

end

end ArithmeticHodge.Analysis.MultiplicativeWeilAbsoluteValueReductionStructural
