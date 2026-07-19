import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneQuarterPartitionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilParentMaskPositivityStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ArithmeticFunction BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutPrimePhaseStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural

/-!
# Prime phases of two nested monotone cutoffs

At an internal cut the monotone partition turns the head--suffix pencil into
`C_k(parent) + d C_{k+1}(parent)`.  This file expands its prime correlations
without replacing the parent by an absolute-value majorant.  The real phase
mask couples to the real part of the directed parent correlation, while the
antisymmetric phase mask couples with the opposite sign to its imaginary
part.
-/

/-- The actual pencil in two consecutive monotone boundary cutoffs. -/
def monotoneCutPencil
    (parent : BombieriTest) (k : ℤ) (d : ℂ) : BombieriTest :=
  monotoneQuarterCutoff parent k +
    d • monotoneQuarterCutoff parent (k + 1)

/-- Product of the two outer cutoff coefficients. -/
def monotoneCutOuterDiagonalMask (k : ℤ) (x y : ℝ) : ℝ :=
  monotoneQuarterStep k (x * y) * monotoneQuarterStep k y

/-- Product of the two inner cutoff coefficients. -/
def monotoneCutInnerDiagonalMask (k : ℤ) (x y : ℝ) : ℝ :=
  monotoneQuarterStep (k + 1) (x * y) *
    monotoneQuarterStep (k + 1) y

/-- Symmetric mixed coefficient of two consecutive cutoff steps. -/
def monotoneCutSymmetricMask (k : ℤ) (x y : ℝ) : ℝ :=
  monotoneQuarterStep (k + 1) (x * y) * monotoneQuarterStep k y +
    monotoneQuarterStep k (x * y) * monotoneQuarterStep (k + 1) y

/-- Antisymmetric mixed coefficient of two consecutive cutoff steps. -/
def monotoneCutAntisymmetricMask (k : ℤ) (x y : ℝ) : ℝ :=
  monotoneQuarterStep (k + 1) (x * y) * monotoneQuarterStep k y -
    monotoneQuarterStep k (x * y) * monotoneQuarterStep (k + 1) y

/-- Real part of the complete nested-cutoff phase mask. -/
def monotoneCutPhaseRealMask (k : ℤ) (d : ℂ) (x y : ℝ) : ℝ :=
  monotoneCutOuterDiagonalMask k x y +
    Complex.normSq d * monotoneCutInnerDiagonalMask k x y +
    d.re * monotoneCutSymmetricMask k x y

/-- Imaginary part of the complete nested-cutoff phase mask. -/
def monotoneCutPhaseImagMask (k : ℤ) (d : ℂ) (x y : ℝ) : ℝ :=
  d.im * monotoneCutAntisymmetricMask k x y

/-- Complete complex phase mask for the nested-cutoff pencil. -/
def monotoneCutPhaseMask (k : ℤ) (d : ℂ) (x y : ℝ) : ℂ :=
  (monotoneCutPhaseRealMask k d x y : ℂ) +
    Complex.I * (monotoneCutPhaseImagMask k d x y : ℂ)

/-- Directed parent autocorrelation before integration. -/
def monotoneCutParentProduct (parent : BombieriTest) (x y : ℝ) : ℂ :=
  parent (x * y) * starRingEnd ℂ (parent y)

@[simp] theorem monotoneCutPencil_apply
    (parent : BombieriTest) (k : ℤ) (d : ℂ) (x : ℝ) :
    monotoneCutPencil parent k d x =
      ((monotoneQuarterStep k x : ℂ) +
        d * (monotoneQuarterStep (k + 1) x : ℂ)) * parent x := by
  simp only [monotoneCutPencil, TestFunction.coe_add, Pi.add_apply,
    TestFunction.coe_smul, Pi.smul_apply, smul_eq_mul,
    monotoneQuarterCutoff_apply]
  ring

/-- Exact complex coefficient algebra for the two nested steps. -/
theorem monotoneCutCoefficient_mul_conj_eq_phaseMask
    (k : ℤ) (d : ℂ) (x y : ℝ) :
    ((monotoneQuarterStep k (x * y) : ℂ) +
        d * (monotoneQuarterStep (k + 1) (x * y) : ℂ)) *
      starRingEnd ℂ
        ((monotoneQuarterStep k y : ℂ) +
          d * (monotoneQuarterStep (k + 1) y : ℂ)) =
      monotoneCutPhaseMask k d x y := by
  rw [starRingEnd_apply]
  apply Complex.ext <;>
    simp only [monotoneCutPhaseMask, monotoneCutPhaseRealMask,
      monotoneCutPhaseImagMask, monotoneCutOuterDiagonalMask,
      monotoneCutInnerDiagonalMask, monotoneCutSymmetricMask,
      monotoneCutAntisymmetricMask, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im] <;>
    ring

/-- The pencil product is the specialized phase mask times the unchanged
directed parent product. -/
theorem monotoneCutPencil_mul_conj_eq_phaseMask
    (parent : BombieriTest) (k : ℤ) (d : ℂ) (x y : ℝ) :
    monotoneCutPencil parent k d (x * y) *
        starRingEnd ℂ (monotoneCutPencil parent k d y) =
      monotoneCutPhaseMask k d x y *
        monotoneCutParentProduct parent x y := by
  rw [monotoneCutPencil_apply, monotoneCutPencil_apply,
    map_mul (starRingEnd ℂ)]
  unfold monotoneCutParentProduct
  calc
    _ = (((monotoneQuarterStep k (x * y) : ℂ) +
            d * (monotoneQuarterStep (k + 1) (x * y) : ℂ)) *
          starRingEnd ℂ
            ((monotoneQuarterStep k y : ℂ) +
              d * (monotoneQuarterStep (k + 1) y : ℂ))) *
        (parent (x * y) * starRingEnd ℂ (parent y)) := by ring
    _ = _ := by rw [monotoneCutCoefficient_mul_conj_eq_phaseMask]

/-- The complete quadratic test is one specialized parent-mask integral. -/
theorem bombieriQuadraticTest_monotoneCutPencil_apply
    (parent : BombieriTest) (k : ℤ) (d : ℂ) (x : ℝ) :
    bombieriQuadraticTest (monotoneCutPencil parent k d) x =
      ∫ y : ℝ in Set.Ioi 0,
        monotoneCutPhaseMask k d x y *
          monotoneCutParentProduct parent x y := by
  rw [bombieriQuadraticTest_apply]
  unfold autocorrelation
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _hy
  exact monotoneCutPencil_mul_conj_eq_phaseMask parent k d x y

/-- Pointwise real/imaginary phase decomposition.  The antisymmetric mask
couples with a minus sign to the imaginary directed parent correlation. -/
theorem monotoneCutPhaseMask_mul_parentProduct_re
    (parent : BombieriTest) (k : ℤ) (d : ℂ) (x y : ℝ) :
    (monotoneCutPhaseMask k d x y *
        monotoneCutParentProduct parent x y).re =
      monotoneCutPhaseRealMask k d x y *
          (monotoneCutParentProduct parent x y).re -
        monotoneCutPhaseImagMask k d x y *
          (monotoneCutParentProduct parent x y).im := by
  unfold monotoneCutPhaseMask
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- The same identity with all four phase components displayed. -/
theorem monotoneCutPhaseMask_mul_parentProduct_re_explicit
    (parent : BombieriTest) (k : ℤ) (d : ℂ) (x y : ℝ) :
    (monotoneCutPhaseMask k d x y *
        monotoneCutParentProduct parent x y).re =
      monotoneCutOuterDiagonalMask k x y *
          (monotoneCutParentProduct parent x y).re +
        Complex.normSq d * monotoneCutInnerDiagonalMask k x y *
          (monotoneCutParentProduct parent x y).re +
        d.re * monotoneCutSymmetricMask k x y *
          (monotoneCutParentProduct parent x y).re -
        d.im * monotoneCutAntisymmetricMask k x y *
          (monotoneCutParentProduct parent x y).im := by
  rw [monotoneCutPhaseMask_mul_parentProduct_re]
  unfold monotoneCutPhaseRealMask monotoneCutPhaseImagMask
  ring

/-- The signed real phase integral at one positive dilation ratio. -/
def monotoneCutSignedPhaseIntegral
    (parent : BombieriTest) (k : ℤ) (d : ℂ) (x : ℝ) : ℝ :=
  ∫ y : ℝ in Set.Ioi 0,
    monotoneCutPhaseRealMask k d x y *
        (monotoneCutParentProduct parent x y).re -
      monotoneCutPhaseImagMask k d x y *
        (monotoneCutParentProduct parent x y).im

/-- Explicit symmetric/antisymmetric decomposition of the signed integral.
The last summand is the sole imaginary-parent contribution. -/
theorem monotoneCutSignedPhaseIntegral_eq_explicit
    (parent : BombieriTest) (k : ℤ) (d : ℂ) (x : ℝ) :
    monotoneCutSignedPhaseIntegral parent k d x =
      ∫ y : ℝ in Set.Ioi 0,
        monotoneCutOuterDiagonalMask k x y *
            (monotoneCutParentProduct parent x y).re +
          Complex.normSq d * monotoneCutInnerDiagonalMask k x y *
            (monotoneCutParentProduct parent x y).re +
          d.re * monotoneCutSymmetricMask k x y *
            (monotoneCutParentProduct parent x y).re -
          d.im * monotoneCutAntisymmetricMask k x y *
            (monotoneCutParentProduct parent x y).im := by
  unfold monotoneCutSignedPhaseIntegral monotoneCutPhaseRealMask
    monotoneCutPhaseImagMask
  apply integral_congr_ae
  filter_upwards [] with y
  ring

private theorem monotoneCutPhaseIntegrand_integrableOn
    (parent : BombieriTest) (k : ℤ) (d : ℂ) (x : ℝ) :
    IntegrableOn
      (fun y : ℝ ↦ monotoneCutPhaseMask k d x y *
        monotoneCutParentProduct parent x y) (Set.Ioi 0) := by
  let q := monotoneCutPencil parent k d
  have hqContinuous : Continuous (q : ℝ → ℂ) := q.contDiff.continuous
  have hproductContinuous : Continuous (fun y : ℝ ↦
      q (x * y) * starRingEnd ℂ (q y)) := by
    fun_prop
  have hconjCompact : HasCompactSupport (fun y : ℝ ↦
      starRingEnd ℂ (q y)) :=
    q.hasCompactSupport.comp_left (map_zero (starRingEnd ℂ))
  have hproductIntegrable : Integrable (fun y : ℝ ↦
      q (x * y) * starRingEnd ℂ (q y)) :=
    hproductContinuous.integrable_of_hasCompactSupport hconjCompact.mul_left
  have hphaseIntegrable : Integrable (fun y : ℝ ↦
      monotoneCutPhaseMask k d x y *
        monotoneCutParentProduct parent x y) :=
    hproductIntegrable.congr (ae_of_all _ fun y ↦ by
      exact monotoneCutPencil_mul_conj_eq_phaseMask parent k d x y)
  exact hphaseIntegrable.integrableOn

/-- The real part of the quadratic autocorrelation is exactly the signed
real/imaginary parent-correlation integral above. -/
theorem bombieriQuadraticTest_monotoneCutPencil_re_eq_signedPhaseIntegral
    (parent : BombieriTest) (k : ℤ) (d : ℂ) (x : ℝ) :
    (bombieriQuadraticTest (monotoneCutPencil parent k d) x).re =
      monotoneCutSignedPhaseIntegral parent k d x := by
  rw [bombieriQuadraticTest_monotoneCutPencil_apply]
  unfold monotoneCutSignedPhaseIntegral
  have hint := monotoneCutPhaseIntegrand_integrableOn parent k d x
  symm
  calc
    (∫ y : ℝ in Set.Ioi 0,
        monotoneCutPhaseRealMask k d x y *
            (monotoneCutParentProduct parent x y).re -
          monotoneCutPhaseImagMask k d x y *
            (monotoneCutParentProduct parent x y).im) =
        ∫ y : ℝ in Set.Ioi 0,
          (monotoneCutPhaseMask k d x y *
            monotoneCutParentProduct parent x y).re := by
              apply integral_congr_ae
              filter_upwards [] with y
              exact (monotoneCutPhaseMask_mul_parentProduct_re
                parent k d x y).symm
    _ = (∫ y : ℝ in Set.Ioi 0,
        monotoneCutPhaseMask k d x y *
          monotoneCutParentProduct parent x y).re := integral_re hint

/-- The exact signed von-Mangoldt sum of the nested-cutoff phase. -/
def monotoneCutSignedPrimePhaseSum
    (parent : BombieriTest) (k : ℤ) (d : ℂ) : ℝ :=
  ∑' n : ℕ,
    ArithmeticFunction.vonMangoldt (n + 1) *
      (2 * monotoneCutSignedPhaseIntegral parent k d ((n + 1 : ℕ) : ℝ))

/-- The prime contribution is exactly the explicit signed integral/sum. -/
theorem primeSum_bombieriQuadraticTest_monotoneCutPencil_re
    (parent : BombieriTest) (k : ℤ) (d : ℂ) :
    (primeSum (bombieriQuadraticTest
      (monotoneCutPencil parent k d))).re =
        monotoneCutSignedPrimePhaseSum parent k d := by
  unfold primeSum monotoneCutSignedPrimePhaseSum
  change Complex.reCLM
      (∑' n : ℕ, vonMangoldtPrimeSummand
        (bombieriQuadraticTest (monotoneCutPencil parent k d)) n) = _
  rw [Complex.reCLM.map_tsum
    (vonMangoldtPrimeSummand_summable
      (bombieriQuadraticTest (monotoneCutPencil parent k d)))]
  apply tsum_congr
  intro n
  unfold vonMangoldtPrimeSummand
  rw [primeKernel_bombieriQuadraticTest_eq_two_re]
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rw [bombieriQuadraticTest_monotoneCutPencil_re_eq_signedPhaseIntegral]

/-- Exact local-minus-signed-prime formula.  Thus the unresolved global sign
is the displayed von-Mangoldt sum, not pointwise positivity of the cutoff
coefficient matrix. -/
theorem bombieriFunctional_monotoneCutPencil_re_eq_local_sub_signedPrime
    (parent : BombieriTest) (k : ℤ) (d : ℂ) :
    (bombieriFunctional
      (bombieriQuadraticTest (monotoneCutPencil parent k d))).re =
        (bombieriLocalCriticalForm
          (monotoneCutPencil parent k d)
          (monotoneCutPencil parent k d)).re -
        monotoneCutSignedPrimePhaseSum parent k d := by
  have h := congrArg Complex.re
    (bombieriFunctional_quadratic_eq_localCritical_sub_prime
      (monotoneCutPencil parent k d))
  rw [Complex.sub_re,
    primeSum_bombieriQuadraticTest_monotoneCutPencil_re] at h
  exact h

/-! ## Structural signs of the specialized phase mask -/

theorem monotoneCutOuterDiagonalMask_nonnegative
    (k : ℤ) (x y : ℝ) :
    0 ≤ monotoneCutOuterDiagonalMask k x y := by
  unfold monotoneCutOuterDiagonalMask
  exact mul_nonneg (monotoneQuarterStep_nonneg k (x * y))
    (monotoneQuarterStep_nonneg k y)

theorem monotoneCutInnerDiagonalMask_nonnegative
    (k : ℤ) (x y : ℝ) :
    0 ≤ monotoneCutInnerDiagonalMask k x y := by
  unfold monotoneCutInnerDiagonalMask
  exact mul_nonneg (monotoneQuarterStep_nonneg (k + 1) (x * y))
    (monotoneQuarterStep_nonneg (k + 1) y)

theorem monotoneCutSymmetricMask_nonnegative
    (k : ℤ) (x y : ℝ) :
    0 ≤ monotoneCutSymmetricMask k x y := by
  unfold monotoneCutSymmetricMask
  exact add_nonneg
    (mul_nonneg (monotoneQuarterStep_nonneg (k + 1) (x * y))
      (monotoneQuarterStep_nonneg k y))
    (mul_nonneg (monotoneQuarterStep_nonneg k (x * y))
      (monotoneQuarterStep_nonneg (k + 1) y))

/-- At every prime ratio `x ≥ 1`, the nesting of the two consecutive
steps fixes the sign of the antisymmetric mask. -/
theorem monotoneCutAntisymmetricMask_nonnegative
    (k : ℤ) {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) :
    0 ≤ monotoneCutAntisymmetricMask k x y := by
  have hyxy : y ≤ x * y := by nlinarith
  by_cases hmid : y ≤ quarterLogLatticePoint (k + 1)
  · rw [monotoneCutAntisymmetricMask,
      monotoneQuarterStep_eq_zero_of_le (k + 1) hmid]
    simp only [mul_zero, sub_zero]
    exact mul_nonneg (monotoneQuarterStep_nonneg (k + 1) (x * y))
      (monotoneQuarterStep_nonneg k y)
  · have hmid' : quarterLogLatticePoint (k + 1) ≤ y := le_of_not_ge hmid
    have hxmid : quarterLogLatticePoint (k + 1) ≤ x * y :=
      hmid'.trans hyxy
    rw [monotoneCutAntisymmetricMask,
      monotoneQuarterStep_eq_one_of_le k hmid',
      monotoneQuarterStep_eq_one_of_le k hxmid,
      mul_one, one_mul]
    exact sub_nonneg.mpr (monotoneQuarterStep_monotone (k + 1) hyxy)

/-- Completion of the real phase mask into two nested scalar factors plus
the nonnegative imaginary-square diagonal. -/
theorem monotoneCutPhaseRealMask_eq_completed
    (k : ℤ) (d : ℂ) (x y : ℝ) :
    monotoneCutPhaseRealMask k d x y =
      (monotoneQuarterStep k (x * y) +
          d.re * monotoneQuarterStep (k + 1) (x * y)) *
        (monotoneQuarterStep k y +
          d.re * monotoneQuarterStep (k + 1) y) +
      d.im ^ 2 * monotoneCutInnerDiagonalMask k x y := by
  unfold monotoneCutPhaseRealMask monotoneCutOuterDiagonalMask
    monotoneCutInnerDiagonalMask monotoneCutSymmetricMask
  rw [Complex.normSq_apply]
  ring

/-- The real phase mask is pointwise nonnegative throughout the half-plane
`Re d ≥ -1`.  For the original cut parameter `c`, where `d = c - 1`, this
is exactly the right half-plane `Re c ≥ 0`. -/
theorem monotoneCutPhaseRealMask_nonnegative_of_neg_one_le_re
    (k : ℤ) (d : ℂ) (x y : ℝ) (hd : -1 ≤ d.re) :
    0 ≤ monotoneCutPhaseRealMask k d x y := by
  rw [monotoneCutPhaseRealMask_eq_completed]
  have hxNested := monotoneQuarterStep_succ_le k (x * y)
  have hyNested := monotoneQuarterStep_succ_le k y
  have hxFactor : 0 ≤ monotoneQuarterStep k (x * y) +
      d.re * monotoneQuarterStep (k + 1) (x * y) := by
    nlinarith [monotoneQuarterStep_nonneg (k + 1) (x * y)]
  have hyFactor : 0 ≤ monotoneQuarterStep k y +
      d.re * monotoneQuarterStep (k + 1) y := by
    nlinarith [monotoneQuarterStep_nonneg (k + 1) y]
  exact add_nonneg (mul_nonneg hxFactor hyFactor)
    (mul_nonneg (sq_nonneg d.im)
      (monotoneCutInnerDiagonalMask_nonnegative k x y))

theorem monotoneCutPhaseImagMask_nonnegative
    (k : ℤ) (d : ℂ) {x y : ℝ}
    (hx : 1 ≤ x) (hy : 0 ≤ y) (hd : 0 ≤ d.im) :
    0 ≤ monotoneCutPhaseImagMask k d x y := by
  unfold monotoneCutPhaseImagMask
  exact mul_nonneg hd (monotoneCutAntisymmetricMask_nonnegative k hx hy)

/-- At ratio one the antisymmetric phase vanishes exactly. -/
@[simp] theorem monotoneCutAntisymmetricMask_one
    (k : ℤ) (y : ℝ) :
    monotoneCutAntisymmetricMask k 1 y = 0 := by
  unfold monotoneCutAntisymmetricMask
  simp only [one_mul]
  ring

/-! ## Unconditional functional slices -/

/-- The scalar `d = -1` is the physical ratio-two head cell, hence its full
Bombieri quadratic value is unconditionally nonnegative. -/
theorem bombieriFunctional_monotoneCutPencil_neg_one_nonnegative
    (parent : BombieriTest) (k : ℤ) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest
        (monotoneCutPencil parent k (-1)))).re := by
  have hpencil : monotoneCutPencil parent k (-1) =
      monotoneQuarterCell parent k := by
    rw [monotoneQuarterCell_eq_cutoff_sub]
    apply TestFunction.ext
    intro x
    simp only [monotoneCutPencil, TestFunction.coe_add, Pi.add_apply,
      TestFunction.coe_sub, Pi.sub_apply, TestFunction.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [hpencil]
  exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell
    (monotoneQuarterCell parent k)
    (monotoneQuarterCell_ratioTwo parent k)

/-- On the closed head-cell slice, the explicit signed prime phase is
actually dominated by the full local critical energy. -/
theorem monotoneCutSignedPrimePhaseSum_neg_one_le_local
    (parent : BombieriTest) (k : ℤ) :
    monotoneCutSignedPrimePhaseSum parent k (-1) ≤
      (bombieriLocalCriticalForm
        (monotoneCutPencil parent k (-1))
        (monotoneCutPencil parent k (-1))).re := by
  have hvalue := bombieriFunctional_monotoneCutPencil_neg_one_nonnegative
    parent k
  rw [bombieriFunctional_monotoneCutPencil_re_eq_local_sub_signedPrime]
    at hvalue
  linarith

/-- If the next cutoff is already zero, every scalar gives the same terminal
ratio-two head cell, so the entire complex pencil is nonnegative. -/
theorem bombieriFunctional_monotoneCutPencil_nonnegative_of_next_eq_zero
    (parent : BombieriTest) (k : ℤ)
    (hnext : monotoneQuarterCutoff parent (k + 1) = 0)
    (d : ℂ) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest (monotoneCutPencil parent k d))).re := by
  have hpencil : monotoneCutPencil parent k d =
      monotoneQuarterCell parent k := by
    rw [monotoneCutPencil, hnext, smul_zero, add_zero,
      monotoneQuarterCell_eq_cutoff_sub, hnext, sub_zero]
  rw [hpencil]
  exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell
    (monotoneQuarterCell parent k)
    (monotoneQuarterCell_ratioTwo parent k)

/-- If the parent itself already lies in one ratio-two support cell, every
nested-cutoff phase stays in that cell and is therefore nonnegative. -/
theorem bombieriFunctional_monotoneCutPencil_nonnegative_of_ratioTwoParent
    (parent : BombieriTest) (hparent : BombieriRatioTwoCell parent)
    (k : ℤ) (d : ℂ) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest (monotoneCutPencil parent k d))).re := by
  obtain ⟨a, b, ha, hab, hsupport, hratio⟩ := hparent
  apply bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell
  refine ⟨a, b, ha, hab, ?_, hratio⟩
  exact (tsupport_add
      (monotoneQuarterCutoff parent k : ℝ → ℂ)
      (d • monotoneQuarterCutoff parent (k + 1) : BombieriTest)).trans
    (union_subset
      ((tsupport_mul_subset_right :
        tsupport (fun x : ℝ ↦
          (monotoneQuarterStep k x : ℂ) * parent x) ⊆
            tsupport (parent : ℝ → ℂ)).trans hsupport)
      ((tsupport_smul_subset_right (fun _x : ℝ ↦ d)
          (monotoneQuarterCutoff parent (k + 1) : ℝ → ℂ)).trans
        ((tsupport_mul_subset_right :
          tsupport (fun x : ℝ ↦
            (monotoneQuarterStep (k + 1) x : ℂ) * parent x) ⊆
              tsupport (parent : ℝ → ℂ)).trans hsupport)))

/-- For a ratio-two parent, the exact signed prime phase is locally dominated
for every complex nested-cutoff scalar. -/
theorem monotoneCutSignedPrimePhaseSum_le_local_of_ratioTwoParent
    (parent : BombieriTest) (hparent : BombieriRatioTwoCell parent)
    (k : ℤ) (d : ℂ) :
    monotoneCutSignedPrimePhaseSum parent k d ≤
      (bombieriLocalCriticalForm
        (monotoneCutPencil parent k d)
        (monotoneCutPencil parent k d)).re := by
  have hvalue :=
    bombieriFunctional_monotoneCutPencil_nonnegative_of_ratioTwoParent
      parent hparent k d
  rw [bombieriFunctional_monotoneCutPencil_re_eq_local_sub_signedPrime]
    at hvalue
  linarith

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutPrimePhaseStructural
