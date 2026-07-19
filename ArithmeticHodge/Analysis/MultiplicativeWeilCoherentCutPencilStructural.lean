import ArithmeticHodge.Analysis.MultiplicativeWeilPartitionChainCriterionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFejerResidualParentMaskStructural

set_option autoImplicit false

open Complex Finset MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCutPencilStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilCoherentFejerResidualParentMaskStructural

/-!
# A coherent partition cut as one parent-mask pencil

At a selected cut of a coherent quarter-log-lattice partition, the entire
suffix is still one real pointwise mask of the original parent.  Consequently
the required head--suffix pencil has one exact correlated parent-mask
autocorrelation.  Its two phase coordinates are not independent: the real
coordinate multiplies the symmetric head--suffix mask, while the imaginary
coordinate multiplies the antisymmetric mask.

No positivity assumption is used here.
-/

/-- The physical suffix strictly to the right of a selected integer cut. -/
def coherentCutSuffix
    (A : ℤ → BombieriTest) (cut hi : ℤ) : BombieriTest :=
  ∑ k ∈ Finset.Icc (cut + 1) hi, A k

/-- The corresponding finite sum of real partition weights. -/
def coherentCutSuffixMask
    (eta : ℤ → ℝ → ℝ) (cut hi : ℤ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (cut + 1) hi, eta k x

/-- A coherent finite suffix remains a single real mask of the parent. -/
theorem coherentCutSuffix_apply_eq_parentMask
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ)
    (hcommon : ∀ k : ℤ, ∀ x : ℝ,
      A k x = (eta k x : ℂ) * parent x)
    (cut hi : ℤ) (x : ℝ) :
    coherentCutSuffix A cut hi x =
      (coherentCutSuffixMask eta cut hi x : ℂ) * parent x := by
  let ev : BombieriTest →+ ℂ :=
    { toFun := fun f ↦ f x
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change ev (∑ k ∈ Finset.Icc (cut + 1) hi, A k) =
    (↑(∑ k ∈ Finset.Icc (cut + 1) hi, eta k x) : ℂ) * parent x
  rw [map_sum]
  change (∑ k ∈ Finset.Icc (cut + 1) hi, A k x) = _
  simp_rw [hcommon]
  rw [← Finset.sum_mul]
  push_cast
  rfl

/-- The selected cut pencil is pointwise a single complex mask of the common
parent.  The mask is correlated because its two real summands come from the
same partition. -/
theorem coherentCutPencil_apply_eq_parentMask
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ)
    (hcommon : ∀ k : ℤ, ∀ x : ℝ,
      A k x = (eta k x : ℂ) * parent x)
    (cut hi : ℤ) (c : ℂ) (x : ℝ) :
    (A cut + c • coherentCutSuffix A cut hi) x =
      ((eta cut x : ℂ) +
          c * (coherentCutSuffixMask eta cut hi x : ℂ)) * parent x := by
  simp only [TestFunction.coe_add, Pi.add_apply, TestFunction.coe_smul,
    Pi.smul_apply, smul_eq_mul, hcommon,
    coherentCutSuffix_apply_eq_parentMask parent A eta hcommon]
  ring

/-- The diagonal mask of the selected head cell. -/
def coherentCutHeadDiagonalMask
    (eta : ℤ → ℝ → ℝ) (cut : ℤ) (x y : ℝ) : ℝ :=
  eta cut (x * y) * eta cut y

/-- The diagonal mask of the whole selected suffix. -/
def coherentCutSuffixDiagonalMask
    (eta : ℤ → ℝ → ℝ) (cut hi : ℤ) (x y : ℝ) : ℝ :=
  coherentCutSuffixMask eta cut hi (x * y) *
    coherentCutSuffixMask eta cut hi y

/-- The symmetric head--suffix two-point mask. -/
def coherentCutSymmetricMask
    (eta : ℤ → ℝ → ℝ) (cut hi : ℤ) (x y : ℝ) : ℝ :=
  coherentCutSuffixMask eta cut hi (x * y) * eta cut y +
    eta cut (x * y) * coherentCutSuffixMask eta cut hi y

/-- The antisymmetric head--suffix two-point mask.  This is the part seen by
the imaginary phase direction. -/
def coherentCutAntisymmetricMask
    (eta : ℤ → ℝ → ℝ) (cut hi : ℤ) (x y : ℝ) : ℝ :=
  coherentCutSuffixMask eta cut hi (x * y) * eta cut y -
    eta cut (x * y) * coherentCutSuffixMask eta cut hi y

/-- The complete complex two-point mask for the cut pencil. -/
def coherentCutPhaseMask
    (eta : ℤ → ℝ → ℝ) (cut hi : ℤ) (c : ℂ) (x y : ℝ) : ℂ :=
  ((coherentCutHeadDiagonalMask eta cut x y +
      Complex.normSq c * coherentCutSuffixDiagonalMask eta cut hi x y +
      c.re * coherentCutSymmetricMask eta cut hi x y : ℝ) : ℂ) +
    Complex.I *
      ((c.im * coherentCutAntisymmetricMask eta cut hi x y : ℝ) : ℂ)

/-- Exact coefficient algebra behind the correlated mask. -/
theorem coherentCut_coefficient_mul_conj_eq_phaseMask
    (eta : ℤ → ℝ → ℝ) (cut hi : ℤ) (c : ℂ) (x y : ℝ) :
    ((eta cut (x * y) : ℂ) +
        c * (coherentCutSuffixMask eta cut hi (x * y) : ℂ)) *
      starRingEnd ℂ
        ((eta cut y : ℂ) +
          c * (coherentCutSuffixMask eta cut hi y : ℂ)) =
      coherentCutPhaseMask eta cut hi c x y := by
  rw [starRingEnd_apply]
  apply Complex.ext
  · simp only [coherentCutPhaseMask, coherentCutHeadDiagonalMask,
      coherentCutSuffixDiagonalMask, coherentCutSymmetricMask,
      coherentCutAntisymmetricMask, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.I_re, Complex.I_im]
    ring
  · simp only [coherentCutPhaseMask, coherentCutHeadDiagonalMask,
      coherentCutSuffixDiagonalMask, coherentCutSymmetricMask,
      coherentCutAntisymmetricMask, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.I_re, Complex.I_im]
    ring

/-- The entire Bombieri quadratic test of a selected coherent cut pencil is
one parent autocorrelation integral with the explicit phase mask.  This keeps
the test intact before applying the Bombieri functional, so both its local and
prime contributions remain present. -/
theorem bombieriQuadraticTest_coherentCutPencil_apply_eq_parentMask
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ)
    (hcommon : ∀ k : ℤ, ∀ x : ℝ,
      A k x = (eta k x : ℂ) * parent x)
    (cut hi : ℤ) (c : ℂ) (x : ℝ) :
    bombieriQuadraticTest
        (A cut + c • coherentCutSuffix A cut hi) x =
      ∫ y : ℝ in Set.Ioi 0,
        coherentCutPhaseMask eta cut hi c x y *
          (parent (x * y) * starRingEnd ℂ (parent y)) := by
  rw [bombieriQuadraticTest_apply]
  unfold autocorrelation
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _hy
  change
    (A cut + c • coherentCutSuffix A cut hi) (x * y) *
        starRingEnd ℂ ((A cut + c • coherentCutSuffix A cut hi) y) = _
  rw [coherentCutPencil_apply_eq_parentMask parent A eta hcommon,
    coherentCutPencil_apply_eq_parentMask parent A eta hcommon]
  rw [map_mul (starRingEnd ℂ)]
  calc
    _ = (((eta cut (x * y) : ℂ) +
            c * (coherentCutSuffixMask eta cut hi (x * y) : ℂ)) *
          starRingEnd ℂ
            ((eta cut y : ℂ) +
              c * (coherentCutSuffixMask eta cut hi y : ℂ))) *
        (parent (x * y) * starRingEnd ℂ (parent y)) := by ring
    _ = _ := by rw [coherentCut_coefficient_mul_conj_eq_phaseMask]

/-- In a real scalar direction only the symmetric mixed mask survives. -/
theorem coherentCutPhaseMask_ofReal
    (eta : ℤ → ℝ → ℝ) (cut hi : ℤ) (a x y : ℝ) :
    coherentCutPhaseMask eta cut hi (a : ℂ) x y =
      ((coherentCutHeadDiagonalMask eta cut x y +
        a ^ 2 * coherentCutSuffixDiagonalMask eta cut hi x y +
        a * coherentCutSymmetricMask eta cut hi x y : ℝ) : ℂ) := by
  unfold coherentCutPhaseMask
  rw [Complex.normSq_ofReal]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    Complex.ofReal_zero, mul_zero, add_zero]
  push_cast
  ring

/-- In a purely imaginary scalar direction only the antisymmetric mixed mask
survives. -/
theorem coherentCutPhaseMask_mul_I
    (eta : ℤ → ℝ → ℝ) (cut hi : ℤ) (b x y : ℝ) :
    coherentCutPhaseMask eta cut hi ((b : ℂ) * Complex.I) x y =
      ((coherentCutHeadDiagonalMask eta cut x y +
        b ^ 2 * coherentCutSuffixDiagonalMask eta cut hi x y : ℝ) : ℂ) +
        Complex.I *
          ((b * coherentCutAntisymmetricMask eta cut hi x y : ℝ) : ℂ) := by
  have hre : ((b : ℂ) * Complex.I).re = 0 := by simp
  have him : ((b : ℂ) * Complex.I).im = b := by simp
  have hnorm : Complex.normSq ((b : ℂ) * Complex.I) = b ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_I]
    ring
  unfold coherentCutPhaseMask
  rw [hre, him, hnorm]
  simp only [zero_mul, add_zero]

/-- Exact real-phase cut-pencil formula with the symmetric parent mask. -/
theorem bombieriQuadraticTest_coherentCutPencil_ofReal_apply
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ)
    (hcommon : ∀ k : ℤ, ∀ x : ℝ,
      A k x = (eta k x : ℂ) * parent x)
    (cut hi : ℤ) (a x : ℝ) :
    bombieriQuadraticTest
        (A cut + (a : ℂ) • coherentCutSuffix A cut hi) x =
      ∫ y : ℝ in Set.Ioi 0,
        ((coherentCutHeadDiagonalMask eta cut x y +
          a ^ 2 * coherentCutSuffixDiagonalMask eta cut hi x y +
          a * coherentCutSymmetricMask eta cut hi x y : ℝ) : ℂ) *
            (parent (x * y) * starRingEnd ℂ (parent y)) := by
  rw [bombieriQuadraticTest_coherentCutPencil_apply_eq_parentMask
    parent A eta hcommon]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _hy
  change coherentCutPhaseMask eta cut hi (a : ℂ) x y *
    (parent (x * y) * starRingEnd ℂ (parent y)) = _
  rw [coherentCutPhaseMask_ofReal]

/-- Exact imaginary-phase cut-pencil formula with the antisymmetric parent
mask. -/
theorem bombieriQuadraticTest_coherentCutPencil_mul_I_apply
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ)
    (hcommon : ∀ k : ℤ, ∀ x : ℝ,
      A k x = (eta k x : ℂ) * parent x)
    (cut hi : ℤ) (b x : ℝ) :
    bombieriQuadraticTest
        (A cut + ((b : ℂ) * Complex.I) • coherentCutSuffix A cut hi) x =
      ∫ y : ℝ in Set.Ioi 0,
        (((coherentCutHeadDiagonalMask eta cut x y +
          b ^ 2 * coherentCutSuffixDiagonalMask eta cut hi x y : ℝ) : ℂ) +
            Complex.I *
              ((b * coherentCutAntisymmetricMask eta cut hi x y : ℝ) : ℂ)) *
          (parent (x * y) * starRingEnd ℂ (parent y)) := by
  rw [bombieriQuadraticTest_coherentCutPencil_apply_eq_parentMask
    parent A eta hcommon]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _hy
  change coherentCutPhaseMask eta cut hi ((b : ℂ) * Complex.I) x y *
    (parent (x * y) * starRingEnd ℂ (parent y)) = _
  rw [coherentCutPhaseMask_mul_I]

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCutPencilStructural
