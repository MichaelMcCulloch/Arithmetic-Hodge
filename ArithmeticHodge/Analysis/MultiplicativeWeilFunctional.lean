/-
  Bombieri's concrete multiplicative Weil functional.

  This assembles the two polar Mellin values, the finite von Mangoldt sum,
  and the convergent real-space archimedean contribution with the signs and
  normalization of Bombieri, *Remarks on Weil's quadratic functional*, p. 186.
-/

import ArithmeticHodge.Analysis.MultiplicativeWeilTranspose
import ArithmeticHodge.Analysis.MultiplicativeWeilPrime
import ArithmeticHodge.Analysis.MultiplicativeWeilArchimedean
import ArithmeticHodge.Analysis.MultiplicativeWeilZeroSummability

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- Mellin evaluation at a fixed complex argument as a complex-linear
functional on Bombieri tests. -/
def mellinLinearMap (s : ℂ) : BombieriTest →ₗ[ℂ] ℂ where
  toFun f := mellin (f : ℝ → ℂ) s
  map_add' f g := by
    exact (hasMellin_add (BombieriTest.mellinConvergent f s)
      (BombieriTest.mellinConvergent g s)).2
  map_smul' c f := by
    simpa only [smul_eq_mul] using
      (hasMellin_const_smul (BombieriTest.mellinConvergent f s) c).2

@[simp]
theorem mellinLinearMap_apply (s : ℂ) (f : BombieriTest) :
    mellinLinearMap s f = mellin (f : ℝ → ℂ) s := rfl

/-- The two polar terms `M f(1) + M f(0)`. -/
def bombieriPolarLinearMap : BombieriTest →ₗ[ℂ] ℂ :=
  mellinLinearMap 1 + mellinLinearMap 0

@[simp]
theorem bombieriPolarLinearMap_apply (f : BombieriTest) :
    bombieriPolarLinearMap f =
      mellin (f : ℝ → ℂ) 1 + mellin (f : ℝ → ℂ) 0 := rfl

/-- The polar contribution is invariant under Bombieri's transpose. -/
theorem bombieriPolarLinearMap_transpose (f : BombieriTest) :
    bombieriPolarLinearMap (transposeLinearMap f) =
      bombieriPolarLinearMap f := by
  have hfun : ((transposeLinearMap f : BombieriTest) : ℝ → ℂ) =
      transpose (f : ℝ → ℂ) := by
    funext x
    exact transposeLinearMap_apply f x
  simp only [bombieriPolarLinearMap_apply, hfun, mellin_transpose]
  ring_nf

/-- The real archimedean integrand is pointwise transpose-invariant on the
positive half-line. -/
theorem bombieriArchIntegrand_transpose (f : BombieriTest)
    {x : ℝ} (hx : 0 < x) :
    bombieriArchIntegrand (transposeLinearMap f) x =
      bombieriArchIntegrand f x := by
  have hfun : ((transposeLinearMap f : BombieriTest) : ℝ → ℂ) =
      transpose (f : ℝ → ℂ) := by
    funext y
    exact transposeLinearMap_apply f y
  rw [bombieriArchIntegrand, bombieriArchIntegrand]
  rw [transposeLinearMap_apply f x, transposeLinearMap_apply f 1, hfun,
    transpose_involutive_on_pos (f : ℝ → ℂ) hx,
    transpose_apply_of_pos (f : ℝ → ℂ) (by norm_num : (0 : ℝ) < 1)]
  norm_num
  ring_nf

/-- The full archimedean contribution is transpose-invariant. -/
theorem bombieriArchTerm_transpose (f : BombieriTest) :
    bombieriArchTerm (transposeLinearMap f) = bombieriArchTerm f := by
  rw [bombieriArchTerm, bombieriArchTerm]
  have hone : transposeLinearMap f 1 = f 1 := by
    rw [transposeLinearMap_apply,
      transpose_apply_of_pos (f : ℝ → ℂ) (by norm_num : (0 : ℝ) < 1)]
    norm_num
  rw [hone]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact bombieriArchIntegrand_transpose f (zero_lt_one.trans hx)

/-- Bombieri's concrete multiplicative Weil functional. -/
def bombieriFunctional : BombieriTest →ₗ[ℂ] ℂ :=
  bombieriPolarLinearMap - primeSumLinearMap + bombieriArchTermLinearMap

@[simp]
theorem bombieriFunctional_apply (f : BombieriTest) :
    bombieriFunctional f =
      mellin (f : ℝ → ℂ) 1 + mellin (f : ℝ → ℂ) 0 - primeSum f +
        bombieriArchTerm f := rfl

/-- The concrete Bombieri functional is transpose-invariant. -/
theorem bombieriFunctional_transpose (f : BombieriTest) :
    bombieriFunctional (transposeLinearMap f) = bombieriFunctional f := by
  simp only [bombieriFunctional_apply, primeSum_transposeLinearMap,
    bombieriArchTerm_transpose]
  have hfun : ((transposeLinearMap f : BombieriTest) : ℝ → ℂ) =
      transpose (f : ℝ → ℂ) := by
    funext x
    exact transposeLinearMap_apply f x
  simp only [hfun, mellin_transpose]
  ring_nf

/-- Given an exhaustive analytic-multiplicity zero enumeration, the remaining
source-level explicit-formula assertion after constructing the concrete
functional, proving its transpose symmetry, and proving absolute convergence
of the zero side. -/
def BombieriZeroSumFormula (zeros : ZetaZeroEnumeration) : Prop :=
  ∀ f : BombieriTest,
    bombieriFunctional f =
      ∑' n, mellin (f : ℝ → ℂ) (zeros.zero n).val

/-- The zero-sum identity supplies the generic explicit-formula interface;
transpose symmetry is already a theorem of the concrete functional. -/
theorem bombieriZeroSumFormula_to_explicitFormula
    (zeros : ZetaZeroEnumeration) (h : BombieriZeroSumFormula zeros) :
    BombieriExplicitFormula bombieriFunctional canonicalTransposeData zeros := by
  intro f
  exact ⟨zeros.mellin_summable f,
    (bombieriFunctional_transpose f).symm, h f⟩

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
