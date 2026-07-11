import ArithmeticHodge.Analysis.MultiplicativeWeilPrime
import ArithmeticHodge.Analysis.MultiplicativeWeilArchimedean

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil.FunctionalScratch

noncomputable section

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

def evaluationLinearMap (x : ℝ) : BombieriTest →ₗ[ℂ] ℂ where
  toFun f := f x
  map_add' f g := by simp
  map_smul' c f := by simp

@[simp]
theorem evaluationLinearMap_apply (x : ℝ) (f : BombieriTest) :
    evaluationLinearMap x f = f x := rfl

def polarLinearMap : BombieriTest →ₗ[ℂ] ℂ :=
  mellinLinearMap 1 + mellinLinearMap 0

@[simp]
theorem polarLinearMap_apply (f : BombieriTest) :
    polarLinearMap f = mellin (f : ℝ → ℂ) 1 + mellin (f : ℝ → ℂ) 0 := rfl

theorem polarLinearMap_transpose (f : BombieriTest) :
    polarLinearMap (transposeLinearMap f) = polarLinearMap f := by
  have hfun : ((transposeLinearMap f : BombieriTest) : ℝ → ℂ) =
      transpose (f : ℝ → ℂ) := by
    funext x
    exact transposeLinearMap_apply f x
  simp only [polarLinearMap_apply, hfun, mellin_transpose]
  ring

def archConstant : ℂ :=
  (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℝ)

def archTermLinearMap : BombieriTest →ₗ[ℂ] ℂ :=
  (-archConstant) • evaluationLinearMap 1 - bombieriArchIntegralLinearMap

@[simp]
theorem archTermLinearMap_apply (f : BombieriTest) :
    archTermLinearMap f = bombieriArchTerm f := by
  rfl

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
  ring

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

def bombieriFunctional : BombieriTest →ₗ[ℂ] ℂ :=
  polarLinearMap - primeSumLinearMap + archTermLinearMap

@[simp]
theorem bombieriFunctional_apply (f : BombieriTest) :
    bombieriFunctional f =
      mellin (f : ℝ → ℂ) 1 + mellin (f : ℝ → ℂ) 0 - primeSum f +
        bombieriArchTerm f := by
  rfl

theorem bombieriFunctional_transpose (f : BombieriTest) :
    bombieriFunctional (transposeLinearMap f) = bombieriFunctional f := by
  simp only [bombieriFunctional_apply, polarLinearMap_apply,
    primeSum_transposeLinearMap, bombieriArchTerm_transpose]
  have hfun : ((transposeLinearMap f : BombieriTest) : ℝ → ℂ) =
      transpose (f : ℝ → ℂ) := by
    funext x
    exact transposeLinearMap_apply f x
  simp only [hfun, mellin_transpose]
  ring

#print axioms mellinLinearMap
#print axioms polarLinearMap_transpose
#print axioms bombieriArchTerm_transpose
#print axioms bombieriFunctional
#print axioms bombieriFunctional_transpose

end


end ArithmeticHodge.Analysis.MultiplicativeWeil.FunctionalScratch
