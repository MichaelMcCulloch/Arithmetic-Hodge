import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeCoherentAggregationStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeFejerDecompositionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFejerResidualCrossTestStructural

set_option autoImplicit false

open Complex Finset MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFejerResidualParentMaskStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilFejerLocalizationStructural
open MultiplicativeWeilFejerLinearResidualStructural
open MultiplicativeWeilFejerResidualCrossTestStructural
open MultiplicativeWeilQuarterLogLatticeFejerAssemblyStructural
open MultiplicativeWeilQuarterLogLatticeFejerDecompositionStructural

/-- The production Fejer residual is the Bombieri functional of one concrete
finite cross-test sum. -/
theorem fejerResidual_eq_functional_crossTestSum_re
    (cells : List BombieriTest) :
    bombieriWeightedLinearLagCross
        bombieriFejerThreeResidualLagWeight cells =
      (bombieriFunctional
        (bombieriWeightedLinearLagCrossTest
          bombieriFejerThreeResidualLagWeight cells)).re := by
  exact (bombieriFunctional_weightedLinearLagCrossTest_re
    bombieriFejerThreeResidualLagWeight cells).symm

/-! ## One common-parent mask -/

def CoherentWith
    (parent f : BombieriTest) (eta : ℝ → ℝ) : Prop :=
  ∀ z : ℝ, f z = ((eta z : ℝ) : ℂ) * parent z

def pairSymmetricLagMask
    (c : ℝ) (eta theta : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (c / 2) *
    (eta (x * y) * theta y + theta (x * y) * eta y)

def headSymmetricLagMask
    (w : ℕ → ℝ) (eta : ℝ → ℝ) :
    ℕ → List (ℝ → ℝ) → ℝ → ℝ → ℝ
  | _k, [], _x, _y => 0
  | k, theta :: tail, x, y =>
      pairSymmetricLagMask (w k) eta theta x y +
        headSymmetricLagMask w eta (k + 1) tail x y

def symmetricLinearLagMask
    (w : ℕ → ℝ) :
    List (ℝ → ℝ) → ℝ → ℝ → ℝ
  | [], _x, _y => 0
  | eta :: tail, x, y =>
      headSymmetricLagMask w eta 1 tail x y +
        symmetricLinearLagMask w tail x y

def parentMaskedIntegrand
    (parent : BombieriTest) (mask : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℂ :=
  ((mask x y : ℝ) : ℂ) *
    (parent (x * y) * starRingEnd ℂ (parent y))

private theorem directedIntegrand_integrableOn
    (f g : BombieriTest) (x : ℝ) :
    IntegrableOn
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (g y))
      (Set.Ioi 0) := by
  have hcont : Continuous
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (g y)) := by
    fun_prop
  have hgcompact : HasCompactSupport
      (fun y : ℝ ↦ starRingEnd ℂ (g y)) := by
    exact g.hasCompactSupport.comp_left (by simp)
  have hcompact : HasCompactSupport
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (g y)) := by
    simpa only [Pi.mul_apply] using
      hgcompact.mul_left (f := fun y : ℝ ↦ f (x * y))
  exact (hcont.integrable_of_hasCompactSupport hcompact).integrableOn

private theorem pairMask_integrableOn
    (c : ℝ) (parent f g : BombieriTest) (eta theta : ℝ → ℝ)
    (hf : CoherentWith parent f eta) (hg : CoherentWith parent g theta)
    (x : ℝ) :
    IntegrableOn
      (parentMaskedIntegrand parent
        (pairSymmetricLagMask c eta theta) x)
      (Set.Ioi 0) := by
  have hphysical : IntegrableOn
      (fun y : ℝ ↦ ((c / 2 : ℝ) : ℂ) *
        (f (x * y) * starRingEnd ℂ (g y) +
          g (x * y) * starRingEnd ℂ (f y)))
      (Set.Ioi 0) :=
    ((directedIntegrand_integrableOn f g x).add
      (directedIntegrand_integrableOn g f x)).const_mul _
  refine IntegrableOn.congr_fun hphysical ?_ measurableSet_Ioi
  intro y _hy
  change ((c / 2 : ℝ) : ℂ) *
      (f (x * y) * starRingEnd ℂ (g y) +
        g (x * y) * starRingEnd ℂ (f y)) = _
  unfold parentMaskedIntegrand pairSymmetricLagMask
  rw [hf (x * y), hg y, hg (x * y), hf y]
  have hstarEta :
      starRingEnd ℂ (((eta y : ℝ) : ℂ) * parent y) =
        ((eta y : ℝ) : ℂ) * starRingEnd ℂ (parent y) := by
    rw [map_mul, Complex.conj_ofReal]
  have hstarTheta :
      starRingEnd ℂ (((theta y : ℝ) : ℂ) * parent y) =
        ((theta y : ℝ) : ℂ) * starRingEnd ℂ (parent y) := by
    rw [map_mul, Complex.conj_ofReal]
  rw [hstarEta, hstarTheta]
  push_cast
  ring

private theorem weightedCrossTest_apply_eq_pairMaskIntegral
    (c : ℝ) (parent f g : BombieriTest) (eta theta : ℝ → ℝ)
    (hf : CoherentWith parent f eta) (hg : CoherentWith parent g theta)
    (x : ℝ) :
    ((((c / 2 : ℝ) : ℂ) • bombieriQuadraticCrossTest f g) :
        BombieriTest) x =
      ∫ y : ℝ in Set.Ioi 0,
        parentMaskedIntegrand parent
          (pairSymmetricLagMask c eta theta) x y := by
  simp only [TestFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [bombieriQuadraticCrossTest_apply]
  unfold bombieriDirectedCorrelation
  rw [← MeasureTheory.integral_add
    (directedIntegrand_integrableOn f g x)
    (directedIntegrand_integrableOn g f x)]
  calc
    _ = ∫ y : ℝ in Set.Ioi 0,
        ((c / 2 : ℝ) : ℂ) *
          (f (x * y) * starRingEnd ℂ (g y) +
            g (x * y) * starRingEnd ℂ (f y)) := by
      exact (MeasureTheory.integral_const_mul _ _).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _hy
      change ((c / 2 : ℝ) : ℂ) *
          (f (x * y) * starRingEnd ℂ (g y) +
            g (x * y) * starRingEnd ℂ (f y)) = _
      unfold parentMaskedIntegrand pairSymmetricLagMask
      rw [hf (x * y), hg y, hg (x * y), hf y]
      have hstarEta :
          starRingEnd ℂ (((eta y : ℝ) : ℂ) * parent y) =
            ((eta y : ℝ) : ℂ) * starRingEnd ℂ (parent y) := by
        rw [map_mul, Complex.conj_ofReal]
      have hstarTheta :
          starRingEnd ℂ (((theta y : ℝ) : ℂ) * parent y) =
            ((theta y : ℝ) : ℂ) * starRingEnd ℂ (parent y) := by
        rw [map_mul, Complex.conj_ofReal]
      rw [hstarEta, hstarTheta]
      push_cast
      ring

private theorem headMask_integrable_and_test_eq
    (w : ℕ → ℝ) (parent f : BombieriTest) (eta : ℝ → ℝ)
    (hf : CoherentWith parent f eta) (k : ℕ)
    {cells : List BombieriTest} {etas : List (ℝ → ℝ)}
    (hrel : List.Forall₂ (CoherentWith parent) cells etas)
    (x : ℝ) :
    IntegrableOn
        (parentMaskedIntegrand parent
          (headSymmetricLagMask w eta k etas) x)
        (Set.Ioi 0) ∧
      (bombieriHeadWeightedLagCrossTest w f k cells : BombieriTest) x =
        ∫ y : ℝ in Set.Ioi 0,
          parentMaskedIntegrand parent
            (headSymmetricLagMask w eta k etas) x y := by
  induction hrel generalizing k with
  | nil =>
      constructor
      · refine IntegrableOn.congr_fun
          (integrableOn_zero : IntegrableOn
            (fun _y : ℝ ↦ (0 : ℂ)) (Set.Ioi 0)) ?_ measurableSet_Ioi
        intro y _hy
        simp [headSymmetricLagMask, parentMaskedIntegrand]
      · simp [bombieriHeadWeightedLagCrossTest, headSymmetricLagMask,
          parentMaskedIntegrand]
  | @cons g theta cells etas hg htail ih =>
      have hpair := pairMask_integrableOn (w k) parent f g eta theta hf hg x
      have hrest := ih (k + 1)
      constructor
      · refine IntegrableOn.congr_fun (hpair.add hrest.1) ?_ measurableSet_Ioi
        intro y _hy
        simp only [headSymmetricLagMask, parentMaskedIntegrand,
          Complex.ofReal_add, Pi.add_apply]
        ring
      · simp only [bombieriHeadWeightedLagCrossTest,
          TestFunction.coe_add, Pi.add_apply]
        rw [weightedCrossTest_apply_eq_pairMaskIntegral
          (w k) parent f g eta theta hf hg x, hrest.2]
        rw [← MeasureTheory.integral_add hpair hrest.1]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y _hy
        simp only [headSymmetricLagMask, parentMaskedIntegrand,
          Complex.ofReal_add]
        ring

private theorem mask_integrable_and_test_eq
    (w : ℕ → ℝ) (parent : BombieriTest)
    {cells : List BombieriTest} {etas : List (ℝ → ℝ)}
    (hrel : List.Forall₂ (CoherentWith parent) cells etas)
    (x : ℝ) :
    IntegrableOn
        (parentMaskedIntegrand parent
          (symmetricLinearLagMask w etas) x)
        (Set.Ioi 0) ∧
      (bombieriWeightedLinearLagCrossTest w cells : BombieriTest) x =
        ∫ y : ℝ in Set.Ioi 0,
          parentMaskedIntegrand parent
            (symmetricLinearLagMask w etas) x y := by
  induction hrel with
  | nil =>
      constructor
      · refine IntegrableOn.congr_fun
          (integrableOn_zero : IntegrableOn
            (fun _y : ℝ ↦ (0 : ℂ)) (Set.Ioi 0)) ?_ measurableSet_Ioi
        intro y _hy
        simp [symmetricLinearLagMask, parentMaskedIntegrand]
      · simp [bombieriWeightedLinearLagCrossTest, symmetricLinearLagMask,
          parentMaskedIntegrand]
  | @cons f eta cells etas hf htail ih =>
      have hhead := headMask_integrable_and_test_eq
        w parent f eta hf 1 htail x
      constructor
      · refine IntegrableOn.congr_fun (hhead.1.add ih.1) ?_ measurableSet_Ioi
        intro y _hy
        simp only [symmetricLinearLagMask, parentMaskedIntegrand,
          Complex.ofReal_add, Pi.add_apply]
        ring
      · simp only [bombieriWeightedLinearLagCrossTest,
          TestFunction.coe_add, Pi.add_apply]
        rw [hhead.2, ih.2]
        rw [← MeasureTheory.integral_add hhead.1 ih.1]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y _hy
        simp only [symmetricLinearLagMask, parentMaskedIntegrand,
          Complex.ofReal_add]
        ring

/-- Exact test-function parent-mask identity for any coherent finite family. -/
theorem weightedLinearLagCrossTest_apply_eq_parentMask
    (w : ℕ → ℝ) (parent : BombieriTest)
    {cells : List BombieriTest} {etas : List (ℝ → ℝ)}
    (hrel : List.Forall₂ (CoherentWith parent) cells etas)
    (x : ℝ) :
    (bombieriWeightedLinearLagCrossTest w cells : BombieriTest) x =
      ∫ y : ℝ in Set.Ioi 0,
        parentMaskedIntegrand parent
          (symmetricLinearLagMask w etas) x y :=
  (mask_integrable_and_test_eq w parent hrel x).2

/-- Full collective identity: the exact production residual is the real
Bombieri functional of one test whose every point is a single common-parent
correlation integral with the symmetric residual mask. -/
theorem coherent_fejerResidual_eq_functional_parentMask
    (parent : BombieriTest)
    {cells : List BombieriTest} {etas : List (ℝ → ℝ)}
    (hrel : List.Forall₂ (CoherentWith parent) cells etas) :
    bombieriWeightedLinearLagCross
        bombieriFejerThreeResidualLagWeight cells =
      (bombieriFunctional
        (bombieriWeightedLinearLagCrossTest
          bombieriFejerThreeResidualLagWeight cells)).re ∧
    ∀ x : ℝ,
      (bombieriWeightedLinearLagCrossTest
          bombieriFejerThreeResidualLagWeight cells : BombieriTest) x =
        ∫ y : ℝ in Set.Ioi 0,
          parentMaskedIntegrand parent
            (symmetricLinearLagMask
              bombieriFejerThreeResidualLagWeight etas) x y := by
  constructor
  · exact fejerResidual_eq_functional_crossTestSum_re cells
  · exact weightedLinearLagCrossTest_apply_eq_parentMask
      bombieriFejerThreeResidualLagWeight parent hrel

private theorem forall₂_list_ofFn
    {A B : Type*} (R : A → B → Prop) {n : ℕ}
    (a : Fin n → A) (b : Fin n → B)
    (h : ∀ i : Fin n, R (a i) (b i)) :
    List.Forall₂ R (List.ofFn a) (List.ofFn b) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      exact List.Forall₂.cons (h 0)
        (ih (fun i ↦ a i.succ) (fun i ↦ b i.succ)
          (fun i ↦ h i.succ))

/-- The exact collective parent-mask identity in the consecutive-block form
produced by the coherent quarter-log-lattice decomposition. -/
theorem coherent_integerBlock_fejerResidual_eq_functional_parentMask
    (parent : BombieriTest)
    (A : ℤ → BombieriTest) (eta : ℤ → ℝ → ℝ)
    (lo : ℤ) (n : ℕ)
    (hcommon : ∀ k : ℤ, ∀ x : ℝ,
      A k x = ((eta k x : ℝ) : ℂ) * parent x) :
    bombieriWeightedLinearLagCross
        bombieriFejerThreeResidualLagWeight
        (List.ofFn (integerBlock A lo n)) =
      (bombieriFunctional
        (bombieriWeightedLinearLagCrossTest
          bombieriFejerThreeResidualLagWeight
          (List.ofFn (integerBlock A lo n)))).re ∧
    ∀ x : ℝ,
      (bombieriWeightedLinearLagCrossTest
          bombieriFejerThreeResidualLagWeight
          (List.ofFn (integerBlock A lo n)) : BombieriTest) x =
        ∫ y : ℝ in Set.Ioi 0,
          parentMaskedIntegrand parent
            (symmetricLinearLagMask
              bombieriFejerThreeResidualLagWeight
              (List.ofFn (integerBlock eta lo n))) x y := by
  apply coherent_fejerResidual_eq_functional_parentMask parent
  apply forall₂_list_ofFn
  intro i z
  simpa only [integerBlock] using hcommon (lo + (i : ℕ)) z

/-- For a coherent padded block, the existing exact Fejer decomposition
turns nonnegativity of the whole quadratic value into the required absorption
inequality.  This deliberately does not claim that the residual is itself
nonnegative. -/
theorem bombieriQuadraticRealValue_paddedIntegerBlock_sum_nonnegative_iff_parentMask_absorption
    (parent : BombieriTest)
    (A : ℤ → BombieriTest) (eta : ℤ → ℝ → ℝ)
    (lo : ℤ) (n : ℕ)
    (hcommon : ∀ k : ℤ, ∀ x : ℝ,
      A k x = ((eta k x : ℝ) : ℂ) * parent x) :
    0 ≤ bombieriQuadraticRealValue
        (∑ i, paddedIntegerBlock A lo n i) ↔
      -bombieriCyclicFejerThree (finRotate (n + 2))
          (paddedIntegerBlock A lo n) ≤
        (bombieriFunctional
          (bombieriWeightedLinearLagCrossTest
            bombieriFejerThreeResidualLagWeight
            (List.ofFn (integerBlock A lo n)))).re := by
  have hmask :=
    (coherent_integerBlock_fejerResidual_eq_functional_parentMask
      parent A eta lo n hcommon).1
  rw [bombieriQuadraticRealValue_paddedIntegerBlock_sum_eq_fejer_add_linear_lags,
    hmask]
  constructor <;> intro h <;> linarith

end


end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFejerResidualParentMaskStructural
