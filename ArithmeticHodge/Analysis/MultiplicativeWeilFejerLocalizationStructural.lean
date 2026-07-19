import ArithmeticHodge.Analysis.MultiplicativeWeilGlobalCrossAdditiveStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilCellAssemblyStructural

set_option autoImplicit false

open Complex Finset Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFejerLocalizationStructural

noncomputable section

open MultiplicativeWeil

/-!
# Fejer localization of a finite Bombieri Gram

An order-three Fejer taper is an exact average of three-cell window
quadratics.  This remains true for the complete Bombieri form: the local
critical cross and polarized prime cross stay coupled throughout the
identity.

The cyclic formulation separates the algebra from boundary bookkeeping.
Applications to a linearly ordered lattice may insert two adjacent zero cells
at the cyclic boundary.  Positivity follows whenever every three-cell window
is a ratio-two cell; no sign is asserted for the complementary residual.
-/

/-- The real Bombieri quadratic value of one test. -/
def bombieriQuadraticRealValue (f : BombieriTest) : ℝ :=
  (bombieriFunctional (bombieriQuadraticTest f)).re

/-- The real coordinate of the complete local-minus-prime cross. -/
def bombieriGlobalCrossRealValue (f g : BombieriTest) : ℝ :=
  (bombieriTwoBlockGlobalCrossSymbol f g).re

/-- Polarization of the real Bombieri quadratic. -/
theorem bombieriQuadraticRealValue_add (f g : BombieriTest) :
    bombieriQuadraticRealValue (f + g) =
      bombieriQuadraticRealValue f + bombieriQuadraticRealValue g +
        2 * bombieriGlobalCrossRealValue f g := by
  simpa only [bombieriQuadraticRealValue, bombieriGlobalCrossRealValue,
    one_smul, Complex.normSq_one, one_mul] using
    bombieriFunctional_twoBlock_re f g 1

/-- Exact expansion of a three-cell window. -/
theorem bombieriQuadraticRealValue_add_add
    (f g h : BombieriTest) :
    bombieriQuadraticRealValue (f + g + h) =
      bombieriQuadraticRealValue f + bombieriQuadraticRealValue g +
        bombieriQuadraticRealValue h +
        2 * bombieriGlobalCrossRealValue f g +
        2 * bombieriGlobalCrossRealValue f h +
        2 * bombieriGlobalCrossRealValue g h := by
  rw [bombieriQuadraticRealValue_add, bombieriQuadraticRealValue_add]
  unfold bombieriGlobalCrossRealValue
  rw [bombieriTwoBlockGlobalCrossSymbol_add_left]
  simp only [Complex.add_re]
  ring

/-- The cyclic order-three Fejer taper.  The first off-diagonal has weight
`2/3` in the Hermitian Gram, and the second has weight `1/3`. -/
def bombieriCyclicFejerThree
    {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (a : ι → BombieriTest) : ℝ :=
  (∑ i, bombieriQuadraticRealValue (a i)) +
    (4 / 3 : ℝ) *
      ∑ i, bombieriGlobalCrossRealValue (a i) (a (σ i)) +
    (2 / 3 : ℝ) *
      ∑ i, bombieriGlobalCrossRealValue (a i) (a (σ (σ i)))

/-- Sum of every cyclic three-cell window quadratic. -/
def bombieriCyclicThreeWindowEnergy
    {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (a : ι → BombieriTest) : ℝ :=
  ∑ i, bombieriQuadraticRealValue
    (a i + a (σ i) + a (σ (σ i)))

/-- Boundary-free Fejer localization: the three-window energy is exactly
three times the tapered Gram. -/
theorem bombieriCyclicThreeWindowEnergy_eq_three_mul_fejer
    {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (a : ι → BombieriTest) :
    bombieriCyclicThreeWindowEnergy σ a =
      3 * bombieriCyclicFejerThree σ a := by
  unfold bombieriCyclicThreeWindowEnergy bombieriCyclicFejerThree
  simp_rw [bombieriQuadraticRealValue_add_add]
  simp only [Finset.sum_add_distrib]
  have hq1 :
      (∑ i, bombieriQuadraticRealValue (a (σ i))) =
        ∑ i, bombieriQuadraticRealValue (a i) := by
    exact Equiv.sum_comp σ (fun i ↦ bombieriQuadraticRealValue (a i))
  have hq2 :
      (∑ i, bombieriQuadraticRealValue (a (σ (σ i)))) =
        ∑ i, bombieriQuadraticRealValue (a i) := by
    exact Equiv.sum_comp (σ.trans σ)
      (fun i ↦ bombieriQuadraticRealValue (a i))
  have hz1 :
      (∑ i, bombieriGlobalCrossRealValue
        (a (σ i)) (a (σ (σ i)))) =
        ∑ i, bombieriGlobalCrossRealValue (a i) (a (σ i)) := by
    exact Equiv.sum_comp σ
      (fun i ↦ bombieriGlobalCrossRealValue (a i) (a (σ i)))
  have hz0mul :
      (∑ i, 2 * bombieriGlobalCrossRealValue (a i) (a (σ i))) =
        2 * ∑ i, bombieriGlobalCrossRealValue (a i) (a (σ i)) := by
    exact (Finset.mul_sum ..).symm
  have hz2mul :
      (∑ i, 2 * bombieriGlobalCrossRealValue
        (a i) (a (σ (σ i)))) =
        2 * ∑ i, bombieriGlobalCrossRealValue
          (a i) (a (σ (σ i))) := by
    exact (Finset.mul_sum ..).symm
  have hz1mul :
      (∑ i, 2 * bombieriGlobalCrossRealValue
        (a (σ i)) (a (σ (σ i)))) =
        2 * ∑ i, bombieriGlobalCrossRealValue (a i) (a (σ i)) := by
    rw [← Finset.mul_sum, hz1]
  rw [hq1, hq2, hz0mul, hz2mul, hz1mul]
  ring

/-- The Fejer taper is nonnegative as soon as all cyclic three-cell windows
have nonnegative Bombieri quadratic value. -/
theorem bombieriCyclicFejerThree_nonnegative_of_windows
    {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (a : ι → BombieriTest)
    (hwindow : ∀ i, 0 ≤ bombieriQuadraticRealValue
      (a i + a (σ i) + a (σ (σ i)))) :
    0 ≤ bombieriCyclicFejerThree σ a := by
  have henergy : 0 ≤ bombieriCyclicThreeWindowEnergy σ a := by
    exact Finset.sum_nonneg fun i _hi ↦ hwindow i
  rw [bombieriCyclicThreeWindowEnergy_eq_three_mul_fejer] at henergy
  linarith

/-- Ratio-two positivity supplies the window hypotheses in the preceding
Fejer theorem. -/
theorem bombieriCyclicFejerThree_nonnegative_of_ratioTwo_windows
    {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (a : ι → BombieriTest)
    (hwindow : ∀ i, BombieriRatioTwoCell
      (a i + a (σ i) + a (σ (σ i)))) :
    0 ≤ bombieriCyclicFejerThree σ a := by
  apply bombieriCyclicFejerThree_nonnegative_of_windows
  intro i
  exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _ (hwindow i)

/-- The phase-coupled remainder left after extracting the positive Fejer
taper. -/
def bombieriCyclicFejerThreeResidual
    {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (a : ι → BombieriTest) : ℝ :=
  bombieriQuadraticRealValue (∑ i, a i) - bombieriCyclicFejerThree σ a

/-- Exact tapered-plus-residual decomposition of the complete finite Gram. -/
theorem bombieriQuadraticRealValue_sum_eq_fejer_add_residual
    {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (a : ι → BombieriTest) :
    bombieriQuadraticRealValue (∑ i, a i) =
      bombieriCyclicFejerThree σ a +
        bombieriCyclicFejerThreeResidual σ a := by
  unfold bombieriCyclicFejerThreeResidual
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFejerLocalizationStructural
