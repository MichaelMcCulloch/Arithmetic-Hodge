import ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilPositiveResidualKernelObstructionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# A rank-nullity obstruction to a universal positive residual sign

The all-length middle-pivot route asks for a fixed sign on the cross of two
middle-orthogonal residuals.  This file records the sharp finite-dimensional
obstruction to such a sign: three independent middle directions leave a
nonzero direction invisible to both endpoint-cross functionals.  If the
remote endpoint cross is negative and the middle quadratic is positive on
that direction, then the desired conditional numerator is strictly negative.

This is a structural rank-nullity argument; it uses no sampling or spectral
enumeration.
-/

/-- Pair two real linear functionals on a three-dimensional coefficient
space into a map with a two-dimensional target. -/
private def pairedEndpointFunctional
    (U V : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun c i := if i = 0 then U c else V c
  map_add' c d := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  map_smul' r c := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]

/-- Two real linear functionals on `Fin 3 → ℝ` have a common nonzero kernel
vector. -/
theorem exists_ne_zero_common_kernel_three_two
    (U V : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) :
    ∃ c : Fin 3 → ℝ, c ≠ 0 ∧ U c = 0 ∧ V c = 0 := by
  let F := pairedEndpointFunctional U V
  have hdim : Module.finrank ℝ (Fin 2 → ℝ) <
      Module.finrank ℝ (Fin 3 → ℝ) := by
    simp
  have hker : LinearMap.ker F ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hFc : F c = 0 := LinearMap.mem_ker.mp hc
  have hU := congrFun hFc (0 : Fin 2)
  have hV := congrFun hFc (1 : Fin 2)
  refine ⟨c, hc0, ?_, ?_⟩
  · simpa only [F, pairedEndpointFunctional, LinearMap.coe_mk,
      AddHom.coe_mk, if_pos] using hU
  · simpa only [F, pairedEndpointFunctional, LinearMap.coe_mk,
      AddHom.coe_mk, show (1 : Fin 2) ≠ 0 by decide, if_false] using hV

/-- A real three-mode synthesis inside the Bombieri test space. -/
def threeMiddleCombination
    (middle : Fin 3 → BombieriTest) (c : Fin 3 → ℝ) : BombieriTest :=
  ∑ i : Fin 3, ((c i : ℝ) : ℂ) • middle i

private theorem threeMiddleCombination_add
    (middle : Fin 3 → BombieriTest) (c d : Fin 3 → ℝ) :
    threeMiddleCombination middle (c + d) =
      threeMiddleCombination middle c +
        threeMiddleCombination middle d := by
  unfold threeMiddleCombination
  simp_rw [Pi.add_apply, Complex.ofReal_add, add_smul]
  exact Finset.sum_add_distrib

private theorem threeMiddleCombination_smul
    (middle : Fin 3 → BombieriTest) (r : ℝ) (c : Fin 3 → ℝ) :
    threeMiddleCombination middle (r • c) =
      ((r : ℝ) : ℂ) • threeMiddleCombination middle c := by
  unfold threeMiddleCombination
  simp_rw [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_smul]
  rw [Finset.smul_sum]

/-- The left endpoint cross is a real linear functional of the three middle
coefficients. -/
private def leftEndpointCrossFunctional
    (a : BombieriTest) (middle : Fin 3 → BombieriTest) :
    (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun c :=
    (bombieriTwoBlockGlobalCrossSymbol a
      (threeMiddleCombination middle c)).re
  map_add' c d := by
    rw [threeMiddleCombination_add,
      bombieriTwoBlockGlobalCrossSymbol_add_right]
    simp
  map_smul' r c := by
    rw [threeMiddleCombination_smul,
      bombieriTwoBlockGlobalCrossSymbol_smul_right]
    simp

/-- The right endpoint cross is a real linear functional of the three middle
coefficients. -/
private def rightEndpointCrossFunctional
    (e : BombieriTest) (middle : Fin 3 → BombieriTest) :
    (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun c :=
    (bombieriTwoBlockGlobalCrossSymbol
      (threeMiddleCombination middle c) e).re
  map_add' c d := by
    rw [threeMiddleCombination_add,
      bombieriTwoBlockGlobalCrossSymbol_add_left]
    simp
  map_smul' r c := by
    rw [threeMiddleCombination_smul,
      bombieriTwoBlockGlobalCrossSymbol_smul_left]
    simp

/-- A negative remote endpoint cross and three middle directions on which the
middle quadratic is positive force a strict reversal of the signed
middle-pivot residual numerator.  Rank-nullity chooses a nonzero middle
combination orthogonal to both endpoints, so the numerator reduces exactly to
`M * X < 0`.

This theorem shows that any universal positive-residual proof must exclude
such a three-dimensional common-parent middle family; adjacent principal
minors alone cannot do so. -/
theorem exists_strictly_negative_middlePivotNumerator_of_three_middle_modes
    (a e : BombieriTest) (middle : Fin 3 → BombieriTest)
    (hmiddle : ∀ c : Fin 3 → ℝ, c ≠ 0 →
      0 < bombieriRealQuadraticValue
        (threeMiddleCombination middle c))
    (hremote :
      (bombieriTwoBlockGlobalCrossSymbol a e).re < 0) :
    ∃ c : Fin 3 → ℝ,
      c ≠ 0 ∧
      let m := threeMiddleCombination middle c
      (bombieriTwoBlockGlobalCrossSymbol a m).re = 0 ∧
        (bombieriTwoBlockGlobalCrossSymbol m e).re = 0 ∧
        bombieriRealQuadraticValue m *
              (bombieriTwoBlockGlobalCrossSymbol a e).re -
            (bombieriTwoBlockGlobalCrossSymbol a m).re *
              (bombieriTwoBlockGlobalCrossSymbol m e).re < 0 := by
  obtain ⟨c, hc0, hleft, hright⟩ :=
    exists_ne_zero_common_kernel_three_two
      (leftEndpointCrossFunctional a middle)
      (rightEndpointCrossFunctional e middle)
  change (bombieriTwoBlockGlobalCrossSymbol a
      (threeMiddleCombination middle c)).re = 0 at hleft
  change (bombieriTwoBlockGlobalCrossSymbol
      (threeMiddleCombination middle c) e).re = 0 at hright
  refine ⟨c, hc0, ?_, ?_, ?_⟩
  · exact hleft
  · exact hright
  · rw [hleft, hright]
    simp only [zero_mul, sub_zero]
    exact mul_neg_of_pos_of_neg (hmiddle c hc0) hremote

end

end ArithmeticHodge.Analysis.MultiplicativeWeilPositiveResidualKernelObstructionStructural
