import ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellCommonParentDeterminantStructural

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set TopologicalSpace
open scoped BigOperators ContDiff Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeilPositiveResidualKernelObstructionStructural

noncomputable section

open MultiplicativeWeil
open ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthEndpointReserveStructural
open ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellCommonParentDeterminantStructural
open ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellMinimalBlockReserveStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
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

/-! ## The actual negative remote endpoint supplied by common-parent geometry -/

/-- The already constructed zero-middle common parent has a strictly negative
*global* endpoint cross, not merely a negative local-kernel cross.  The
zero-middle support identity annihilates the only factor-two prime atom, so
the exact local-minus-prime formula transfers the strict sign without loss. -/
theorem exists_real_middleZero_fiveCell_negative_remoteGlobalCross
    (k : ℤ) :
    ∃ parent : BombieriTest,
      bombieriConjugateTest parent = parent ∧
        fiveCellMiddleThree parent k = 0 ∧
        (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent (k + 4))).re < 0 := by
  obtain ⟨parent, hparent, hmiddle, hlocal⟩ :=
    exists_real_middleZero_fiveCell_negative_remoteLocalCross k
  have hprime := fiveCell_remoteEndpointCross_eq_zero_of_middle_zero
    parent k hmiddle
  have hcross :=
    two_mul_fiveCell_remoteEndpointGlobalCross_re_eq_local_sub_prime
      parent k
  rw [hprime] at hcross
  simp only [Complex.zero_re, mul_zero, sub_zero] at hcross
  refine ⟨parent, hparent, hmiddle, ?_⟩
  linarith

/-! ## Common-parent realization interface -/

/-- If the three middle directions can be realized while keeping two fixed
endpoint cells, the rank-nullity obstruction is an actual real common-parent
five-cell obstruction: its interior pivot is positive but its conditional
residual numerator is strictly negative. -/
theorem exists_real_fiveCell_strictly_negative_middlePivotNumerator_of_realization
    (k : ℤ) (a e : BombieriTest) (middle : Fin 3 → BombieriTest)
    (hmiddle : ∀ c : Fin 3 → ℝ, c ≠ 0 →
      0 < bombieriRealQuadraticValue
        (threeMiddleCombination middle c))
    (hremote :
      (bombieriTwoBlockGlobalCrossSymbol a e).re < 0)
    (hrealize : ∀ c : Fin 3 → ℝ,
      ∃ parent : BombieriTest,
        bombieriConjugateTest parent = parent ∧
          monotoneQuarterCell parent k = a ∧
          monotoneQuarterCell parent (k + 4) = e ∧
          fiveCellMiddleThree parent k =
            threeMiddleCombination middle c) :
    ∃ parent : BombieriTest,
      bombieriConjugateTest parent = parent ∧
        0 < bombieriRealQuadraticValue (fiveCellMiddleThree parent k) ∧
        bombieriRealQuadraticValue (fiveCellMiddleThree parent k) *
              (bombieriTwoBlockGlobalCrossSymbol
                (monotoneQuarterCell parent k)
                (monotoneQuarterCell parent (k + 4))).re -
            (bombieriTwoBlockGlobalCrossSymbol
              (monotoneQuarterCell parent k)
              (fiveCellMiddleThree parent k)).re *
            (bombieriTwoBlockGlobalCrossSymbol
              (fiveCellMiddleThree parent k)
              (monotoneQuarterCell parent (k + 4))).re < 0 := by
  obtain ⟨c, hc0, hleft, hright, hnegative⟩ :=
    exists_strictly_negative_middlePivotNumerator_of_three_middle_modes
      a e middle hmiddle hremote
  obtain ⟨parent, hparent, ha, he, hm⟩ := hrealize c
  refine ⟨parent, hparent, ?_, ?_⟩
  · rw [hm]
    exact hmiddle c hc0
  · rw [ha, he, hm]
    exact hnegative

/-! ## Three disjoint real middle bumps -/

/-- A real smooth Bombieri bump with prescribed value one and support inside
an arbitrary positive neighborhood. -/
private theorem exists_real_bombieri_bump_at
    (c : ℝ) (U : Set ℝ) (hU : U ∈ 𝓝 c) (hUpos : U ⊆ Ioi 0) :
    ∃ eta : BombieriTest,
      eta c = 1 ∧ tsupport (eta : ℝ → ℂ) ⊆ U ∧
        bombieriConjugateTest eta = eta := by
  obtain ⟨phi, hphiSupport, hphiCompact, hphiSmooth, _hphiRange, hphiOne⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hU
  have hsmooth : ContDiff ℝ ∞ (fun x : ℝ ↦ (phi x : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp hphiSmooth
  have hcompact : HasCompactSupport (fun x : ℝ ↦ (phi x : ℂ)) := by
    change HasCompactSupport (Complex.ofRealCLM ∘ phi)
    exact hphiCompact.comp_left rfl
  have htsupport : tsupport (fun x : ℝ ↦ (phi x : ℂ)) = tsupport phi := by
    have hsupport : Function.support (fun x : ℝ ↦ (phi x : ℂ)) =
        Function.support phi := by
      ext x
      simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
    unfold tsupport
    rw [hsupport]
  let eta : BombieriTest := TestFunction.mk
    (fun x : ℝ ↦ (phi x : ℂ)) hsmooth hcompact (by
      rw [htsupport]
      simpa only [positiveHalfLine] using hphiSupport.trans hUpos)
  refine ⟨eta, ?_, ?_, ?_⟩
  · change (phi c : ℂ) = 1
    rw [hphiOne]
    norm_num
  · change tsupport (fun x : ℝ ↦ (phi x : ℂ)) ⊆ U
    rw [htsupport]
    exact hphiSupport
  · apply TestFunction.ext
    intro x
    simp only [bombieriConjugateTest_apply]
    change starRingEnd ℂ (phi x : ℂ) = (phi x : ℂ)
    simp

private theorem value_eq_zero_of_not_mem_tsupport
    (f : BombieriTest) {x : ℝ} (hx : x ∉ tsupport (f : ℝ → ℂ)) :
    f x = 0 := by
  by_contra hne
  exact hx (subset_tsupport _ (Function.mem_support.mpr hne))

/-- Every positive interval contains three real Bombieri bumps with disjoint
supports and a point-evaluation Kronecker matrix. -/
theorem exists_three_pointSeparated_real_bombieri_bumps
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ middle : Fin 3 → BombieriTest, ∃ center : Fin 3 → ℝ,
      (∀ i, bombieriConjugateTest (middle i) = middle i) ∧
      (∀ i, tsupport (middle i : ℝ → ℂ) ⊆ Ioo a b) ∧
      ∀ i j, middle i (center j) = if i = j then 1 else 0 := by
  let x0 : ℝ := (6 * a + b) / 7
  let y0 : ℝ := (5 * a + 2 * b) / 7
  let x1 : ℝ := (4 * a + 3 * b) / 7
  let y1 : ℝ := (3 * a + 4 * b) / 7
  let x2 : ℝ := (2 * a + 5 * b) / 7
  let y2 : ℝ := (a + 6 * b) / 7
  let c0 : ℝ := (x0 + y0) / 2
  let c1 : ℝ := (x1 + y1) / 2
  let c2 : ℝ := (x2 + y2) / 2
  have hax0 : a < x0 := by dsimp only [x0]; linarith
  have hx0y0 : x0 < y0 := by dsimp only [x0, y0]; linarith
  have hy0x1 : y0 < x1 := by dsimp only [y0, x1]; linarith
  have hx1y1 : x1 < y1 := by dsimp only [x1, y1]; linarith
  have hy1x2 : y1 < x2 := by dsimp only [y1, x2]; linarith
  have hx2y2 : x2 < y2 := by dsimp only [x2, y2]; linarith
  have hy2b : y2 < b := by dsimp only [y2]; linarith
  have hx0c0 : x0 < c0 := by dsimp only [c0]; linarith
  have hc0y0 : c0 < y0 := by dsimp only [c0]; linarith
  have hx1c1 : x1 < c1 := by dsimp only [c1]; linarith
  have hc1y1 : c1 < y1 := by dsimp only [c1]; linarith
  have hx2c2 : x2 < c2 := by dsimp only [c2]; linarith
  have hc2y2 : c2 < y2 := by dsimp only [c2]; linarith
  have hU0pos : Ioo x0 y0 ⊆ Ioi 0 := by
    intro x hx
    exact ha.trans (hax0.trans hx.1)
  have hU1pos : Ioo x1 y1 ⊆ Ioi 0 := by
    intro x hx
    exact ha.trans (hax0.trans (hx0y0.trans (hy0x1.trans hx.1)))
  have hU2pos : Ioo x2 y2 ⊆ Ioi 0 := by
    intro x hx
    exact ha.trans
      (hax0.trans (hx0y0.trans
        (hy0x1.trans (hx1y1.trans (hy1x2.trans hx.1)))))
  obtain ⟨b0, hb0one, hb0support, hb0real⟩ :=
    exists_real_bombieri_bump_at c0 (Ioo x0 y0)
      (Ioo_mem_nhds hx0c0 hc0y0) hU0pos
  obtain ⟨b1, hb1one, hb1support, hb1real⟩ :=
    exists_real_bombieri_bump_at c1 (Ioo x1 y1)
      (Ioo_mem_nhds hx1c1 hc1y1) hU1pos
  obtain ⟨b2, hb2one, hb2support, hb2real⟩ :=
    exists_real_bombieri_bump_at c2 (Ioo x2 y2)
      (Ioo_mem_nhds hx2c2 hc2y2) hU2pos
  have hb0c1 : b0 c1 = 0 := by
    apply value_eq_zero_of_not_mem_tsupport b0
    intro hc
    have h := hb0support hc
    exact (not_lt_of_ge (hy0x1.trans hx1c1).le) h.2
  have hb0c2 : b0 c2 = 0 := by
    apply value_eq_zero_of_not_mem_tsupport b0
    intro hc
    have h := hb0support hc
    have hy0c2 : y0 < c2 :=
      hy0x1.trans (hx1y1.trans (hy1x2.trans hx2c2))
    exact (not_lt_of_ge hy0c2.le) h.2
  have hb1c0 : b1 c0 = 0 := by
    apply value_eq_zero_of_not_mem_tsupport b1
    intro hc
    have h := hb1support hc
    exact (not_lt_of_ge (hc0y0.trans hy0x1).le) h.1
  have hb1c2 : b1 c2 = 0 := by
    apply value_eq_zero_of_not_mem_tsupport b1
    intro hc
    have h := hb1support hc
    exact (not_lt_of_ge (hy1x2.trans hx2c2).le) h.2
  have hb2c0 : b2 c0 = 0 := by
    apply value_eq_zero_of_not_mem_tsupport b2
    intro hc
    have h := hb2support hc
    have hc0x2 : c0 < x2 :=
      hc0y0.trans (hy0x1.trans (hx1y1.trans hy1x2))
    exact (not_lt_of_ge hc0x2.le) h.1
  have hb2c1 : b2 c1 = 0 := by
    apply value_eq_zero_of_not_mem_tsupport b2
    intro hc
    have h := hb2support hc
    exact (not_lt_of_ge (hc1y1.trans hy1x2).le) h.1
  let middle : Fin 3 → BombieriTest := ![b0, b1, b2]
  let center : Fin 3 → ℝ := ![c0, c1, c2]
  refine ⟨middle, center, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [middle, hb0real, hb1real, hb2real]
  · intro i
    fin_cases i
    · intro x hx
      have h := hb0support hx
      exact ⟨hax0.trans h.1, h.2.trans
        (hy0x1.trans (hx1y1.trans (hy1x2.trans (hx2y2.trans hy2b))))⟩
    · intro x hx
      have h := hb1support hx
      exact ⟨hax0.trans (hx0y0.trans (hy0x1.trans h.1)),
        h.2.trans (hy1x2.trans (hx2y2.trans hy2b))⟩
    · intro x hx
      have h := hb2support hx
      exact ⟨hax0.trans (hx0y0.trans
        (hy0x1.trans (hx1y1.trans (hy1x2.trans h.1)))), h.2.trans hy2b⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [middle, center, hb0one, hb1one, hb2one,
        hb0c1, hb0c2, hb1c0, hb1c2, hb2c0, hb2c1]

end

end ArithmeticHodge.Analysis.MultiplicativeWeilPositiveResidualKernelObstructionStructural
