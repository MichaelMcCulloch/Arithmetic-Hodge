import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneLocalFullCoercivityStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCellEnergyFrameStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneLocalFullCoercivityStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealCutPhaseReductionStructural
open YoshidaEndpointHyperbolicBound
open YoshidaOddHomogeneousCoercivity

/-!
# Critical-energy frame for the monotone quarter partition

The local coercivity theorem supplies a quantitative reserve on every real
ratio-two cell.  Here its centered crop norm is identified with the intrinsic
critical logarithmic `L²` norm and the canonical monotone weights are shown to
form a finite frame with lower bound `1 / 2`.
-/

/-- Intrinsic unweighted critical logarithmic `L²` mass of a Bombieri test. -/
def bombieriCriticalLogEnergy (g : BombieriTest) : ℝ :=
  ∫ u : ℝ, ‖g.logarithmicPullbackSchwartz (1 / 2) u‖ ^ 2

private theorem bombieriCriticalLogEnergy_normalizedDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    bombieriCriticalLogEnergy (normalizedDilation lambda hlambda g) =
      bombieriCriticalLogEnergy g := by
  unfold bombieriCriticalLogEnergy
  simp_rw [normalizedDilation_logarithmicPullbackSchwartz_critical]
  simpa only [sub_eq_add_neg] using
    MeasureTheory.integral_add_right_eq_self
      (fun u : ℝ ↦ ‖g.logarithmicPullbackSchwartz (1 / 2) u‖ ^ 2)
      (-Real.log lambda)

/-- On a supported ratio-two test, the centered crop energy is exactly the
full critical logarithmic `L²` mass.  Thus the coercive norm is independent of
the chosen support endpoints and logarithmic center. -/
theorem bombieriCenteredCropEnergy_eq_criticalLogEnergy_of_ratio_le_two
    (g : BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2) :
    bombieriCenteredCropEnergy g l r = bombieriCriticalLogEnergy g := by
  let lambda : ℝ := logarithmicCenter l r
  have hlambda : 0 < lambda := logarithmicCenter_pos l r
  let g' : BombieriTest := normalizedDilation lambda hlambda g
  have hsupported : YoshidaCriticalPullbackSupported yoshidaEndpointA g' :=
    logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaEndpointA
      g hl hlr hsupport hratio
  have hcrop :
      clippedIntervalEnergy
          (yoshidaCriticalPullbackCropLinear yoshidaEndpointA g') =
        bombieriCriticalLogEnergy g' := by
    unfold clippedIntervalEnergy bombieriCriticalLogEnergy
    rw [yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hsupported]
    rw [intervalIntegral.integral_of_le (by
      linarith [yoshidaEndpointA_pos]), ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by rw [hsupported x hx, norm_zero]; norm_num)
  change clippedIntervalEnergy
      (yoshidaCriticalPullbackCropLinear yoshidaEndpointA g') =
    bombieriCriticalLogEnergy g
  rw [hcrop, bombieriCriticalLogEnergy_normalizedDilation]

/-- Pointwise critical logarithmic density of a monotone cell. -/
theorem norm_sq_logarithmicPullback_monotoneQuarterCell
    (parent : BombieriTest) (k : ℤ) (u : ℝ) :
    ‖(monotoneQuarterCell parent k).logarithmicPullbackSchwartz
        (1 / 2) u‖ ^ 2 =
      monotoneQuarterWeight k (Real.exp (-u)) ^ 2 *
        ‖parent.logarithmicPullbackSchwartz (1 / 2) u‖ ^ 2 := by
  simp only [BombieriTest.logarithmicPullbackSchwartz_apply,
    BombieriTest.logarithmicPullback, monotoneQuarterCell_apply]
  rw [norm_mul, norm_mul, norm_mul]
  have hw : ‖((monotoneQuarterWeight k (Real.exp (-u)) : ℝ) : ℂ)‖ =
      monotoneQuarterWeight k (Real.exp (-u)) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (monotoneQuarterWeight_nonnegative k (Real.exp (-u)))]
  rw [hw]
  ring

/-- Critical logarithmic energy of a monotone cell is the parent energy
density multiplied by the square of its physical monotone weight. -/
theorem bombieriCriticalLogEnergy_monotoneQuarterCell
    (parent : BombieriTest) (k : ℤ) :
    bombieriCriticalLogEnergy (monotoneQuarterCell parent k) =
      ∫ u : ℝ,
        monotoneQuarterWeight k (Real.exp (-u)) ^ 2 *
          ‖parent.logarithmicPullbackSchwartz (1 / 2) u‖ ^ 2 := by
  unfold bombieriCriticalLogEnergy
  apply integral_congr_ae
  filter_upwards [] with u
  exact norm_sq_logarithmicPullback_monotoneQuarterCell parent k u

private theorem criticalLogNormSq_integrable (g : BombieriTest) :
    Integrable
      (fun u : ℝ ↦ ‖g.logarithmicPullbackSchwartz (1 / 2) u‖ ^ 2) := by
  let H := g.logarithmicPullbackSchwartz (1 / 2)
  have hm := (MeasureTheory.memLp_two_iff_integrable_sq_norm
    H.continuous.aestronglyMeasurable).mp (H.memLp 2 volume)
  simpa only [H] using hm

private theorem monotoneQuarterWeight_mul_eq_zero_of_separated
    (k l : ℤ)
    (hkl : k + 2 ≤ l ∨ l + 2 ≤ k)
    (x : ℝ) :
    monotoneQuarterWeight k x * monotoneQuarterWeight l x = 0 := by
  rcases hkl with hkl | hlk
  · rcases le_total x (quarterLogLatticePoint (k + 2)) with hx | hx
    · rw [monotoneQuarterWeight_eq_zero_of_le l
        (hx.trans (quarterLogLatticePoint_mono hkl)), mul_zero]
    · rw [monotoneQuarterWeight_eq_zero_of_le_left k hx, zero_mul]
  · rcases le_total x (quarterLogLatticePoint (l + 2)) with hx | hx
    · rw [monotoneQuarterWeight_eq_zero_of_le k
        (hx.trans (quarterLogLatticePoint_mono hlk)), zero_mul]
    · rw [monotoneQuarterWeight_eq_zero_of_le_left l hx, mul_zero]

/-- A finite scalar family indexed along a path and having only nearest-neighbor
overlap has lower frame constant `1 / 2`. -/
private theorem sq_sum_le_two_mul_sum_sq_of_nearestNeighbor
    (w : ℕ → ℝ) (n : ℕ)
    (hsep : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i + 2 ≤ j ∨ j + 2 ≤ i → w i * w j = 0) :
    (∑ i ∈ Finset.range n, w i) ^ 2 ≤
      2 * ∑ i ∈ Finset.range n, w i ^ 2 := by
  classical
  let t : Finset ℕ := (Finset.range n).filter fun i ↦ w i ≠ 0
  have htSubset : t ⊆ Finset.range n := Finset.filter_subset _ _
  have hsum : (∑ i ∈ t, w i) = ∑ i ∈ Finset.range n, w i := by
    apply Finset.sum_subset htSubset
    intro i hiRange hiNotT
    have hnot : ¬w i ≠ 0 := by
      intro hi
      exact hiNotT (Finset.mem_filter.mpr ⟨hiRange, hi⟩)
    exact not_ne_iff.mp hnot
  have hsquares :
      (∑ i ∈ t, w i ^ 2) ≤ ∑ i ∈ Finset.range n, w i ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg htSubset
      (fun i _hiRange _hiNotT ↦ sq_nonneg (w i))
  have htCard : t.card ≤ 2 := by
    by_cases ht : t.Nonempty
    · let m : ℕ := t.min' ht
      have hm : m ∈ t := Finset.min'_mem t ht
      have hwm : w m ≠ 0 := (Finset.mem_filter.mp hm).2
      have hsub : t ⊆ {m, m + 1} := by
        intro i hi
        have hmi : m ≤ i := Finset.min'_le t i hi
        have hwi : w i ≠ 0 := (Finset.mem_filter.mp hi).2
        have hiUpper : i ≤ m + 1 := by
          by_contra hnot
          have hfar : m + 2 ≤ i := by omega
          have hzero := hsep m (htSubset hm) i (htSubset hi) (Or.inl hfar)
          exact (mul_ne_zero hwm hwi) hzero
        have hiCases : i = m ∨ i = m + 1 := by omega
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hiCases
      calc
        t.card ≤ ({m, m + 1} : Finset ℕ).card := Finset.card_le_card hsub
        _ ≤ 2 := by simp
    · rw [Finset.not_nonempty_iff_eq_empty.mp ht]
      norm_num
  have htCardReal : (t.card : ℝ) ≤ 2 := by exact_mod_cast htCard
  have htSquaresNonneg : 0 ≤ ∑ i ∈ t, w i ^ 2 :=
    Finset.sum_nonneg fun i _hi ↦ sq_nonneg (w i)
  have hcs :
      (∑ i ∈ t, w i) ^ 2 ≤
        (t.card : ℝ) * ∑ i ∈ t, w i ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc
    (∑ i ∈ Finset.range n, w i) ^ 2 =
        (∑ i ∈ t, w i) ^ 2 := by rw [hsum]
    _ ≤ (t.card : ℝ) * ∑ i ∈ t, w i ^ 2 := hcs
    _ ≤ 2 * ∑ i ∈ t, w i ^ 2 :=
      mul_le_mul_of_nonneg_right htCardReal htSquaresNonneg
    _ ≤ 2 * ∑ i ∈ Finset.range n, w i ^ 2 :=
      mul_le_mul_of_nonneg_left hsquares (by norm_num)

/-- Pointwise lower frame bound for any finite consecutive monotone partition
whose two boundary steps are respectively one and zero. -/
theorem half_le_sum_sq_monotoneQuarterWeight
    (lo : ℤ) (n : ℕ) (x : ℝ)
    (hleft : monotoneQuarterStep lo x = 1)
    (hright : monotoneQuarterStep (lo + (n : ℤ)) x = 0) :
    (1 / 2 : ℝ) ≤
      ∑ i ∈ Finset.range n,
        monotoneQuarterWeight (lo + (i : ℤ)) x ^ 2 := by
  have hframe := sq_sum_le_two_mul_sum_sq_of_nearestNeighbor
    (fun i : ℕ ↦ monotoneQuarterWeight (lo + (i : ℤ)) x) n
    (by
      intro i hi j hj hij
      apply monotoneQuarterWeight_mul_eq_zero_of_separated
      rcases hij with hij | hji
      · left
        have hij' : (i : ℤ) + 2 ≤ (j : ℤ) := by exact_mod_cast hij
        omega
      · right
        have hji' : (j : ℤ) + 2 ≤ (i : ℤ) := by exact_mod_cast hji
        omega)
  rw [sum_range_monotoneQuarterWeight, hleft, hright] at hframe
  norm_num at hframe ⊢
  linarith

/-- Finite canonical monotone cells retain at least half of their parent's
critical logarithmic `L²` mass.  The boundary hypotheses are needed only where
the parent is pointwise nonzero. -/
theorem half_mul_bombieriCriticalLogEnergy_le_sum_monotoneQuarterCell
    (parent : BombieriTest) (lo : ℤ) (n : ℕ)
    (hleft : ∀ x : ℝ, parent x ≠ 0 → monotoneQuarterStep lo x = 1)
    (hright : ∀ x : ℝ, parent x ≠ 0 →
      monotoneQuarterStep (lo + (n : ℤ)) x = 0) :
    (1 / 2 : ℝ) * bombieriCriticalLogEnergy parent ≤
      ∑ i ∈ Finset.range n,
        bombieriCriticalLogEnergy
          (monotoneQuarterCell parent (lo + (i : ℤ))) := by
  let P : ℝ → ℝ := fun u ↦
    ‖parent.logarithmicPullbackSchwartz (1 / 2) u‖ ^ 2
  let C : ℕ → ℝ → ℝ := fun i u ↦
    ‖(monotoneQuarterCell parent
      (lo + (i : ℤ))).logarithmicPullbackSchwartz (1 / 2) u‖ ^ 2
  have hPint : Integrable P := by
    simpa only [P] using criticalLogNormSq_integrable parent
  have hCint (i : ℕ) : Integrable (C i) := by
    simpa only [C] using criticalLogNormSq_integrable
      (monotoneQuarterCell parent (lo + (i : ℤ)))
  have hpoint (u : ℝ) :
      (1 / 2 : ℝ) * P u ≤
        ∑ i ∈ Finset.range n, C i u := by
    by_cases hp : parent (Real.exp (-u)) = 0
    · have hPzero : P u = 0 := by
        dsimp only [P]
        simp only [BombieriTest.logarithmicPullbackSchwartz_apply,
          BombieriTest.logarithmicPullback, hp, mul_zero, norm_zero]
        norm_num
      have hCnonneg : 0 ≤ ∑ i ∈ Finset.range n, C i u :=
        Finset.sum_nonneg fun i _hi ↦ sq_nonneg _
      rw [hPzero, mul_zero]
      exact hCnonneg
    · have hframe := half_le_sum_sq_monotoneQuarterWeight lo n
        (Real.exp (-u)) (hleft _ hp) (hright _ hp)
      have hPnonneg : 0 ≤ P u := sq_nonneg _
      calc
        (1 / 2 : ℝ) * P u ≤
            (∑ i ∈ Finset.range n,
              monotoneQuarterWeight
                (lo + (i : ℤ)) (Real.exp (-u)) ^ 2) * P u :=
          mul_le_mul_of_nonneg_right hframe hPnonneg
        _ = ∑ i ∈ Finset.range n,
            monotoneQuarterWeight
              (lo + (i : ℤ)) (Real.exp (-u)) ^ 2 * P u := by
          rw [Finset.sum_mul]
        _ = ∑ i ∈ Finset.range n, C i u := by
          apply Finset.sum_congr rfl
          intro i _hi
          dsimp only [C, P]
          exact
            (norm_sq_logarithmicPullback_monotoneQuarterCell parent
              (lo + (i : ℤ)) u).symm
  change (1 / 2 : ℝ) * (∫ u : ℝ, P u) ≤
    ∑ i ∈ Finset.range n, ∫ u : ℝ, C i u
  rw [← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_finset_sum]
  · exact MeasureTheory.integral_mono (hPint.const_mul _)
      (integrable_finset_sum _ fun i _hi ↦ hCint i) hpoint
  · intro i _hi
    exact hCint i

/-- The canonical endpoint choice for one monotone quarter cell exposes
exactly its intrinsic critical logarithmic energy. -/
theorem bombieriCenteredCropEnergy_monotoneQuarterCell_eq_criticalLogEnergy
    (parent : BombieriTest) (k : ℤ) :
    bombieriCenteredCropEnergy
        (monotoneQuarterCell parent k)
        (quarterLogLatticePoint k)
        (quarterLogLatticePoint (k + 2)) =
      bombieriCriticalLogEnergy (monotoneQuarterCell parent k) := by
  apply bombieriCenteredCropEnergy_eq_criticalLogEnergy_of_ratio_le_two
  · exact quarterLogLatticePoint_pos k
  · exact quarterLogLatticePoint_mono (by omega)
  · exact monotoneQuarterCell_tsupport_subset parent k
  · rw [quarterLogLatticePoint_add_two,
      mul_div_cancel_right₀ _ (quarterLogLatticePoint_pos k).ne']
    calc
      quarterLogLatticePoint 2 ≤ quarterLogLatticePoint 4 :=
        quarterLogLatticePoint_mono (by omega)
      _ = 2 := quarterLogLatticePoint_four

/-- Combining the `1 / 2` frame bound with the `1 / 12000` local gap gives a
`1 / 24000` reserve in the sum of the cell diagonals.  This theorem makes no
claim about the cross terms in the quadratic form of the parent sum. -/
theorem sum_monotoneQuarterCell_quadratic_re_ge_parentCriticalLogEnergy
    (parent : BombieriTest)
    (hreal : bombieriConjugateTest parent = parent)
    (lo : ℤ) (n : ℕ)
    (hleft : ∀ x : ℝ, parent x ≠ 0 → monotoneQuarterStep lo x = 1)
    (hright : ∀ x : ℝ, parent x ≠ 0 →
      monotoneQuarterStep (lo + (n : ℤ)) x = 0) :
    (1 / 24000 : ℝ) * bombieriCriticalLogEnergy parent ≤
      ∑ i ∈ Finset.range n,
        (bombieriFunctional
          (bombieriQuadraticTest
            (monotoneQuarterCell parent (lo + (i : ℤ))))).re := by
  have hframe :=
    half_mul_bombieriCriticalLogEnergy_le_sum_monotoneQuarterCell
      parent lo n hleft hright
  have hcells :
      (∑ i ∈ Finset.range n,
          (1 / 12000 : ℝ) *
            bombieriCriticalLogEnergy
              (monotoneQuarterCell parent (lo + (i : ℤ)))) ≤
        ∑ i ∈ Finset.range n,
          (bombieriFunctional
            (bombieriQuadraticTest
              (monotoneQuarterCell parent (lo + (i : ℤ))))).re := by
    apply Finset.sum_le_sum
    intro i _hi
    rw [← bombieriCenteredCropEnergy_monotoneQuarterCell_eq_criticalLogEnergy]
    exact monotoneQuarterCell_quadratic_re_ge_centeredCropEnergy
      parent hreal (lo + (i : ℤ))
  calc
    (1 / 24000 : ℝ) * bombieriCriticalLogEnergy parent =
        (1 / 12000 : ℝ) *
          ((1 / 2 : ℝ) * bombieriCriticalLogEnergy parent) := by ring
    _ ≤ (1 / 12000 : ℝ) *
        (∑ i ∈ Finset.range n,
          bombieriCriticalLogEnergy
            (monotoneQuarterCell parent (lo + (i : ℤ)))) :=
      mul_le_mul_of_nonneg_left hframe (by norm_num)
    _ = ∑ i ∈ Finset.range n,
        (1 / 12000 : ℝ) *
          bombieriCriticalLogEnergy
            (monotoneQuarterCell parent (lo + (i : ℤ))) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range n,
        (bombieriFunctional
          (bombieriQuadraticTest
            (monotoneQuarterCell parent (lo + (i : ℤ))))).re := hcells

private theorem monotoneQuarterStep_eq_one_of_cutoff_eq_parent
    (parent : BombieriTest) (k : ℤ)
    (hcut : monotoneQuarterCutoff parent k = parent)
    (x : ℝ) (hx : parent x ≠ 0) :
    monotoneQuarterStep k x = 1 := by
  have happ := congrArg (fun f : BombieriTest ↦ f x) hcut
  change ((monotoneQuarterStep k x : ℝ) : ℂ) * parent x = parent x at happ
  have hproduct :
      ((((monotoneQuarterStep k x : ℝ) : ℂ) - 1) * parent x) = 0 := by
    rw [sub_mul, happ]
    ring
  have hfactor : (((monotoneQuarterStep k x : ℝ) : ℂ) - 1) = 0 :=
    (mul_eq_zero.mp hproduct).resolve_right hx
  have hc : ((monotoneQuarterStep k x : ℝ) : ℂ) = 1 :=
    sub_eq_zero.mp hfactor
  simpa using congrArg Complex.re hc

private theorem monotoneQuarterStep_eq_zero_of_cutoff_eq_zero
    (parent : BombieriTest) (k : ℤ)
    (hcut : monotoneQuarterCutoff parent k = 0)
    (x : ℝ) (hx : parent x ≠ 0) :
    monotoneQuarterStep k x = 0 := by
  have happ := congrArg (fun f : BombieriTest ↦ f x) hcut
  change ((monotoneQuarterStep k x : ℝ) : ℂ) * parent x = 0 at happ
  have hc : ((monotoneQuarterStep k x : ℝ) : ℂ) = 0 :=
    (mul_eq_zero.mp happ).resolve_right hx
  simpa using congrArg Complex.re hc

/-- Every conjugation-fixed Bombieri test admits an exact finite canonical
cell decomposition whose sum of diagonal quadratic values controls the
parent's full critical logarithmic mass with constant `1 / 24000`. -/
theorem exists_monotoneQuarterCell_decomposition_with_diagonal_reserve
    (parent : BombieriTest)
    (hreal : bombieriConjugateTest parent = parent) :
    ∃ (lo : ℤ) (n : ℕ),
      (∑ i ∈ Finset.range n,
          monotoneQuarterCell parent (lo + (i : ℤ))) = parent ∧
      (1 / 24000 : ℝ) * bombieriCriticalLogEnergy parent ≤
        ∑ i ∈ Finset.range n,
          (bombieriFunctional
            (bombieriQuadraticTest
              (monotoneQuarterCell parent (lo + (i : ℤ))))).re := by
  obtain ⟨lo, n, hcutLeft, hcutRight, hsum, _hratio, _hsuffix⟩ :=
    exists_monotoneQuarterCell_decomposition parent
  refine ⟨lo, n, hsum, ?_⟩
  apply sum_monotoneQuarterCell_quadratic_re_ge_parentCriticalLogEnergy
    parent hreal lo n
  · intro x hx
    exact monotoneQuarterStep_eq_one_of_cutoff_eq_parent
      parent lo hcutLeft x hx
  · intro x hx
    exact monotoneQuarterStep_eq_zero_of_cutoff_eq_zero
      parent (lo + (n : ℤ)) hcutRight x hx

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCellEnergyFrameStructural
