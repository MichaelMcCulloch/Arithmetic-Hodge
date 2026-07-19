import ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotonePropagationCriterionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotonePropagationLogDefectStructural

set_option autoImplicit false

open Complex Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotoneTailConeCriterionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealCutPhaseReductionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open MultiplicativeWeilRealMonotonePropagationLogDefectStructural

/-!
# Propagation from the whole nonnegative monotone tail cone

Finite backward assembly knows more at the `k`-th step than the sign of only
`C_(k+1)`: every later cutoff has already been proved nonnegative.  We record
the resulting tail-cone implication and prove that it still assembles every
real Bombieri test.

The second half is not merely logical plumbing.  Later cutoffs absorb earlier
ones exactly, and the logarithmic one-step identities telescope into a
triangular reserve system.  All later inequalities constrain the later
reserve prefixes, but the current defect `D_k` remains an uncoupled boundary
term.  This identifies exactly why the tail cone alone does not yet give the
needed current lower bound.
-/

/-! ## Exact nesting and absorption -/

/-- A strictly later monotone step is absorbed by every earlier step. -/
theorem monotoneQuarterStep_mul_later
    {k j : ℤ} (hkj : k < j) (x : ℝ) :
    monotoneQuarterStep k x * monotoneQuarterStep j x =
      monotoneQuarterStep j x := by
  by_cases hx : x ≤ quarterLogLatticePoint j
  · rw [monotoneQuarterStep_eq_zero_of_le j hx, mul_zero]
  · have hjx : quarterLogLatticePoint j ≤ x := (not_le.mp hx).le
    have hindex : k + 1 ≤ j := by omega
    have hkx : quarterLogLatticePoint (k + 1) ≤ x :=
      (quarterLogLatticePoint_mono hindex).trans hjx
    rw [monotoneQuarterStep_eq_one_of_le k hkx, one_mul]

/-- Consequently a later cutoff of an earlier cutoff is exactly the same
later cutoff of the original parent. -/
theorem monotoneQuarterCutoff_cutoff_eq_later
    (parent : BombieriTest) {k j : ℤ} (hkj : k < j) :
    monotoneQuarterCutoff (monotoneQuarterCutoff parent k) j =
      monotoneQuarterCutoff parent j := by
  apply TestFunction.ext
  intro x
  simp only [monotoneQuarterCutoff_apply]
  calc
    (monotoneQuarterStep j x : ℂ) *
        ((monotoneQuarterStep k x : ℂ) * parent x) =
        ((monotoneQuarterStep k x : ℂ) *
          (monotoneQuarterStep j x : ℂ)) * parent x := by ring_nf
    _ = ((monotoneQuarterStep k x *
          monotoneQuarterStep j x : ℝ) : ℂ) * parent x := by
      rw [Complex.ofReal_mul]
    _ = (monotoneQuarterStep j x : ℂ) * parent x := by
      rw [monotoneQuarterStep_mul_later hkj]

/-- Once a cutoff vanishes, every later cutoff vanishes as well. -/
theorem monotoneQuarterCutoff_eq_zero_of_zero_of_le
    (parent : BombieriTest) {k j : ℤ}
    (hzero : monotoneQuarterCutoff parent k = 0)
    (hkj : k ≤ j) :
    monotoneQuarterCutoff parent j = 0 := by
  rcases hkj.eq_or_lt with rfl | hlt
  · exact hzero
  · rw [← monotoneQuarterCutoff_cutoff_eq_later parent hlt, hzero]
    apply TestFunction.ext
    intro x
    simp [monotoneQuarterCutoff_apply]

/-! ## Tail-cone propagation and finite backward assembly -/

/-- The genuinely weaker propagation rule whose antecedent is the entire
strictly later nonnegative cutoff cone. -/
def BombieriRealMonotoneTailConePropagation : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        (∀ j : ℕ,
          0 ≤ bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1 + (j : ℤ)))) →
          0 ≤ bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent k)

/-- The one-step rule implies the tail-cone rule simply by projecting to the
first later cutoff. -/
theorem bombieriRealMonotoneTailConePropagation_of_oneStep
    (hstep : BombieriRealMonotoneCutPropagation) :
    BombieriRealMonotoneTailConePropagation := by
  intro parent hparent k htail
  apply hstep parent hparent k
  simpa only [Int.natCast_zero, add_zero] using htail 0

private theorem bombieriRealQuadraticValue_zero :
    bombieriRealQuadraticValue (0 : BombieriTest) = 0 := by
  unfold bombieriRealQuadraticValue
  have h := bombieriFunctional_quadratic_smul
    (0 : ℂ) (0 : BombieriTest)
  simpa only [zero_smul, Complex.normSq_zero, Complex.ofReal_zero,
    zero_mul, Complex.zero_re] using congrArg Complex.re h

/-- Eventual vanishing plus the tail-cone rule propagates nonnegativity to
every earlier natural-number index. -/
private theorem nonnegative_of_eventually_zero_tailCone
    (q : ℕ → ℝ)
    (heventually : ∃ N : ℕ, ∀ m > N, q m = 0)
    (htail : ∀ n : ℕ, (∀ m > n, 0 ≤ q m) → 0 ≤ q n) :
    ∀ n : ℕ, 0 ≤ q n := by
  apply Nat.strong_decreasing_induction
  · obtain ⟨N, hN⟩ := heventually
    exact ⟨N, fun m hm ↦ by rw [hN m hm]⟩
  · exact htail

/-- The tail-cone rule is sufficient for global real Bombieri positivity and
hence RH. -/
theorem riemannHypothesis_of_bombieriRealMonotoneTailConePropagation
    (zeros : ZetaZeroEnumeration)
    (hprop : BombieriRealMonotoneTailConePropagation) :
    RiemannHypothesis := by
  apply
    (riemannHypothesis_iff_bombieriRealQuadraticNonnegativity zeros).2
  intro parent hparent
  obtain ⟨lo, n, hleft, hright, _hsum, _hratio, _hsuffix⟩ :=
    exists_monotoneQuarterCell_decomposition parent
  let q : ℕ → ℝ := fun m ↦
    bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent (lo + (m : ℤ)))
  have heventually : ∃ N : ℕ, ∀ m > N, q m = 0 := by
    refine ⟨n, ?_⟩
    intro m hmn
    have hindex : lo + (n : ℤ) ≤ lo + (m : ℤ) := by
      have hnm : (n : ℤ) ≤ (m : ℤ) := by exact_mod_cast hmn.le
      omega
    have hzero := monotoneQuarterCutoff_eq_zero_of_zero_of_le
      parent hright hindex
    dsimp only [q]
    rw [hzero, bombieriRealQuadraticValue_zero]
  have htailQ (m : ℕ) (hlater : ∀ r > m, 0 ≤ q r) : 0 ≤ q m := by
    dsimp only [q]
    apply hprop parent hparent (lo + (m : ℤ))
    intro j
    have hj := hlater (m + 1 + j) (by omega)
    dsimp only [q] at hj
    convert hj using 1
    norm_num
    ring_nf
  have hall : ∀ m : ℕ, 0 ≤ q m :=
    nonnegative_of_eventually_zero_tailCone q heventually htailQ
  have hzero := hall 0
  dsimp only [q] at hzero
  simpa only [Int.natCast_zero, add_zero, hleft,
    bombieriRealQuadraticValue] using hzero

/-- RH trivially supplies every member of every tail cone; conversely the
tail-cone rule assembles RH by the preceding finite argument. -/
theorem riemannHypothesis_iff_bombieriRealMonotoneTailConePropagation
    (zeros : ZetaZeroEnumeration) :
    RiemannHypothesis ↔ BombieriRealMonotoneTailConePropagation := by
  constructor
  · intro hRH parent _hparent k _htail
    exact
      (riemannHypothesis_iff_bombieriQuadratic_re_nonnegative zeros).1 hRH
        (monotoneQuarterCutoff parent k)
  · exact riemannHypothesis_of_bombieriRealMonotoneTailConePropagation zeros

/-! ## Telescoped logarithmic reserves -/

/-- One triangular reserve summand: the ratio-two cell diagonal plus the
complete logarithmic head--suffix defect at that boundary. -/
def monotoneQuarterLogReserveSummand
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
    monotoneQuarterRealLogStepDefect parent k

/-- The reserve accumulated across `n` consecutive monotone boundaries. -/
def monotoneQuarterLogTailReserve
    (parent : BombieriTest) (k : ℤ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    monotoneQuarterLogReserveSummand parent (k + (i : ℤ))

/-- The one-step defect identities telescope exactly, with the last cutoff
as the sole boundary term. -/
theorem bombieriRealQuadraticValue_cutoff_eq_logTailReserve_add_terminal
    (parent : BombieriTest) (k : ℤ) (n : ℕ) :
    bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) =
      monotoneQuarterLogTailReserve parent k n +
        bombieriRealQuadraticValue
          (monotoneQuarterCutoff parent (k + (n : ℤ))) := by
  induction n with
  | zero =>
      simp [monotoneQuarterLogTailReserve]
  | succ n ih =>
      rw [ih]
      have hstep :=
        bombieriFunctional_monotoneQuarterCutoff_oneStep_logDefect
          parent (k + (n : ℤ))
      have hstep' :
          bombieriRealQuadraticValue
              (monotoneQuarterCutoff parent (k + (n : ℤ))) =
            bombieriRealQuadraticValue
                (monotoneQuarterCell parent (k + (n : ℤ))) +
              bombieriRealQuadraticValue
                (monotoneQuarterCutoff parent (k + (n : ℤ) + 1)) +
              monotoneQuarterRealLogStepDefect parent (k + (n : ℤ)) := by
        simpa only [bombieriRealQuadraticValue] using hstep
      rw [hstep']
      unfold monotoneQuarterLogTailReserve
      rw [Finset.sum_range_succ]
      unfold monotoneQuarterLogReserveSummand
      norm_num
      ring_nf

/-- Every nonnegative tail cone places every later reserve prefix in an exact
two-sided corridor. -/
theorem monotoneQuarterLogTailReserve_mem_tailConeCorridor
    (parent : BombieriTest) (k : ℤ)
    (htail : ∀ j : ℕ,
      0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterCutoff parent (k + 1 + (j : ℤ))))
    (n : ℕ) :
    -bombieriRealQuadraticValue
        (monotoneQuarterCutoff parent (k + 1 + (n : ℤ))) ≤
      monotoneQuarterLogTailReserve parent (k + 1) n ∧
    monotoneQuarterLogTailReserve parent (k + 1) n ≤
      bombieriRealQuadraticValue
        (monotoneQuarterCutoff parent (k + 1)) := by
  have htel :=
    bombieriRealQuadraticValue_cutoff_eq_logTailReserve_add_terminal
      parent (k + 1) n
  have hstart := htail 0
  have hterminal := htail n
  norm_num at hstart
  have hindex : k + 1 + (n : ℤ) = k + 1 + (n : ℤ) := rfl
  rw [hindex] at hterminal
  constructor <;> linarith

/-- Expanding through any length of the known tail still leaves the current
defect as a single uncancelled boundary term. -/
theorem bombieriRealQuadraticValue_cutoff_eq_currentDefect_add_tailReserve
    (parent : BombieriTest) (k : ℤ) (n : ℕ) :
    bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) =
      bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
        monotoneQuarterRealLogStepDefect parent k +
        monotoneQuarterLogTailReserve parent (k + 1) n +
        bombieriRealQuadraticValue
          (monotoneQuarterCutoff parent (k + 1 + (n : ℤ))) := by
  have hcurrent :=
    bombieriFunctional_monotoneQuarterCutoff_oneStep_logDefect parent k
  have htail :=
    bombieriRealQuadraticValue_cutoff_eq_logTailReserve_add_terminal
      parent (k + 1) n
  simp only [bombieriRealQuadraticValue] at hcurrent htail ⊢
  rw [hcurrent, htail]
  ring_nf

/-- Sharp obstruction after using an arbitrary finite portion of the tail
cone: current nonnegativity is equivalent to a lower bound on `D_k` alone.
All deeper information is confined to the displayed tail reserve and terminal
value. -/
theorem monotoneQuarterCutoff_nonnegative_iff_currentLogDefect_tailBound
    (parent : BombieriTest) (k : ℤ) (n : ℕ) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) ↔
      -(bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
          monotoneQuarterLogTailReserve parent (k + 1) n +
          bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1 + (n : ℤ)))) ≤
        monotoneQuarterRealLogStepDefect parent k := by
  rw [bombieriRealQuadraticValue_cutoff_eq_currentDefect_add_tailReserve]
  constructor <;> intro h <;> linarith

/-- Telescoping does not strengthen the numerical threshold: the complete
later reserve plus its terminal boundary is exactly `Q(C_(k+1))`.  Thus the
tail cone supplies genuine corridor relations, but no additional term that
can absorb the current archimedean-minus-Mangoldt defect. -/
theorem monotoneQuarterLogTailReserve_add_terminal_eq_nextCutoff
    (parent : BombieriTest) (k : ℤ) (n : ℕ) :
    monotoneQuarterLogTailReserve parent (k + 1) n +
        bombieriRealQuadraticValue
          (monotoneQuarterCutoff parent (k + 1 + (n : ℤ))) =
      bombieriRealQuadraticValue
        (monotoneQuarterCutoff parent (k + 1)) := by
  exact (bombieriRealQuadraticValue_cutoff_eq_logTailReserve_add_terminal
    parent (k + 1) n).symm

end

end ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotoneTailConeCriterionStructural
