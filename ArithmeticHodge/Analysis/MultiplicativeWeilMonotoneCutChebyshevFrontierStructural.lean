import ArithmeticHodge.Analysis.MultiplicativeWeilGlobalCrossAdditiveStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneQuarterPartitionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRatioTwoBlockPropagationStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeFarChebyshevStructural

set_option autoImplicit false

open Complex Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutChebyshevFrontierStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilCorrectedChebyshevPotentialStructural
open MultiplicativeWeilMonotoneCutoffEnergyMonotonicityObstructionStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilMonotoneRatioTwoBlockPropagationStructural
open MultiplicativeWeilQuarterLogLatticeFarChebyshevStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# The monotone-cut frontier as a Chebyshev-error row

The one-step propagation problem contains the complete global cross between
one quarter-lattice head cell and its whole suffix.  This file converts every
lag-three-and-beyond entry of that row into the exact corrected Chebyshev
formula.  Thus only the first two neighboring cells remain outside the
classical `psi(x) - x` representation.

No estimate for the Chebyshev error is assumed here.  The point is to replace
an abstract signed Gram entry by the precise arithmetic quantity which a
structural proof still has to control.
-/

/-- A physical monotone cell pulled back to the common base interval
`[1, sqrt 2]`. -/
def monotoneQuarterNormalizedCell
    (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  quarterLogLatticeNormalize k (monotoneQuarterCell parent k)

/-- The normalized monotone cell has the fixed base support required by the
far-cell Chebyshev formula. -/
theorem monotoneQuarterNormalizedCell_tsupport_subset
    (parent : BombieriTest) (k : ℤ) :
    tsupport (monotoneQuarterNormalizedCell parent k) ⊆
      Set.Icc 1 (quarterLogLatticePoint 2) := by
  exact quarterLogLatticeNormalize_tsupport_subset_base k
    (monotoneQuarterCell parent k)
    (monotoneQuarterCell_tsupport_subset parent k)

/-- Rescaling the normalized seed returns the original physical monotone
cell. -/
@[simp] theorem quarterLogLatticeRescale_monotoneQuarterNormalizedCell
    (parent : BombieriTest) (k : ℤ) :
    quarterLogLatticeRescale k (monotoneQuarterNormalizedCell parent k) =
      monotoneQuarterCell parent k := by
  exact quarterLogLatticeRescale_normalize k (monotoneQuarterCell parent k)

/-- The exact complex numerator attached to a head cell at `k` and a later
cell at signed lag `lag`. -/
def monotoneQuarterFarChebyshevNumerator
    (parent : BombieriTest) (k lag : ℤ) : ℂ :=
  (∫ x : ℝ in Set.Ioi 0,
      ((Chebyshev.psi (quarterLogLatticePoint lag * x) -
          quarterLogLatticePoint lag * x : ℝ) : ℂ) *
        deriv (fun y : ℝ ↦
          starRingEnd ℂ
            (bombieriDirectedCorrelation
              (monotoneQuarterNormalizedCell parent (k + lag))
              (monotoneQuarterNormalizedCell parent k) y)) x) +
    ∫ x : ℝ in Set.Ioi 0,
      ((correctedChebyshevPotential
          (quarterLogLatticePoint lag * x) : ℝ) : ℂ) *
        deriv (fun y : ℝ ↦
          starRingEnd ℂ
            (bombieriDirectedCorrelation
              (monotoneQuarterNormalizedCell parent (k + lag))
              (monotoneQuarterNormalizedCell parent k) y)) x

/-- At lag at least three, the physical later--head cross is exactly the
corrected Chebyshev numerator after multiplication by the square-root
dilation factor. -/
theorem sqrt_mul_monotoneQuarterCell_far_globalCross_eq_numerator
    (parent : BombieriTest) (k lag : ℤ) (hfar : 3 ≤ lag) :
    ((Real.sqrt (quarterLogLatticePoint lag) : ℝ) : ℂ) *
        bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent (k + lag))
          (monotoneQuarterCell parent k) =
      monotoneQuarterFarChebyshevNumerator parent k lag := by
  have hindex : (k + lag) - k = lag := by ring
  simpa only [hindex,
      quarterLogLatticeRescale_monotoneQuarterNormalizedCell,
      monotoneQuarterFarChebyshevNumerator] using
    sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_quarterLogLatticeRescale_far_eq_chebyshevError_add_correctedPotential
      (k + lag) k
      (monotoneQuarterNormalizedCell parent (k + lag))
      (monotoneQuarterNormalizedCell parent k) (by simpa only [hindex] using hfar)
      (monotoneQuarterNormalizedCell_tsupport_subset parent (k + lag))
      (monotoneQuarterNormalizedCell_tsupport_subset parent k)

/-- The real contribution of one far cell, with its exact square-root
dilation weight divided out. -/
def monotoneQuarterFarChebyshevContribution
    (parent : BombieriTest) (k lag : ℤ) : ℝ :=
  (monotoneQuarterFarChebyshevNumerator parent k lag).re /
    Real.sqrt (quarterLogLatticePoint lag)

/-- Hermitian symmetry turns the later--head formula into the orientation
needed by monotone propagation: head against later suffix cell. -/
theorem monotoneQuarterCell_far_globalCross_re_eq_contribution
    (parent : BombieriTest) (k lag : ℤ) (hfar : 3 ≤ lag) :
    (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (monotoneQuarterCell parent (k + lag))).re =
        monotoneQuarterFarChebyshevContribution parent k lag := by
  have hraw :=
    sqrt_mul_monotoneQuarterCell_far_globalCross_eq_numerator
      parent k lag hfar
  have hre := congrArg Complex.re hraw
  have hswap :
      (bombieriTwoBlockGlobalCrossSymbol
        (monotoneQuarterCell parent (k + lag))
        (monotoneQuarterCell parent k)).re =
      (bombieriTwoBlockGlobalCrossSymbol
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent (k + lag))).re := by
    have h := congrArg Complex.re
      (bombieriTwoBlockGlobalCrossSymbol_conj_swap
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent (k + lag)))
    simpa only [Complex.star_def, Complex.conj_re] using h
  have hsqrt : 0 < Real.sqrt (quarterLogLatticePoint lag) :=
    Real.sqrt_pos.2 (quarterLogLatticePoint_pos lag)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hre
  rw [hswap] at hre
  unfold monotoneQuarterFarChebyshevContribution
  rw [mul_comm] at hre
  exact (eq_div_iff hsqrt.ne').2 hre

/-! ## The complete finite far row -/

/-- The part of the suffix beginning three lattice steps beyond the head. -/
def monotoneQuarterFarTail
    (parent : BombieriTest) (k : ℤ) (n : ℕ) : BombieriTest :=
  ∑ i ∈ Finset.range n,
    monotoneQuarterCell parent (k + 3 + (i : ℤ))

/-- Additivity converts the full far row into the sum of its exact
Chebyshev contributions. -/
theorem monotoneQuarterCell_farTail_globalCross_re_eq_sum
    (parent : BombieriTest) (k : ℤ) (n : ℕ) :
    (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (monotoneQuarterFarTail parent k n)).re =
        ∑ i ∈ Finset.range n,
          monotoneQuarterFarChebyshevContribution
            parent k (3 + (i : ℤ)) := by
  induction n with
  | zero =>
      simp only [monotoneQuarterFarTail, Finset.range_zero,
        Finset.sum_empty, bombieriTwoBlockGlobalCrossSymbol_zero_right,
        Complex.zero_re]
  | succ n ih =>
      have hcell :=
        monotoneQuarterCell_far_globalCross_re_eq_contribution
          parent k (3 + (n : ℤ)) (by omega)
      have hcell' :
          (bombieriTwoBlockGlobalCrossSymbol
            (monotoneQuarterCell parent k)
            (monotoneQuarterCell parent (k + 3 + (n : ℤ)))).re =
              monotoneQuarterFarChebyshevContribution
                parent k (3 + (n : ℤ)) := by
        simpa only [add_assoc] using hcell
      have ih' :
          (bombieriTwoBlockGlobalCrossSymbol
            (monotoneQuarterCell parent k)
            (∑ i ∈ Finset.range n,
              monotoneQuarterCell parent (k + 3 + (i : ℤ)))).re =
            ∑ i ∈ Finset.range n,
              monotoneQuarterFarChebyshevContribution
                parent k (3 + (i : ℤ)) := by
        simpa only [monotoneQuarterFarTail] using ih
      change
        (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent k)
          (∑ i ∈ Finset.range (n + 1),
            monotoneQuarterCell parent (k + 3 + (i : ℤ)))).re =
          ∑ i ∈ Finset.range (n + 1),
            monotoneQuarterFarChebyshevContribution
              parent k (3 + (i : ℤ))
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        bombieriTwoBlockGlobalCrossSymbol_add_right, Complex.add_re, ih', hcell']

/-- If the cutoff after the far tail vanishes, the whole inner suffix is
the two neighboring cells followed by the finite far tail. -/
theorem monotoneQuarterCutoff_succ_eq_twoNear_add_farTail_of_terminal
    (parent : BombieriTest) (k : ℤ) (n : ℕ)
    (hterminal :
      monotoneQuarterCutoff parent (k + 3 + (n : ℤ)) = 0) :
    monotoneQuarterCutoff parent (k + 1) =
      monotoneQuarterCell parent (k + 1) +
        monotoneQuarterCell parent (k + 2) +
          monotoneQuarterFarTail parent k n := by
  have hfar :=
    sum_range_monotoneQuarterCell_eq_cutoff_sub parent (k + 3) n
  have hindex : (k + 3) + (n : ℤ) = k + 3 + (n : ℤ) := rfl
  have hfar' : monotoneQuarterFarTail parent k n =
      monotoneQuarterCutoff parent (k + 3) := by
    unfold monotoneQuarterFarTail
    rw [hfar, hindex, hterminal, sub_zero]
  rw [monotoneQuarterCutoff_eq_cell_add_next parent (k + 1)]
  have hnext : k + 1 + 1 = k + 2 := by ring
  rw [hnext, monotoneQuarterCutoff_eq_cell_add_next parent (k + 2)]
  have hsucc : k + 2 + 1 = k + 3 := by ring
  rw [hsucc, ← hfar']
  abel

/-- Exact near/far decomposition of the signed head--suffix row.  Only lags
one and two remain as raw Gram entries; every later lag is a corrected
Chebyshev term. -/
theorem monotoneQuarterCell_suffix_globalCross_re_eq_twoNear_add_chebyshev
    (parent : BombieriTest) (k : ℤ) (n : ℕ)
    (hterminal :
      monotoneQuarterCutoff parent (k + 3 + (n : ℤ)) = 0) :
    (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (monotoneQuarterCutoff parent (k + 1))).re =
        (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent (k + 1))).re +
        (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent (k + 2))).re +
        ∑ i ∈ Finset.range n,
          monotoneQuarterFarChebyshevContribution
            parent k (3 + (i : ℤ)) := by
  rw [monotoneQuarterCutoff_succ_eq_twoNear_add_farTail_of_terminal
      parent k n hterminal,
    bombieriTwoBlockGlobalCrossSymbol_add_right,
    bombieriTwoBlockGlobalCrossSymbol_add_right,
    Complex.add_re, Complex.add_re,
    monotoneQuarterCell_farTail_globalCross_re_eq_sum]

/-- The exact universal one-step propagation target, now expressed as two
near Gram entries plus a finite weighted corrected-Chebyshev row.  Proving
the displayed lower bound for real parents would close the monotone route to
RH; no computational truncation or finite prime search is hidden in it. -/
theorem bombieriRealQuadraticValue_cutoff_nonnegative_iff_twoNear_add_chebyshev
    (parent : BombieriTest) (k : ℤ) (n : ℕ)
    (hterminal :
      monotoneQuarterCutoff parent (k + 3 + (n : ℤ)) = 0) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) ↔
      -(bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
          bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1))) / 2 ≤
        (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent (k + 1))).re +
        (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent (k + 2))).re +
        ∑ i ∈ Finset.range n,
          monotoneQuarterFarChebyshevContribution
            parent k (3 + (i : ℤ)) := by
  rw [bombieriRealQuadraticValue_cutoff_nonnegative_iff_oneStep_cross_bound,
    monotoneQuarterCell_suffix_globalCross_re_eq_twoNear_add_chebyshev
      parent k n hterminal]

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutChebyshevFrontierStructural
