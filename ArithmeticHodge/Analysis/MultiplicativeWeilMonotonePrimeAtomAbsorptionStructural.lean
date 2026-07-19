import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRatioTwoBlockPropagationStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotonePropagationLogDefectStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotoneTailConeCriterionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilTwoSeedFactorTwo

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ArithmeticFunction BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAbsorptionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilDirectedCorrelationPhysicalStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilMonotoneRatioTwoBlockPropagationStructural
open MultiplicativeWeilRealLogKernelStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open MultiplicativeWeilRealMonotonePropagationLogDefectStructural
open MultiplicativeWeilRealMonotoneTailConeCriterionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open YoshidaBombieriCrossDistribution

/-!
# Transplanting one Mangoldt atom into a ratio-two plateau

At an actual prime ratio `n >= 2`, the orientation with the head at `n*y`
and the suffix at `y` vanishes.  The surviving orientation can be moved back
to the head scale by normalized dilation by `n`.  We then cut the moved suffix
with the three-step plateau

`s_(k-1) - s_(k+2)`.

This plateau is identically one on the one-cell head and has endpoint ratio
two.  Consequently every scalar combination of the head and the transplanted
slice has nonnegative complete Bombieri quadratic value, and hence satisfies
an honest two-by-two determinant bound.

The determinant does *not* isolate the selected Mangoldt atom.  It controls
the selected atom plus the rest of the translated complete logarithmic
kernel.  The exact remainder and its finite-sum accumulation are recorded
below.  Thus atomwise transplantation supplies a valid reserve, but using it
for monotone propagation requires a new bound on the translated remainders.
-/

/-! ## A ratio-two plateau which is one on the head -/

/-- The maximal ratio-two plateau surrounding the one-cell head. -/
def monotonePrimeAtomPlateauMultiplier (k : ℤ) (x : ℝ) : ℝ :=
  monotoneRatioTwoBlockMultiplier (k - 1) x

/-- The surrounding plateau absorbs the head weight exactly. -/
theorem monotonePrimeAtomPlateauMultiplier_mul_headWeight
    (k : ℤ) (x : ℝ) :
    monotonePrimeAtomPlateauMultiplier k x * monotoneQuarterWeight k x =
      monotoneQuarterWeight k x := by
  unfold monotonePrimeAtomPlateauMultiplier monotoneRatioTwoBlockMultiplier
    monotoneQuarterWeight
  have h₀ : k - 1 < k := by omega
  have h₁ : k - 1 < k + 1 := by omega
  have h₂ : k < k + 2 := by omega
  have h₃ : k + 1 < k + 2 := by omega
  rw [show k - 1 + 3 = k + 2 by omega]
  have hk2k : monotoneQuarterStep (k + 2) x * monotoneQuarterStep k x =
      monotoneQuarterStep (k + 2) x := by
    rw [mul_comm, monotoneQuarterStep_mul_later h₂]
  have hk2k1 : monotoneQuarterStep (k + 2) x *
      monotoneQuarterStep (k + 1) x =
      monotoneQuarterStep (k + 2) x := by
    rw [mul_comm, monotoneQuarterStep_mul_later h₃]
  calc
    (monotoneQuarterStep (k - 1) x - monotoneQuarterStep (k + 2) x) *
        (monotoneQuarterStep k x - monotoneQuarterStep (k + 1) x) =
      monotoneQuarterStep (k - 1) x * monotoneQuarterStep k x -
        monotoneQuarterStep (k - 1) x * monotoneQuarterStep (k + 1) x -
        monotoneQuarterStep (k + 2) x * monotoneQuarterStep k x +
        monotoneQuarterStep (k + 2) x *
          monotoneQuarterStep (k + 1) x := by ring
    _ = monotoneQuarterStep k x - monotoneQuarterStep (k + 1) x := by
      rw [monotoneQuarterStep_mul_later h₀,
        monotoneQuarterStep_mul_later h₁, hk2k, hk2k1]
      ring

/-! ## The transplanted slice -/

/-- Move the inner suffix at the integer ratio `j+1` back to the head scale,
then retain only the ratio-two plateau surrounding the head. -/
def monotonePrimeAtomTransplantedSlice
    (parent : BombieriTest) (k : ℤ) (j : ℕ) : BombieriTest :=
  monotoneRatioTwoBlock
    (normalizedDilation ((j + 1 : ℕ) : ℝ) (by positivity)
      (monotoneQuarterCutoff parent (k + 1)))
    (k - 1)

/-- Pointwise form of the transplanted suffix slice. -/
theorem monotonePrimeAtomTransplantedSlice_apply
    (parent : BombieriTest) (k : ℤ) (j : ℕ) (x : ℝ) :
    monotonePrimeAtomTransplantedSlice parent k j x =
      ((Real.sqrt (((j + 1 : ℕ) : ℝ)) *
        monotonePrimeAtomPlateauMultiplier k x : ℝ) : ℂ) *
        monotoneQuarterCutoff parent (k + 1)
          (((j + 1 : ℕ) : ℝ) * x) := by
  rw [monotonePrimeAtomTransplantedSlice, monotoneRatioTwoBlock_apply,
    normalizedDilation_apply]
  unfold monotonePrimeAtomPlateauMultiplier
  push_cast
  ring

/-- The transplanted slice and the head lie in one common ratio-two box. -/
theorem monotonePrimeAtom_head_add_smul_slice_ratioTwo
    (parent : BombieriTest) (k : ℤ) (j : ℕ) (c : ℂ) :
    BombieriRatioTwoCell
      (monotoneQuarterCell parent k +
        c • monotonePrimeAtomTransplantedSlice parent k j) := by
  refine ⟨quarterLogLatticePoint (k - 1),
    quarterLogLatticePoint (k + 3),
    quarterLogLatticePoint_pos (k - 1),
    quarterLogLatticePoint_mono (by omega), ?_, ?_⟩
  · exact (tsupport_add
      (monotoneQuarterCell parent k : ℝ → ℂ)
      (c • monotonePrimeAtomTransplantedSlice parent k j : BombieriTest)).trans
      (union_subset
        ((monotoneQuarterCell_tsupport_subset parent k).trans
          (Icc_subset_Icc
            (quarterLogLatticePoint_mono (by omega))
            (quarterLogLatticePoint_mono (by omega))))
        ((tsupport_smul_subset_right (fun _x : ℝ ↦ c)
          (monotonePrimeAtomTransplantedSlice parent k j : ℝ → ℂ)).trans
          (by
            simpa only [monotonePrimeAtomTransplantedSlice,
              show k - 1 + 4 = k + 3 by omega] using
              (monotoneRatioTwoBlock_tsupport_subset
                (normalizedDilation ((j + 1 : ℕ) : ℝ) (by positivity)
                  (monotoneQuarterCutoff parent (k + 1))) (k - 1)))))
  · have hindex : k - 1 + 4 = k + 3 := by omega
    rw [← hindex, quarterLogLatticePoint_add_four]
    exact le_of_eq
      (mul_div_cancel_right₀ 2 (quarterLogLatticePoint_pos (k - 1)).ne')

/-- Every scalar pencil formed from the head and the transplanted slice is
therefore nonnegative by the already-proved ratio-two theorem. -/
theorem bombieriFunctional_head_add_smul_transplantedSlice_nonnegative
    (parent : BombieriTest) (k : ℤ) (j : ℕ) (c : ℂ) :
    0 ≤ (bombieriFunctional (bombieriQuadraticTest
      (monotoneQuarterCell parent k +
        c • monotonePrimeAtomTransplantedSlice parent k j))).re := by
  exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
    (monotonePrimeAtom_head_add_smul_slice_ratioTwo parent k j c)

/-! ## Exact transport of the surviving prime orientation -/

/-- At a nontrivial integer ratio the head-at-the-dilated-point orientation
vanishes before integration. -/
theorem bombieriDirectedCorrelation_head_suffix_eq_zero
    (parent : BombieriTest) (k : ℤ) (j : ℕ) (hj : 1 ≤ j) :
    bombieriDirectedCorrelation
      (monotoneQuarterCell parent k)
      (monotoneQuarterCutoff parent (k + 1)) ((j + 1 : ℕ) : ℝ) = 0 := by
  unfold bombieriDirectedCorrelation
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hx : (2 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ j + 1 by omega)
  have hmask := monotoneOneCellForwardPrimeMask_eq_zero_of_two_le
    k hx hy.le
  rw [monotoneQuarterCell_apply, monotoneQuarterCutoff_apply,
    map_mul (starRingEnd ℂ), Complex.conj_ofReal]
  unfold monotoneOneCellForwardPrimeMask at hmask
  calc
    (monotoneQuarterWeight k (((j + 1 : ℕ) : ℝ) * y) : ℂ) *
          parent (((j + 1 : ℕ) : ℝ) * y) *
        ((monotoneQuarterStep (k + 1) y : ℂ) *
          starRingEnd ℂ (parent y)) =
      ((monotoneQuarterWeight k (((j + 1 : ℕ) : ℝ) * y) *
        monotoneQuarterStep (k + 1) y : ℝ) : ℂ) *
        (parent (((j + 1 : ℕ) : ℝ) * y) *
          starRingEnd ℂ (parent y)) := by
            push_cast
            ring
    _ = 0 := by rw [hmask]; simp

/-- The zero-lag overlap of the moved slice with the head is exactly
`sqrt (j+1)` times the surviving directed prime correlation. -/
theorem bombieriDirectedCorrelation_transplantedSlice_head_one
    (parent : BombieriTest) (k : ℤ) (j : ℕ) :
    bombieriDirectedCorrelation
      (monotonePrimeAtomTransplantedSlice parent k j)
      (monotoneQuarterCell parent k) 1 =
      ((Real.sqrt (((j + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        bombieriDirectedCorrelation
          (monotoneQuarterCutoff parent (k + 1))
          (monotoneQuarterCell parent k) ((j + 1 : ℕ) : ℝ) := by
  unfold bombieriDirectedCorrelation
  calc
    (∫ y : ℝ in Set.Ioi 0,
        monotonePrimeAtomTransplantedSlice parent k j (1 * y) *
          starRingEnd ℂ (monotoneQuarterCell parent k y)) =
      ∫ y : ℝ in Set.Ioi 0,
        ((Real.sqrt (((j + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
          (monotoneQuarterCutoff parent (k + 1)
              (((j + 1 : ℕ) : ℝ) * y) *
            starRingEnd ℂ (monotoneQuarterCell parent k y)) := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [one_mul, monotonePrimeAtomTransplantedSlice_apply,
          monotoneQuarterCell_apply, map_mul (starRingEnd ℂ),
          Complex.conj_ofReal]
        have habsorb :=
          monotonePrimeAtomPlateauMultiplier_mul_headWeight k y
        calc
          ((Real.sqrt (((j + 1 : ℕ) : ℝ)) *
                monotonePrimeAtomPlateauMultiplier k y : ℝ) : ℂ) *
                monotoneQuarterCutoff parent (k + 1)
                  (((j + 1 : ℕ) : ℝ) * y) *
              ((monotoneQuarterWeight k y : ℂ) *
                starRingEnd ℂ (parent y)) =
            ((Real.sqrt (((j + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
              ((monotonePrimeAtomPlateauMultiplier k y *
                    monotoneQuarterWeight k y : ℝ) : ℂ) *
                (monotoneQuarterCutoff parent (k + 1)
                    (((j + 1 : ℕ) : ℝ) * y) *
                  starRingEnd ℂ (parent y)) := by
                    push_cast
                    ring
          _ = ((Real.sqrt (((j + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
              (monotoneQuarterCutoff parent (k + 1)
                  (((j + 1 : ℕ) : ℝ) * y) *
                ((monotoneQuarterWeight k y : ℂ) *
                  starRingEnd ℂ (parent y))) := by
                    rw [habsorb]
                    ring
    _ = ((Real.sqrt (((j + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        ∫ y : ℝ in Set.Ioi 0,
          monotoneQuarterCutoff parent (k + 1)
              (((j + 1 : ℕ) : ℝ) * y) *
            starRingEnd ℂ (monotoneQuarterCell parent k y) := by
      exact MeasureTheory.integral_const_mul _ _

/-- The real value of the selected symmetric logarithmic Mangoldt atom in the
head--suffix cross. -/
def monotonePrimeAtomValue
    (parent : BombieriTest) (k : ℤ) (j : ℕ) : ℝ :=
  (bombieriLogPrimeAtomCrossSummand
    (monotoneQuarterCell parent k)
    (monotoneQuarterCutoff parent (k + 1)) j).re

/-- Individual (rather than merely summed) identification of the logarithmic
atom with its two physical directed orientations. -/
theorem monotonePrimeAtomValue_eq_directedShell_re
    (parent : BombieriTest) (k : ℤ) (j : ℕ) :
    monotonePrimeAtomValue parent k j =
      (((ArithmeticFunction.vonMangoldt (j + 1) : ℝ) : ℂ) *
        (bombieriDirectedCorrelation
            (monotoneQuarterCutoff parent (k + 1))
            (monotoneQuarterCell parent k) ((j + 1 : ℕ) : ℝ) +
          starRingEnd ℂ
            (bombieriDirectedCorrelation
              (monotoneQuarterCell parent k)
              (monotoneQuarterCutoff parent (k + 1))
              ((j + 1 : ℕ) : ℝ)))).re := by
  let n : ℝ := ((j + 1 : ℕ) : ℝ)
  have hn : 0 < n := by dsimp only [n]; positivity
  have hsqrt : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [← Real.exp_log (Real.sqrt_pos.2 hn), Real.log_sqrt hn.le]
  have hsqrt0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hn).ne'
  have hfg :=
    bombieriCriticalCrossCorrelation_eq_exp_mul_star_directedCorrelation
      (monotoneQuarterCell parent k)
      (monotoneQuarterCutoff parent (k + 1)) (Real.log n)
  have hgf :=
    bombieriCriticalCrossCorrelation_eq_exp_mul_star_directedCorrelation
      (monotoneQuarterCutoff parent (k + 1))
      (monotoneQuarterCell parent k) (Real.log n)
  rw [Real.exp_log hn, hsqrt] at hfg hgf
  have hneg := bombieriCriticalCrossCorrelation_neg_eq_star_swap
    (monotoneQuarterCell parent k)
    (monotoneQuarterCutoff parent (k + 1)) (Real.log n)
  have hshell :
      bombieriLogPrimeAtomCrossSummand
          (monotoneQuarterCell parent k)
          (monotoneQuarterCutoff parent (k + 1)) j =
        (ArithmeticFunction.vonMangoldt (j + 1) : ℂ) *
          (bombieriDirectedCorrelation
              (monotoneQuarterCutoff parent (k + 1))
              (monotoneQuarterCell parent k) ((j + 1 : ℕ) : ℝ) +
            starRingEnd ℂ
              (bombieriDirectedCorrelation
                (monotoneQuarterCell parent k)
                (monotoneQuarterCutoff parent (k + 1))
                ((j + 1 : ℕ) : ℝ))) := by
    unfold bombieriLogPrimeAtomCrossSummand bombieriLogPrimeAtomWeight
    change ((ArithmeticFunction.vonMangoldt (j + 1) *
        (Real.sqrt n)⁻¹ : ℝ) : ℂ) *
          (bombieriCriticalCrossCorrelation
              (monotoneQuarterCell parent k)
              (monotoneQuarterCutoff parent (k + 1)) (-Real.log n) +
            bombieriCriticalCrossCorrelation
              (monotoneQuarterCell parent k)
              (monotoneQuarterCutoff parent (k + 1)) (Real.log n)) = _
    rw [hneg, hgf, hfg]
    simp only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
    push_cast
    field_simp [hsqrt0]
    norm_num [n, Nat.cast_add, Nat.cast_one]
  exact congrArg Complex.re hshell

/-- For `j >= 1`, the symmetric logarithmic atom is exactly the surviving
physical orientation, weighted by `vonMangoldt (j+1)`. -/
theorem monotonePrimeAtomValue_eq_survivingDirected
    (parent : BombieriTest) (k : ℤ) (j : ℕ) (hj : 1 ≤ j) :
    monotonePrimeAtomValue parent k j =
      ArithmeticFunction.vonMangoldt (j + 1) *
        (bombieriDirectedCorrelation
          (monotoneQuarterCutoff parent (k + 1))
          (monotoneQuarterCell parent k) ((j + 1 : ℕ) : ℝ)).re := by
  let n : ℝ := ((j + 1 : ℕ) : ℝ)
  have hn : 0 < n := by dsimp only [n]; positivity
  have hsqrt : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [← Real.exp_log (Real.sqrt_pos.2 hn), Real.log_sqrt hn.le]
  have hsqrt0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hn).ne'
  have hpos :=
    bombieriCriticalCrossCorrelation_eq_exp_mul_star_directedCorrelation
      (monotoneQuarterCell parent k)
      (monotoneQuarterCutoff parent (k + 1)) (Real.log n)
  have hswap :=
    bombieriCriticalCrossCorrelation_eq_exp_mul_star_directedCorrelation
      (monotoneQuarterCutoff parent (k + 1))
      (monotoneQuarterCell parent k) (Real.log n)
  rw [Real.exp_log hn, hsqrt] at hpos hswap
  have hneg := bombieriCriticalCrossCorrelation_neg_eq_star_swap
    (monotoneQuarterCell parent k)
    (monotoneQuarterCutoff parent (k + 1)) (Real.log n)
  have hforward := bombieriDirectedCorrelation_head_suffix_eq_zero
    parent k j hj
  change bombieriDirectedCorrelation
      (monotoneQuarterCell parent k)
      (monotoneQuarterCutoff parent (k + 1)) n = 0 at hforward
  unfold monotonePrimeAtomValue bombieriLogPrimeAtomCrossSummand
    bombieriLogPrimeAtomWeight
  change (((ArithmeticFunction.vonMangoldt (j + 1) *
      (Real.sqrt n)⁻¹ : ℝ) : ℂ) *
      (bombieriCriticalCrossCorrelation
          (monotoneQuarterCell parent k)
          (monotoneQuarterCutoff parent (k + 1)) (-Real.log n) +
        bombieriCriticalCrossCorrelation
          (monotoneQuarterCell parent k)
          (monotoneQuarterCutoff parent (k + 1)) (Real.log n))).re = _
  rw [hneg, hswap, hpos, hforward]
  simp only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply,
    map_zero, mul_zero, add_zero, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  field_simp [hsqrt0]
  norm_num [n, Nat.cast_add, Nat.cast_one]

/-- The individual atom sequence is actually finitely supported.  This
follows from the finite support of the two prime-polarization summands, not
from totalized summation. -/
theorem monotonePrimeAtomValue_hasFiniteSupport
    (parent : BombieriTest) (k : ℤ) :
    Function.HasFiniteSupport (monotonePrimeAtomValue parent k) := by
  let f := monotoneQuarterCell parent k
  let g := monotoneQuarterCutoff parent (k + 1)
  let s₁ : ℕ → ℂ := vonMangoldtPrimeSummand
    (bombieriQuadraticCrossTest f g)
  let s₂ : ℕ → ℂ := vonMangoldtPrimeSummand
    (bombieriQuadraticCrossTest f (Complex.I • g))
  have hs₁ : Function.HasFiniteSupport s₁ := by
    exact vonMangoldtPrimeSummand_hasFiniteSupport _
  have hs₂ : Function.HasFiniteSupport s₂ := by
    exact vonMangoldtPrimeSummand_hasFiniteSupport _
  refine ((hs₁.union hs₂).union (Set.finite_singleton 0)).subset ?_
  intro j hj
  change monotonePrimeAtomValue parent k j ≠ 0 at hj
  by_contra hmem
  have hjnot : j ∉ Function.support s₁ ∪ Function.support s₂ := by
    intro h
    exact hmem (Or.inl h)
  have hj0 : j ≠ 0 := by
    intro h
    subst j
    exact hmem (Or.inr (by simp))
  have hs₁zero : s₁ j = 0 := by
    rw [← not_ne_iff]
    exact fun h ↦ hjnot (Or.inl h)
  have hs₂zero : s₂ j = 0 := by
    rw [← not_ne_iff]
    exact fun h ↦ hjnot (Or.inr h)
  have hpol := vonMangoldtPrimeSummand_polarization_eq_directedShell f g j
  change (((s₁ j).re / 2 : ℝ) : ℂ) -
      (((s₂ j).re / 2 : ℝ) : ℂ) * Complex.I = _ at hpol
  rw [hs₁zero, hs₂zero] at hpol
  have hpolzero :
      (ArithmeticFunction.vonMangoldt (j + 1) : ℂ) *
        (bombieriDirectedCorrelation g f ((j + 1 : ℕ) : ℝ) +
          starRingEnd ℂ
            (bombieriDirectedCorrelation f g ((j + 1 : ℕ) : ℝ))) = 0 := by
    simpa using hpol.symm
  have hatom := monotonePrimeAtomValue_eq_directedShell_re parent k j
  change monotonePrimeAtomValue parent k j =
    (((ArithmeticFunction.vonMangoldt (j + 1) : ℝ) : ℂ) *
      (bombieriDirectedCorrelation g f ((j + 1 : ℕ) : ℝ) +
        starRingEnd ℂ
          (bombieriDirectedCorrelation f g ((j + 1 : ℕ) : ℝ)))).re at hatom
  rw [hpolzero] at hatom
  norm_num at hatom
  exact hj hatom

/-- Hence there always exists an ordinary finite set containing every
nonzero head--suffix Mangoldt atom. -/
theorem exists_finset_monotonePrimeAtom_support
    (parent : BombieriTest) (k : ℤ) :
    ∃ S : Finset ℕ, ∀ j ∉ S, monotonePrimeAtomValue parent k j = 0 := by
  let hfinite := monotonePrimeAtomValue_hasFiniteSupport parent k
  refine ⟨hfinite.toFinset, ?_⟩
  intro j hj
  by_contra hne
  exact hj (hfinite.mem_toFinset.mpr hne)

/-- Equivalently, one prime atom is the zero-lag overlap with the ratio-two
transplanted slice, multiplied by the usual logarithmic atom weight. -/
theorem monotonePrimeAtomValue_eq_weight_mul_transplantedOverlap
    (parent : BombieriTest) (k : ℤ) (j : ℕ) (hj : 1 ≤ j) :
    monotonePrimeAtomValue parent k j =
      bombieriLogPrimeAtomWeight j *
        (bombieriDirectedCorrelation
          (monotonePrimeAtomTransplantedSlice parent k j)
          (monotoneQuarterCell parent k) 1).re := by
  rw [monotonePrimeAtomValue_eq_survivingDirected parent k j hj,
    bombieriDirectedCorrelation_transplantedSlice_head_one]
  unfold bombieriLogPrimeAtomWeight
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have hsqrt0 : Real.sqrt (((j + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hsqrt0]

/-! ## What the ratio-two determinant actually controls -/

/-- Complete quadratic reserve of the transplanted slice. -/
def monotonePrimeAtomTransplantedReserve
    (parent : BombieriTest) (k : ℤ) (j : ℕ) : ℝ :=
  bombieriRealQuadraticValue
    (monotonePrimeAtomTransplantedSlice parent k j)

/-- Complete head--transplanted-slice cross. -/
def monotonePrimeAtomTransportedCross
    (parent : BombieriTest) (k : ℤ) (j : ℕ) : ℂ :=
  bombieriTwoBlockGlobalCrossSymbol
    (monotoneQuarterCell parent k)
    (monotonePrimeAtomTransplantedSlice parent k j)

/-- The exact part of the weighted translated complete kernel not equal to
the selected zero-lag Mangoldt overlap. -/
def monotonePrimeAtomTransportRemainder
    (parent : BombieriTest) (k : ℤ) (j : ℕ) : ℝ :=
  bombieriLogPrimeAtomWeight j *
      (monotonePrimeAtomTransportedCross parent k j).re -
    monotonePrimeAtomValue parent k j

/-- The unconditional ratio-two pencil gives an honest determinant for the
head and the transplanted slice. -/
theorem monotonePrimeAtom_transportedCross_determinant
    (parent : BombieriTest) (k : ℤ) (j : ℕ) :
    Complex.normSq (monotonePrimeAtomTransportedCross parent k j) ≤
      bombieriRealQuadraticValue (monotoneQuarterCell parent k) *
        monotonePrimeAtomTransplantedReserve parent k j := by
  have hhead : 0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterCell parent k) := by
    unfold bombieriRealQuadraticValue
    exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
      (monotoneQuarterCell_ratioTwo parent k)
  have hslice : 0 ≤ monotonePrimeAtomTransplantedReserve parent k j := by
    unfold monotonePrimeAtomTransplantedReserve bombieriRealQuadraticValue
    exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
      (monotoneRatioTwoBlock_ratioTwo _ (k - 1))
  apply (twoSeedHermitian_nonneg_iff
    (bombieriRealQuadraticValue (monotoneQuarterCell parent k))
    (monotonePrimeAtomTransplantedReserve parent k j)
    (monotonePrimeAtomTransportedCross parent k j) hhead hslice).1
  intro c
  have hnonneg :=
    bombieriFunctional_head_add_smul_transplantedSlice_nonnegative
      parent k j c
  rw [bombieriFunctional_twoBlock_re] at hnonneg
  simpa only [twoSeedHermitianValue, bombieriRealQuadraticValue,
    monotonePrimeAtomTransplantedReserve,
    monotonePrimeAtomTransportedCross] using hnonneg

/-- After weighting, the determinant controls the square of "selected atom
plus translated-kernel remainder", not the selected atom alone. -/
theorem monotonePrimeAtom_atom_add_remainder_sq_le
    (parent : BombieriTest) (k : ℤ) (j : ℕ) :
    (monotonePrimeAtomValue parent k j +
        monotonePrimeAtomTransportRemainder parent k j) ^ 2 ≤
      bombieriLogPrimeAtomWeight j ^ 2 *
        (bombieriRealQuadraticValue (monotoneQuarterCell parent k) *
          monotonePrimeAtomTransplantedReserve parent k j) := by
  have hdet := monotonePrimeAtom_transportedCross_determinant parent k j
  have hre : (monotonePrimeAtomTransportedCross parent k j).re ^ 2 ≤
      Complex.normSq (monotonePrimeAtomTransportedCross parent k j) := by
    simp only [Complex.normSq_apply]
    nlinarith [sq_nonneg (monotonePrimeAtomTransportedCross parent k j).im]
  have hweighted := mul_le_mul_of_nonneg_left (hre.trans hdet)
    (sq_nonneg (bombieriLogPrimeAtomWeight j))
  unfold monotonePrimeAtomTransportRemainder
  nlinarith

/-- The sharp arithmetic-mean consequence of the transported determinant.
The selected atom is bounded by the weighted head reserve and the new slice
reserve, but only after paying the signed translated-kernel remainder. -/
theorem two_mul_monotonePrimeAtomValue_le_transported_reserves
    (parent : BombieriTest) (k : ℤ) (j : ℕ) :
    2 * monotonePrimeAtomValue parent k j ≤
      bombieriLogPrimeAtomWeight j ^ 2 *
          bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
        monotonePrimeAtomTransplantedReserve parent k j -
        2 * monotonePrimeAtomTransportRemainder parent k j := by
  let A := monotonePrimeAtomValue parent k j
  let R := monotonePrimeAtomTransportRemainder parent k j
  let w := bombieriLogPrimeAtomWeight j
  let H := bombieriRealQuadraticValue (monotoneQuarterCell parent k)
  let T := monotonePrimeAtomTransplantedReserve parent k j
  have hsq : (A + R) ^ 2 ≤ w ^ 2 * (H * T) := by
    simpa only [A, R, w, H, T] using
      monotonePrimeAtom_atom_add_remainder_sq_le parent k j
  have hH : 0 ≤ H := by
    dsimp only [H, bombieriRealQuadraticValue]
    exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
      (monotoneQuarterCell_ratioTwo parent k)
  have hT : 0 ≤ T := by
    dsimp only [T, monotonePrimeAtomTransplantedReserve,
      bombieriRealQuadraticValue]
    exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
      (monotoneRatioTwoBlock_ratioTwo _ (k - 1))
  have hwH : 0 ≤ w ^ 2 * H := mul_nonneg (sq_nonneg w) hH
  have hmean : 2 * (A + R) ≤ w ^ 2 * H + T := by
    nlinarith [sq_nonneg (w ^ 2 * H - T)]
  simpa only [A, R, w, H, T] using (show
    2 * A ≤ w ^ 2 * H + T - 2 * R by linarith)

/-- Concrete finite atomwise budget obtained by summing the preceding
arithmetic-mean bounds. -/
def monotonePrimeAtomFiniteAbsorptionBudget
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) : ℝ :=
  ∑ j ∈ S, (
    bombieriLogPrimeAtomWeight j ^ 2 *
        bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
      monotonePrimeAtomTransplantedReserve parent k j -
      2 * monotonePrimeAtomTransportRemainder parent k j)

/-- Summing the valid atomwise determinant bounds gives exactly the displayed
finite budget; no translated remainder is discarded. -/
theorem two_mul_monotonePrimeAtom_finset_sum_le_budget
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    2 * (∑ j ∈ S, monotonePrimeAtomValue parent k j) ≤
      monotonePrimeAtomFiniteAbsorptionBudget parent k S := by
  rw [Finset.mul_sum]
  unfold monotonePrimeAtomFiniteAbsorptionBudget
  exact Finset.sum_le_sum fun j _hj ↦
    two_mul_monotonePrimeAtomValue_le_transported_reserves parent k j

/-- The explicit logarithmic head--suffix prime cross is exactly the sum of
the individual real atom values above. -/
theorem monotoneQuarterHeadSuffixRealPrimeCross_eq_tsum_primeAtomValue
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterHeadSuffixRealPrimeCross parent k =
      ∑' j : ℕ, monotonePrimeAtomValue parent k j := by
  unfold monotoneQuarterHeadSuffixRealPrimeCross monotonePrimeAtomValue
    bombieriLogPrimeAtomCrossSummand
  apply tsum_congr
  intro j
  rw [bombieriCriticalCrossCorrelation_cell_cutoff_eq_parentLogMultiplier,
    bombieriCriticalCrossCorrelation_cell_cutoff_eq_parentLogMultiplier]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_re]

/-- Any finite set containing the nonzero atoms realizes the complete prime
cross as an ordinary finite sum. -/
theorem monotoneQuarterHeadSuffixRealPrimeCross_eq_finset
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hout : ∀ j ∉ S, monotonePrimeAtomValue parent k j = 0) :
    monotoneQuarterHeadSuffixRealPrimeCross parent k =
      ∑ j ∈ S, monotonePrimeAtomValue parent k j := by
  rw [monotoneQuarterHeadSuffixRealPrimeCross_eq_tsum_primeAtomValue]
  exact tsum_eq_sum hout

/-- A genuine sufficient one-step propagation theorem from atomwise
transplantation.  The budget retains the complete archimedean cross.  Its
unproved content is now explicit: the weighted slice reserves and signed
translated remainders must fit inside the original head--suffix reserve plus
twice the archimedean term. -/
theorem monotoneQuarterCutoff_nonnegative_of_primeAtom_absorptionBudget
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hout : ∀ j ∉ S, monotonePrimeAtomValue parent k j = 0)
    (hbudget :
      monotonePrimeAtomFiniteAbsorptionBudget parent k S -
          2 * monotoneQuarterHeadSuffixRealArchimedeanCross parent k ≤
        bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
          bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1))) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) := by
  have hatoms := two_mul_monotonePrimeAtom_finset_sum_le_budget
    parent k S
  have hprime :=
    monotoneQuarterHeadSuffixRealPrimeCross_eq_finset parent k S hout
  rw [← hprime] at hatoms
  unfold bombieriRealQuadraticValue
  apply (monotoneQuarterCutoff_nonnegative_iff_logDefect_lowerBound
    parent k).2
  rw [monotoneQuarterRealLogStepDefect_eq_archimedean_sub_mangoldt]
  change -((bombieriRealQuadraticValue (monotoneQuarterCell parent k)) +
      bombieriRealQuadraticValue
        (monotoneQuarterCutoff parent (k + 1))) ≤
    2 * monotoneQuarterHeadSuffixRealArchimedeanCross parent k -
      2 * monotoneQuarterHeadSuffixRealPrimeCross parent k
  linarith

/-- Exact finite accumulation of the translated remainders.  This is the
term an atom-by-atom reserve argument must retain when the atoms are summed. -/
theorem monotonePrimeAtom_finset_sum_eq_transport_sub_remainder
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    (∑ j ∈ S, monotonePrimeAtomValue parent k j) =
      (∑ j ∈ S, bombieriLogPrimeAtomWeight j *
        (monotonePrimeAtomTransportedCross parent k j).re) -
      ∑ j ∈ S, monotonePrimeAtomTransportRemainder parent k j := by
  simp_rw [monotonePrimeAtomTransportRemainder]
  rw [Finset.sum_sub_distrib]
  ring

/-! ## Algebraic sharpness of the leftover -/

/-- A determinant for `atom + remainder` cannot by itself bound the atom:
the remainder may cancel an arbitrarily large positive atom while both
diagonal reserves vanish.  Any successful atomwise absorption must therefore
control the translated-kernel remainder (and, after summation, its signed
accumulation). -/
theorem translatedDeterminant_does_not_bound_atom
    (A : ℝ) (hA : 0 < A) :
    ∃ H T R : ℝ,
      0 ≤ H ∧ 0 ≤ T ∧ (A + R) ^ 2 ≤ H * T ∧ H + T < 2 * A := by
  exact ⟨0, 0, -A, le_rfl, le_rfl, by norm_num, by linarith⟩

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAbsorptionStructural
