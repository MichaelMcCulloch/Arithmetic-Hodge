import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCutPencilStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeCoherentFejerDecompositionStructural

set_option autoImplicit false

open Complex Finset Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCutMaskGeometryStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilCoherentCutPencilStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural

/-!
# Geometry of a coherent quarter-lattice cut mask

The head and suffix coefficients form a rank-one two-point matrix before the
Bombieri functional is applied.  Its symmetric and antisymmetric coordinates
therefore satisfy an exact determinant identity.  This identity also exposes
a sharp obstruction: unless the head-to-suffix ratio agrees at the two
correlated points, the real-phase mask is negative for one real scalar.  Thus
pointwise positivity of the parent mask cannot prove the required cut-pencil
inequality; any successful proof has to retain cancellation in the Bombieri
functional.
-/

/-- The symmetric and antisymmetric mixed masks have the exact rank-one
determinant relation. -/
theorem coherentCut_symmetric_sq_sub_antisymmetric_sq
    (eta : ℤ → ℝ → ℝ) (cut hi : ℤ) (x y : ℝ) :
    coherentCutSymmetricMask eta cut hi x y ^ 2 -
        coherentCutAntisymmetricMask eta cut hi x y ^ 2 =
      4 * coherentCutHeadDiagonalMask eta cut x y *
        coherentCutSuffixDiagonalMask eta cut hi x y := by
  unfold coherentCutSymmetricMask coherentCutAntisymmetricMask
    coherentCutHeadDiagonalMask coherentCutSuffixDiagonalMask
  ring

/-- Completing the square in the real phase leaves exactly the square of the
antisymmetric mask as the defect. -/
theorem coherentCut_realPhase_completeSquare
    (eta : ℤ → ℝ → ℝ) (cut hi : ℤ) (a x y : ℝ) :
    4 * coherentCutSuffixDiagonalMask eta cut hi x y *
        (coherentCutHeadDiagonalMask eta cut x y +
          a ^ 2 * coherentCutSuffixDiagonalMask eta cut hi x y +
          a * coherentCutSymmetricMask eta cut hi x y) =
      (2 * coherentCutSuffixDiagonalMask eta cut hi x y * a +
          coherentCutSymmetricMask eta cut hi x y) ^ 2 -
        coherentCutAntisymmetricMask eta cut hi x y ^ 2 := by
  have hdet := coherentCut_symmetric_sq_sub_antisymmetric_sq
    eta cut hi x y
  nlinarith

/-- At the vertex of the real-phase quadratic, the pointwise mask is the
negative antisymmetric determinant defect. -/
theorem coherentCut_realPhase_vertex
    (eta : ℤ → ℝ → ℝ) (cut hi : ℤ) (x y : ℝ)
    (hSuffix : coherentCutSuffixDiagonalMask eta cut hi x y ≠ 0) :
    coherentCutHeadDiagonalMask eta cut x y +
        (-coherentCutSymmetricMask eta cut hi x y /
            (2 * coherentCutSuffixDiagonalMask eta cut hi x y)) ^ 2 *
          coherentCutSuffixDiagonalMask eta cut hi x y +
        (-coherentCutSymmetricMask eta cut hi x y /
            (2 * coherentCutSuffixDiagonalMask eta cut hi x y)) *
          coherentCutSymmetricMask eta cut hi x y =
      -coherentCutAntisymmetricMask eta cut hi x y ^ 2 /
        (4 * coherentCutSuffixDiagonalMask eta cut hi x y) := by
  field_simp [hSuffix]
  nlinarith [coherentCut_symmetric_sq_sub_antisymmetric_sq eta cut hi x y]

/-- A nonzero antisymmetric mask forces a strictly negative pointwise real
phase whenever the suffix diagonal is positive. -/
theorem coherentCut_exists_realPhaseMask_neg
    (eta : ℤ → ℝ → ℝ) (cut hi : ℤ) (x y : ℝ)
    (hSuffix : 0 < coherentCutSuffixDiagonalMask eta cut hi x y)
    (hAnti : coherentCutAntisymmetricMask eta cut hi x y ≠ 0) :
    ∃ a : ℝ,
      coherentCutHeadDiagonalMask eta cut x y +
          a ^ 2 * coherentCutSuffixDiagonalMask eta cut hi x y +
          a * coherentCutSymmetricMask eta cut hi x y < 0 := by
  let a : ℝ := -coherentCutSymmetricMask eta cut hi x y /
    (2 * coherentCutSuffixDiagonalMask eta cut hi x y)
  refine ⟨a, ?_⟩
  rw [show coherentCutHeadDiagonalMask eta cut x y +
      a ^ 2 * coherentCutSuffixDiagonalMask eta cut hi x y +
      a * coherentCutSymmetricMask eta cut hi x y =
        -coherentCutAntisymmetricMask eta cut hi x y ^ 2 /
          (4 * coherentCutSuffixDiagonalMask eta cut hi x y) by
    exact coherentCut_realPhase_vertex eta cut hi x y hSuffix.ne']
  exact div_neg_of_neg_of_pos
    (neg_lt_zero.mpr (sq_pos_of_ne_zero hAnti)) (by positivity)

/-- Sharp pointwise criterion: with positive suffix diagonal, all real phases
are nonnegative exactly when the antisymmetric mask vanishes. -/
theorem coherentCut_all_realPhaseMask_nonneg_iff_antisymmetric_eq_zero
    (eta : ℤ → ℝ → ℝ) (cut hi : ℤ) (x y : ℝ)
    (hSuffix : 0 < coherentCutSuffixDiagonalMask eta cut hi x y) :
    (∀ a : ℝ,
        0 ≤ coherentCutHeadDiagonalMask eta cut x y +
          a ^ 2 * coherentCutSuffixDiagonalMask eta cut hi x y +
          a * coherentCutSymmetricMask eta cut hi x y) ↔
      coherentCutAntisymmetricMask eta cut hi x y = 0 := by
  constructor
  · intro hall
    by_contra hne
    obtain ⟨a, ha⟩ := coherentCut_exists_realPhaseMask_neg
      eta cut hi x y hSuffix hne
    exact (not_lt_of_ge (hall a)) ha
  · intro hAnti a
    have hsquare := coherentCut_realPhase_completeSquare eta cut hi a x y
    rw [hAnti] at hsquare
    norm_num at hsquare
    nlinarith [sq_nonneg
      (2 * coherentCutSuffixDiagonalMask eta cut hi x y * a +
        coherentCutSymmetricMask eta cut hi x y)]

/-- Nonnegative coherent weights give a nonnegative cumulative suffix mask. -/
theorem coherentCutSuffixMask_nonnegative
    (eta : ℤ → ℝ → ℝ)
    (hnonneg : ∀ k z, 0 ≤ eta k z) (cut hi : ℤ) (z : ℝ) :
    0 ≤ coherentCutSuffixMask eta cut hi z := by
  unfold coherentCutSuffixMask
  exact Finset.sum_nonneg fun k _hk ↦ hnonneg k z

theorem coherentCutHeadDiagonalMask_nonnegative
    (eta : ℤ → ℝ → ℝ) (hnonneg : ∀ k z, 0 ≤ eta k z)
    (cut : ℤ) (x y : ℝ) :
    0 ≤ coherentCutHeadDiagonalMask eta cut x y := by
  unfold coherentCutHeadDiagonalMask
  exact mul_nonneg (hnonneg cut (x * y)) (hnonneg cut y)

theorem coherentCutSuffixDiagonalMask_nonnegative
    (eta : ℤ → ℝ → ℝ) (hnonneg : ∀ k z, 0 ≤ eta k z)
    (cut hi : ℤ) (x y : ℝ) :
    0 ≤ coherentCutSuffixDiagonalMask eta cut hi x y := by
  unfold coherentCutSuffixDiagonalMask
  exact mul_nonneg
    (coherentCutSuffixMask_nonnegative eta hnonneg cut hi (x * y))
    (coherentCutSuffixMask_nonnegative eta hnonneg cut hi y)

theorem coherentCutSymmetricMask_nonnegative
    (eta : ℤ → ℝ → ℝ) (hnonneg : ∀ k z, 0 ≤ eta k z)
    (cut hi : ℤ) (x y : ℝ) :
    0 ≤ coherentCutSymmetricMask eta cut hi x y := by
  unfold coherentCutSymmetricMask
  exact add_nonneg
    (mul_nonneg
      (coherentCutSuffixMask_nonnegative eta hnonneg cut hi (x * y))
      (hnonneg cut y))
    (mul_nonneg (hnonneg cut (x * y))
      (coherentCutSuffixMask_nonnegative eta hnonneg cut hi y))

/-- The imaginary-phase mask is pointwise dominated in absolute value by the
real symmetric cross mask.  Equality is possible on a full cross-transition,
so this estimate has no uniform slack. -/
theorem abs_coherentCutAntisymmetricMask_le_symmetricMask
    (eta : ℤ → ℝ → ℝ) (hnonneg : ∀ k z, 0 ≤ eta k z)
    (cut hi : ℤ) (x y : ℝ) :
    |coherentCutAntisymmetricMask eta cut hi x y| ≤
      coherentCutSymmetricMask eta cut hi x y := by
  let u := coherentCutSuffixMask eta cut hi (x * y) * eta cut y
  let v := eta cut (x * y) * coherentCutSuffixMask eta cut hi y
  have hu : 0 ≤ u := mul_nonneg
    (coherentCutSuffixMask_nonnegative eta hnonneg cut hi (x * y))
    (hnonneg cut y)
  have hv : 0 ≤ v := mul_nonneg (hnonneg cut (x * y))
    (coherentCutSuffixMask_nonnegative eta hnonneg cut hi y)
  change |u - v| ≤ u + v
  calc
    |u - v| ≤ |u| + |v| := abs_sub u v
    _ = u + v := by rw [abs_of_nonneg hu, abs_of_nonneg hv]

/-- For the actual nonnegative partition weights, the antisymmetric mask is
the only pointwise obstruction in every case, including degenerate suffix
diagonals.  A nonzero defect makes the quadratic either have a negative
vertex or become a nonconstant affine function. -/
theorem coherentCut_all_realPhaseMask_nonneg_iff_of_nonnegative
    (eta : ℤ → ℝ → ℝ) (hnonneg : ∀ k z, 0 ≤ eta k z)
    (cut hi : ℤ) (x y : ℝ) :
    (∀ a : ℝ,
        0 ≤ coherentCutHeadDiagonalMask eta cut x y +
          a ^ 2 * coherentCutSuffixDiagonalMask eta cut hi x y +
          a * coherentCutSymmetricMask eta cut hi x y) ↔
      coherentCutAntisymmetricMask eta cut hi x y = 0 := by
  let Dhead := coherentCutHeadDiagonalMask eta cut x y
  let Dsuffix := coherentCutSuffixDiagonalMask eta cut hi x y
  let sym := coherentCutSymmetricMask eta cut hi x y
  let anti := coherentCutAntisymmetricMask eta cut hi x y
  have hDhead : 0 ≤ Dhead :=
    coherentCutHeadDiagonalMask_nonnegative eta hnonneg cut x y
  have hDsuffix : 0 ≤ Dsuffix :=
    coherentCutSuffixDiagonalMask_nonnegative eta hnonneg cut hi x y
  have hsym : 0 ≤ sym :=
    coherentCutSymmetricMask_nonnegative eta hnonneg cut hi x y
  have hdet : sym ^ 2 - anti ^ 2 = 4 * Dhead * Dsuffix := by
    exact coherentCut_symmetric_sq_sub_antisymmetric_sq eta cut hi x y
  change (∀ a : ℝ, 0 ≤ Dhead + a ^ 2 * Dsuffix + a * sym) ↔ anti = 0
  constructor
  · intro hall
    by_contra hanti
    rcases hDsuffix.eq_or_lt with hzero | hpos
    · have hantiSq : 0 < anti ^ 2 := sq_pos_of_ne_zero hanti
      have hsymPos : 0 < sym := by
        nlinarith
      let a : ℝ := -(Dhead + 1) / sym
      have ha : a * sym = -(Dhead + 1) := by
        dsimp only [a]
        field_simp [hsymPos.ne']
      have hnegative : Dhead + a ^ 2 * Dsuffix + a * sym = -1 := by
        rw [← hzero]
        nlinarith
      exact (not_lt_of_ge (hall a)) (by rw [hnegative]; norm_num)
    · obtain ⟨a, ha⟩ := coherentCut_exists_realPhaseMask_neg
        eta cut hi x y hpos hanti
      exact (not_lt_of_ge (hall a)) ha
  · intro hanti a
    by_cases hzero : Dsuffix = 0
    · have hsymZero : sym = 0 := by
        rw [hanti, hzero] at hdet
        norm_num at hdet
        nlinarith [sq_nonneg sym]
      rw [hzero, hsymZero]
      simpa using hDhead
    · have hpos : 0 < Dsuffix := lt_of_le_of_ne hDsuffix (Ne.symm hzero)
      exact
        (coherentCut_all_realPhaseMask_nonneg_iff_antisymmetric_eq_zero
          eta cut hi x y hpos).2 hanti a

/-- Because quarter-lattice weights overlap only their immediate neighbors,
the head times the whole suffix is exactly the head times the next weight. -/
theorem coherentCut_head_mul_suffix_eq_next
    (eta : ℤ → ℝ → ℝ)
    (hdisjoint : ∀ k l : ℤ,
      k + 2 ≤ l ∨ l + 2 ≤ k →
        ∀ z : ℝ, eta k z * eta l z = 0)
    (cut hi : ℤ) (hcut : cut + 1 ≤ hi) (z : ℝ) :
    eta cut z * coherentCutSuffixMask eta cut hi z =
      eta cut z * eta (cut + 1) z := by
  unfold coherentCutSuffixMask
  rw [Finset.mul_sum]
  apply Finset.sum_eq_single (cut + 1)
  · intro k hk hne
    simp only [Finset.mem_Icc] at hk
    apply hdisjoint cut k (Or.inl (by omega)) z
  · intro hnot
    exact (hnot (Finset.mem_Icc.mpr ⟨by omega, hcut⟩)).elim

/-! ## The cumulative suffix is a one-cell transition -/

/-- On a nonzero point of the parent, the physical cell support forces its
coherent weight to vanish outside the corresponding two-step lattice cell. -/
theorem coherentWeight_eq_zero_of_not_mem_latticeCell
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ)
    (hcommon : ∀ k z, A k z = (eta k z : ℂ) * parent z)
    (hsupport : ∀ k, tsupport (A k) ⊆ Set.Icc
      (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2)))
    (k : ℤ) (z : ℝ) (hparent : parent z ≠ 0)
    (hz : z ∉ Set.Icc
      (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2))) :
    eta k z = 0 := by
  have hAzero : A k z = 0 := by
    by_contra hne
    exact hz (hsupport k
      (subset_tsupport (A k) (Function.mem_support.mpr hne)))
  rw [hcommon k z] at hAzero
  exact Complex.ofReal_eq_zero.mp
    ((mul_eq_zero.mp hAzero).resolve_right hparent)

/-- Strictly left of the next lattice point, every cell in the selected
suffix vanishes on a nonzero point of the parent. -/
theorem coherentCutSuffixMask_eq_zero_of_lt_nextLatticePoint
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ)
    (hcommon : ∀ k z, A k z = (eta k z : ℂ) * parent z)
    (hsupport : ∀ k, tsupport (A k) ⊆ Set.Icc
      (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2)))
    (cut hi : ℤ) (z : ℝ) (hparent : parent z ≠ 0)
    (hz : z < quarterLogLatticePoint (cut + 1)) :
    coherentCutSuffixMask eta cut hi z = 0 := by
  unfold coherentCutSuffixMask
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Finset.mem_Icc] at hk
  apply coherentWeight_eq_zero_of_not_mem_latticeCell
    parent A eta hcommon hsupport k z hparent
  intro hzCell
  have hmono : quarterLogLatticePoint (cut + 1) ≤
      quarterLogLatticePoint k := quarterLogLatticePoint_mono hk.1
  exact (not_lt_of_ge (hmono.trans hzCell.1)) hz

/-- Strictly right of the head cell's upper lattice endpoint, its coherent
weight vanishes on a nonzero point of the parent. -/
theorem coherentCutHeadWeight_eq_zero_of_upperLatticePoint_lt
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ)
    (hcommon : ∀ k z, A k z = (eta k z : ℂ) * parent z)
    (hsupport : ∀ k, tsupport (A k) ⊆ Set.Icc
      (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2)))
    (cut : ℤ) (z : ℝ) (hparent : parent z ≠ 0)
    (hz : quarterLogLatticePoint (cut + 2) < z) :
    eta cut z = 0 := by
  apply coherentWeight_eq_zero_of_not_mem_latticeCell
    parent A eta hcommon hsupport cut z hparent
  intro hzCell
  exact (not_lt_of_ge hzCell.2) hz

/-- Once a nonzero parent point lies beyond the head cell, the entire
partition mass is in the selected suffix.  Thus the cumulative suffix is a
cutoff which is exactly zero to the left of one lattice point and exactly one
to the right of the next. -/
theorem coherentCutSuffixMask_eq_one_of_upperLatticePoint_lt
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ) (lo cut hi : ℤ)
    (hcommon : ∀ k z, A k z = (eta k z : ℂ) * parent z)
    (hsupport : ∀ k, tsupport (A k) ⊆ Set.Icc
      (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2)))
    (hsum : ∀ z ∈ tsupport parent,
      (∑ k ∈ Finset.Icc lo hi, eta k z) = 1)
    (hlo : lo ≤ cut) (z : ℝ) (hparent : parent z ≠ 0)
    (hz : quarterLogLatticePoint (cut + 2) < z) :
    coherentCutSuffixMask eta cut hi z = 1 := by
  have hsubset : Finset.Icc (cut + 1) hi ⊆ Finset.Icc lo hi :=
    Finset.Icc_subset_Icc (by omega) le_rfl
  have hsumSubset :
      (∑ k ∈ Finset.Icc (cut + 1) hi, eta k z) =
        ∑ k ∈ Finset.Icc lo hi, eta k z := by
    apply Finset.sum_subset hsubset
    intro k hkFull hkSuffix
    simp only [Finset.mem_Icc] at hkFull hkSuffix
    have hkcut : k ≤ cut := by omega
    apply coherentWeight_eq_zero_of_not_mem_latticeCell
      parent A eta hcommon hsupport k z hparent
    intro hzCell
    have hmono : quarterLogLatticePoint (k + 2) ≤
        quarterLogLatticePoint (cut + 2) :=
      quarterLogLatticePoint_mono (by omega)
    exact (not_lt_of_ge (hzCell.2.trans hmono)) hz
  unfold coherentCutSuffixMask
  rw [hsumSubset, hsum z
    (subset_tsupport parent (Function.mem_support.mpr hparent))]

/-- A parent autocorrelation pair which crosses the full one-cell transition
already makes the real phase mask negative at scalar `-1`.  This is the
degenerate-diagonal counterpart of the determinant obstruction above. -/
theorem coherentCut_crossTransition_realPhaseMask_neg
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ) (lo cut hi : ℤ)
    (hcommon : ∀ k z, A k z = (eta k z : ℂ) * parent z)
    (hsupport : ∀ k, tsupport (A k) ⊆ Set.Icc
      (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2)))
    (hsum : ∀ z ∈ tsupport parent,
      (∑ k ∈ Finset.Icc lo hi, eta k z) = 1)
    (hlo : lo ≤ cut) (x y : ℝ)
    (hparentY : parent y ≠ 0) (hparentXY : parent (x * y) ≠ 0)
    (hy : y < quarterLogLatticePoint (cut + 1))
    (hxy : quarterLogLatticePoint (cut + 2) < x * y)
    (hheadY : 0 < eta cut y) :
    coherentCutHeadDiagonalMask eta cut x y +
        (-1 : ℝ) ^ 2 * coherentCutSuffixDiagonalMask eta cut hi x y +
        (-1 : ℝ) * coherentCutSymmetricMask eta cut hi x y < 0 := by
  have hsuffixY : coherentCutSuffixMask eta cut hi y = 0 :=
    coherentCutSuffixMask_eq_zero_of_lt_nextLatticePoint
      parent A eta hcommon hsupport cut hi y hparentY hy
  have hsuffixXY : coherentCutSuffixMask eta cut hi (x * y) = 1 :=
    coherentCutSuffixMask_eq_one_of_upperLatticePoint_lt
      parent A eta lo cut hi hcommon hsupport hsum hlo
      (x * y) hparentXY hxy
  have hheadXY : eta cut (x * y) = 0 :=
    coherentCutHeadWeight_eq_zero_of_upperLatticePoint_lt
      parent A eta hcommon hsupport cut (x * y) hparentXY hxy
  unfold coherentCutHeadDiagonalMask coherentCutSuffixDiagonalMask
    coherentCutSymmetricMask
  rw [hsuffixY, hsuffixXY, hheadXY]
  norm_num
  exact hheadY

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCutMaskGeometryStructural
