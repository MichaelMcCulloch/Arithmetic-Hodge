import ArithmeticHodge.Analysis.MultiplicativeWeilCellAssemblyStructural
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false

open Complex Filter Real Set
open scoped ContDiff Distributions Manifold Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Finite smooth ratio-two partitions

Every Bombieri test admits a finite smooth partition into tests supported in
multiplicative intervals of width at most two.  Compactness first reduces the
pointwise ratio-two cover to a finite cover; a smooth partition of unity on
the topological support then gives the test-function pieces.
-/

/-- Every Bombieri test is a finite sum of Bombieri tests, each carried by a
multiplicative interval of width at most two. -/
theorem exists_ratioTwoCell_decomposition (g : BombieriTest) :
    ∃ cells : List BombieriTest,
      cells.sum = g ∧ ∀ f ∈ cells, BombieriRatioTwoCell f := by
  classical
  let U : ℝ → Set ℝ := fun x ↦ Set.Ioo (3 * x / 4) (3 * x / 2)
  have hU_nhds : ∀ x ∈ tsupport g, U x ∈ 𝓝 x := by
    intro x hx
    have hxpos : 0 < x := g.tsupport_subset hx
    exact Ioo_mem_nhds (by nlinarith) (by nlinarith)
  obtain ⟨t, ht_mem, ht_cover⟩ :=
    g.hasCompactSupport.elim_nhds_subcover U hU_nhds
  let V : t → Set ℝ := fun i ↦ U i.1
  have hV_open : ∀ i, IsOpen (V i) := by
    intro i
    exact isOpen_Ioo
  have ht_cover' : tsupport g ⊆ ⋃ i : t, V i := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (ht_cover hx) with ⟨y, hyt, hxy⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hyt⟩, hxy⟩
  obtain ⟨rho, hrho⟩ :
      ∃ rho : SmoothPartitionOfUnity t 𝓘(ℝ, ℝ) ℝ (tsupport g),
        rho.IsSubordinate V :=
    SmoothPartitionOfUnity.exists_isSubordinate
      𝓘(ℝ, ℝ) g.hasCompactSupport.isClosed V hV_open ht_cover'
  let cell : t → BombieriTest := fun i ↦ TestFunction.mk
    (fun x : ℝ ↦ (rho i x : ℂ) * g x)
    ((Complex.ofRealCLM.contDiff.comp (rho i).contMDiff.contDiff).mul g.contDiff)
    g.hasCompactSupport.mul_left
    ((tsupport_mul_subset_right :
        tsupport (fun x : ℝ ↦ (rho i x : ℂ) * g x) ⊆ tsupport g).trans
      g.tsupport_subset)
  have hcell_support (i : t) :
      tsupport (cell i : ℝ → ℂ) ⊆ V i := by
    have hleft :
        tsupport (fun x : ℝ ↦ (rho i x : ℂ) * g x) ⊆
          tsupport (fun x : ℝ ↦ (rho i x : ℂ)) :=
      tsupport_mul_subset_left
    have hcoe :
        tsupport (fun x : ℝ ↦ (rho i x : ℂ)) = tsupport (rho i : ℝ → ℝ) := by
      unfold tsupport
      apply congrArg closure
      ext x
      simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
    rw [hcoe] at hleft
    exact hleft.trans (hrho i)
  have hcell_ratio (i : t) : BombieriRatioTwoCell (cell i) := by
    have hipos : 0 < (i.1 : ℝ) :=
      g.tsupport_subset (ht_mem i.1 i.2)
    refine ⟨3 * i.1 / 4, 3 * i.1 / 2, ?_, ?_, ?_, ?_⟩
    · positivity
    · nlinarith
    · exact (hcell_support i).trans Set.Ioo_subset_Icc_self
    · have hi0 : (i.1 : ℝ) ≠ 0 := ne_of_gt hipos
      field_simp [hi0]
      norm_num
  have hsum : ∑ i : t, cell i = g := by
    apply TestFunction.ext
    intro x
    let ev : BombieriTest →+ ℂ :=
      { toFun := fun f ↦ f x
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    change ev (∑ i : t, cell i) = ev g
    rw [map_sum]
    change (∑ i : t, (rho i x : ℂ) * g x) = g x
    by_cases hx : x ∈ tsupport g
    · have hrho_sum : ∑ i : t, rho i x = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact rho.sum_eq_one hx
      rw [← Finset.sum_mul]
      simp only [← Complex.ofReal_sum, hrho_sum, Complex.ofReal_one, one_mul]
    · have hgx : g x = 0 := by
        by_contra hgx
        exact hx (subset_tsupport g (Function.mem_support.mpr hgx))
      simp only [hgx, mul_zero, Finset.sum_const_zero]
  let cells : List BombieriTest := (Finset.univ : Finset t).toList.map cell
  refine ⟨cells, ?_, ?_⟩
  · simpa only [cells, Finset.sum_map_toList] using hsum
  · intro f hf
    simp only [cells, List.mem_map, Finset.mem_toList, Finset.mem_univ,
      true_and] at hf
    obtain ⟨i, rfl⟩ := hf
    exact hcell_ratio i

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
