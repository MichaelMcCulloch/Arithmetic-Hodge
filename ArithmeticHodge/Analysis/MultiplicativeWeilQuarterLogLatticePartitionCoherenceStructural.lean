import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticePartitionStructural

set_option autoImplicit false

open Complex Filter Real Set
open scoped ContDiff Distributions Manifold Topology BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticePartitionCoherenceStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilQuarterLogLatticePartitionStructural

/-- A normalized quarter-lattice seed together with the real partition
weight from which its physical cell was cut. -/
structure CoherentQuarterCell where
  index : ℤ
  seed : BombieriTest
  weight : ℝ → ℝ

def CoherentQuarterCell.physical (p : CoherentQuarterCell) : BombieriTest :=
  quarterLogLatticeRescale p.index p.seed

/-- Common-parent coherence is equivalently an exact rank-one pointwise Gram
identity. -/
theorem CoherentQuarterCell.pointwiseGram_eq
    (p q : CoherentQuarterCell) (g : BombieriTest) (x : ℝ)
    (hp : p.physical x = (p.weight x : ℂ) * g x)
    (hq : q.physical x = (q.weight x : ℂ) * g x) :
    starRingEnd ℂ (p.physical x) * q.physical x =
      ((p.weight x * q.weight x * Complex.normSq (g x) : ℝ) : ℂ) := by
  rw [hp, hq, map_mul, starRingEnd_apply, Complex.star_def,
    Complex.conj_ofReal]
  have hg : (starRingEnd ℂ) (g x) * g x =
      (Complex.normSq (g x) : ℂ) := by
    exact (Complex.normSq_eq_conj_mul_self (z := g x)).symm
  calc
    (p.weight x : ℂ) * (starRingEnd ℂ) (g x) *
        ((q.weight x : ℂ) * g x) =
      ((p.weight x * q.weight x : ℝ) : ℂ) *
        ((starRingEnd ℂ) (g x) * g x) := by push_cast; ring
    _ = _ := by rw [hg]; push_cast; ring

/-- The actual partition-of-unity construction retains substantially more
than support and total sum: every physical cell is a nonnegative real
pointwise multiple of one common parent, the weights sum to one on the
parent support, and cells whose lattice indices differ by at least two have
pointwise-disjoint weights. -/
theorem exists_coherent_quarterLogLattice_decomposition (g : BombieriTest) :
    ∃ cells : List CoherentQuarterCell,
      (cells.map CoherentQuarterCell.physical).sum = g ∧
      (∀ p ∈ cells,
        tsupport p.seed ⊆ Set.Icc 1 (quarterLogLatticePoint 2)) ∧
      (∀ p ∈ cells, ∀ x : ℝ,
        p.physical x = (p.weight x : ℂ) * g x) ∧
      (∀ p ∈ cells, ∀ x : ℝ, 0 ≤ p.weight x) ∧
      (∀ x ∈ tsupport g,
        (cells.map fun p ↦ p.weight x).sum = 1) ∧
      (∀ p ∈ cells, ∀ q ∈ cells,
        p.index + 2 ≤ q.index ∨ q.index + 2 ≤ p.index →
          ∀ x : ℝ, p.weight x * q.weight x = 0) := by
  classical
  let U : ℝ → Set ℝ := fun x ↦ Set.Ioo
    (quarterLogLatticePoint (quarterLogLatticeIndex x))
    (quarterLogLatticePoint (quarterLogLatticeIndex x + 2))
  have hU_nhds : ∀ x ∈ tsupport g, U x ∈ 𝓝 x := by
    intro x hx
    have hxpos : 0 < x := g.tsupport_subset hx
    exact Ioo_mem_nhds
      (mem_quarterLogLatticeInterval x hxpos).1
      (mem_quarterLogLatticeInterval x hxpos).2
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
        tsupport (fun x : ℝ ↦ (rho i x : ℂ)) =
          tsupport (rho i : ℝ → ℝ) := by
      unfold tsupport
      apply congrArg closure
      ext x
      simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
    rw [hcoe] at hleft
    exact hleft.trans (hrho i)
  have hcell_lattice (i : t) :
      tsupport (cell i : ℝ → ℂ) ⊆ Set.Icc
        (quarterLogLatticePoint (quarterLogLatticeIndex i.1))
        (quarterLogLatticePoint (quarterLogLatticeIndex i.1 + 2)) := by
    exact (hcell_support i).trans Set.Ioo_subset_Icc_self
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
  let coherent : t → CoherentQuarterCell := fun i ↦
    { index := quarterLogLatticeIndex i.1
      seed := quarterLogLatticeNormalize (quarterLogLatticeIndex i.1) (cell i)
      weight := rho i }
  let cells : List CoherentQuarterCell :=
    (Finset.univ : Finset t).toList.map coherent
  have hmem (p : CoherentQuarterCell) (hp : p ∈ cells) :
      ∃ i : t, p = coherent i := by
    simp only [cells, List.mem_map, Finset.mem_toList, Finset.mem_univ,
      true_and] at hp
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, hi.symm⟩
  refine ⟨cells, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [cells, List.map_map, Function.comp_apply, coherent,
      CoherentQuarterCell.physical, quarterLogLatticeRescale_normalize,
      Finset.sum_map_toList] using hsum
  · intro p hp
    obtain ⟨i, rfl⟩ := hmem p hp
    exact quarterLogLatticeNormalize_tsupport_subset_base
      (quarterLogLatticeIndex i.1) (cell i) (hcell_lattice i)
  · intro p hp x
    obtain ⟨i, rfl⟩ := hmem p hp
    simp only [coherent, CoherentQuarterCell.physical,
      quarterLogLatticeRescale_normalize]
    rfl
  · intro p hp x
    obtain ⟨i, rfl⟩ := hmem p hp
    exact rho.nonneg i x
  · intro x hx
    have hrho_sum : ∑ i : t, rho i x = 1 := by
      rw [← finsum_eq_sum_of_fintype]
      exact rho.sum_eq_one hx
    simpa only [cells, List.map_map, Function.comp_apply, coherent,
      Finset.sum_map_toList] using hrho_sum
  · intro p hp q hq hsep x
    obtain ⟨i, rfl⟩ := hmem p hp
    obtain ⟨j, rfl⟩ := hmem q hq
    simp only [coherent] at hsep ⊢
    by_cases hi : rho i x = 0
    · simp only [hi, zero_mul]
    by_cases hj : rho j x = 0
    · simp only [hj, mul_zero]
    exfalso
    have hxi : x ∈ V i := hrho i
      (subset_tsupport (rho i : ℝ → ℝ)
        (Function.mem_support.mpr hi))
    have hxj : x ∈ V j := hrho j
      (subset_tsupport (rho j : ℝ → ℝ)
        (Function.mem_support.mpr hj))
    change x ∈ Set.Ioo
      (quarterLogLatticePoint (quarterLogLatticeIndex i.1))
      (quarterLogLatticePoint (quarterLogLatticeIndex i.1 + 2)) at hxi
    change x ∈ Set.Ioo
      (quarterLogLatticePoint (quarterLogLatticeIndex j.1))
      (quarterLogLatticePoint (quarterLogLatticeIndex j.1 + 2)) at hxj
    rcases hsep with hij | hji
    · have hmono := quarterLogLatticePoint_mono hij
      exact (not_lt_of_ge (hxi.2.le.trans hmono)) hxj.1
    · have hmono := quarterLogLatticePoint_mono hji
      exact (not_lt_of_ge (hxj.2.le.trans hmono)) hxi.1

end

end ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticePartitionCoherenceStructural
