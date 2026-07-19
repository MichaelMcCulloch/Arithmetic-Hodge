import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticePartitionStructural

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set
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
  weight_contDiff : ContDiff ℝ ∞ weight

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

/-- Every directed correlation between coherent cells is the parent
correlation integrand multiplied by a nonnegative real two-point mask. -/
theorem CoherentQuarterCell.directedCorrelation_eq_weighted_parent
    (p q : CoherentQuarterCell) (g : BombieriTest)
    (hp : ∀ z : ℝ, p.physical z = (p.weight z : ℂ) * g z)
    (hq : ∀ z : ℝ, q.physical z = (q.weight z : ℂ) * g z)
    (x : ℝ) :
    bombieriDirectedCorrelation p.physical q.physical x =
      ∫ y : ℝ in Set.Ioi 0,
        ((p.weight (x * y) * q.weight y : ℝ) : ℂ) *
          (g (x * y) * starRingEnd ℂ (g y)) := by
  unfold bombieriDirectedCorrelation
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _hy
  change p.physical (x * y) * starRingEnd ℂ (q.physical y) = _
  rw [hp (x * y), hq y]
  have hstar :
      starRingEnd ℂ ((q.weight y : ℂ) * g y) =
        (q.weight y : ℂ) * starRingEnd ℂ (g y) := by
    rw [map_mul, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  rw [hstar]
  push_cast
  ring

private theorem coherentDirectedIntegrand_integrableOn
    (f h : BombieriTest) (x : ℝ) :
    IntegrableOn
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (h y))
      (Set.Ioi 0) := by
  have hcont : Continuous
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (h y)) := by
    fun_prop
  have hhcompact : HasCompactSupport
      (fun y : ℝ ↦ starRingEnd ℂ (h y)) := by
    exact h.hasCompactSupport.comp_left (by simp)
  have hcompact : HasCompactSupport
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (h y)) := by
    simpa only [Pi.mul_apply] using
      hhcompact.mul_left (f := fun y : ℝ ↦ f (x * y))
  exact (hcont.integrable_of_hasCompactSupport hcompact).integrableOn

/-- Any finite lag-weighted family of coherent directed correlations is one
parent correlation integral with a real scalar two-point mask. -/
theorem finite_lagWeighted_directedCorrelation_eq_parentMask
    {I : Type*} [DecidableEq I]
    (g : BombieriTest) (cells : I → CoherentQuarterCell)
    (hparent : ∀ i : I, ∀ z : ℝ,
      (cells i).physical z = ((cells i).weight z : ℂ) * g z)
    (pairs : Finset (I × I)) (lagWeight : ℤ → ℝ) (x : ℝ) :
    (∑ ij ∈ pairs,
      ((lagWeight ((cells ij.2).index - (cells ij.1).index) : ℝ) : ℂ) *
        bombieriDirectedCorrelation
          (cells ij.1).physical (cells ij.2).physical x) =
      ∫ y : ℝ in Set.Ioi 0,
        (∑ ij ∈ pairs,
          ((lagWeight ((cells ij.2).index - (cells ij.1).index) *
              (cells ij.1).weight (x * y) *
              (cells ij.2).weight y : ℝ) : ℂ)) *
          (g (x * y) * starRingEnd ℂ (g y)) := by
  unfold bombieriDirectedCorrelation
  calc
    (∑ ij ∈ pairs,
        ((lagWeight ((cells ij.2).index - (cells ij.1).index) : ℝ) : ℂ) *
          ∫ y : ℝ in Set.Ioi 0,
            (cells ij.1).physical (x * y) *
              starRingEnd ℂ ((cells ij.2).physical y)) =
      ∑ ij ∈ pairs,
        ∫ y : ℝ in Set.Ioi 0,
          ((lagWeight ((cells ij.2).index - (cells ij.1).index) : ℝ) : ℂ) *
            ((cells ij.1).physical (x * y) *
              starRingEnd ℂ ((cells ij.2).physical y)) := by
        apply Finset.sum_congr rfl
        intro ij hij
        exact (MeasureTheory.integral_const_mul _ _).symm
    _ = ∫ y : ℝ in Set.Ioi 0,
        ∑ ij ∈ pairs,
          ((lagWeight ((cells ij.2).index - (cells ij.1).index) : ℝ) : ℂ) *
            ((cells ij.1).physical (x * y) *
              starRingEnd ℂ ((cells ij.2).physical y)) := by
        rw [MeasureTheory.integral_finset_sum]
        intro ij hij
        exact (coherentDirectedIntegrand_integrableOn
          (cells ij.1).physical (cells ij.2).physical x).const_mul _
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _hy
      change (∑ ij ∈ pairs,
          ((lagWeight ((cells ij.2).index - (cells ij.1).index) : ℝ) : ℂ) *
            ((cells ij.1).physical (x * y) *
              starRingEnd ℂ ((cells ij.2).physical y))) =
        (∑ ij ∈ pairs,
          ((lagWeight ((cells ij.2).index - (cells ij.1).index) *
              (cells ij.1).weight (x * y) *
              (cells ij.2).weight y : ℝ) : ℂ)) *
          (g (x * y) * starRingEnd ℂ (g y))
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      rw [hparent ij.1 (x * y), hparent ij.2 y]
      have hstar :
          starRingEnd ℂ (((cells ij.2).weight y : ℂ) * g y) =
            ((cells ij.2).weight y : ℂ) * starRingEnd ℂ (g y) := by
        rw [map_mul, starRingEnd_apply, Complex.star_def,
          Complex.conj_ofReal]
      rw [hstar]
      push_cast
      ring

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
      weight := rho i
      weight_contDiff := (rho i).contMDiff.contDiff }
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
