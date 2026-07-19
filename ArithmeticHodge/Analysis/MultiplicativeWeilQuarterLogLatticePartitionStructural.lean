import ArithmeticHodge.Analysis.MultiplicativeWeilFixedLogLatticePartitionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFejerLocalizationStructural

set_option autoImplicit false

open Complex Filter Real Set
open scoped ContDiff Distributions Manifold Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticePartitionStructural

noncomputable section

open MultiplicativeWeil

/-!
# A quarter-octave lattice for Fejer localization

The half-octave lattice makes every single cell ratio two, but already a
two-cell window is too wide for the proved local positivity theorem.  On the
quarter-octave lattice, one cell spans two quarter steps and has ratio
`sqrt 2`; every three consecutive cells fit exactly inside a ratio-two
interval.  This is the geometry required by order-three Fejer localization.
-/

/-- The quarter-octave lattice point `exp (n * log 2 / 4)`. -/
def quarterLogLatticePoint (n : ℤ) : ℝ :=
  Real.exp ((n : ℝ) * (Real.log 2 / 4))

theorem quarterLogLatticePoint_pos (n : ℤ) :
    0 < quarterLogLatticePoint n := by
  exact Real.exp_pos _

/-- Translation on the integer lattice becomes multiplication of positive
lattice points. -/
theorem quarterLogLatticePoint_add (n k : ℤ) :
    quarterLogLatticePoint (n + k) =
      quarterLogLatticePoint k * quarterLogLatticePoint n := by
  unfold quarterLogLatticePoint
  rw [Int.cast_add, add_mul, Real.exp_add]
  ring

theorem quarterLogLatticePoint_zero :
    quarterLogLatticePoint 0 = 1 := by
  norm_num [quarterLogLatticePoint]

/-- Four quarter-octave steps multiply scale by two. -/
theorem quarterLogLatticePoint_four :
    quarterLogLatticePoint 4 = 2 := by
  unfold quarterLogLatticePoint
  norm_num
  rw [show 4 * (Real.log 2 / 4) = Real.log 2 by ring,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem quarterLogLatticePoint_add_two (n : ℤ) :
    quarterLogLatticePoint (n + 2) =
      quarterLogLatticePoint 2 * quarterLogLatticePoint n := by
  exact quarterLogLatticePoint_add n 2

theorem quarterLogLatticePoint_add_four (n : ℤ) :
    quarterLogLatticePoint (n + 4) =
      2 * quarterLogLatticePoint n := by
  rw [quarterLogLatticePoint_add, quarterLogLatticePoint_four]

/-- The quarter-octave lattice is monotone in its integer index. -/
theorem quarterLogLatticePoint_mono {m n : ℤ} (hmn : m ≤ n) :
    quarterLogLatticePoint m ≤ quarterLogLatticePoint n := by
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast hmn
  · positivity

/-- The shifted floor index whose two-step interval contains a positive
point in its interior. -/
def quarterLogLatticeIndex (x : ℝ) : ℤ :=
  ⌊4 * Real.log x / Real.log 2⌋ - 1

theorem mem_quarterLogLatticeInterval (x : ℝ) (hx : 0 < x) :
    x ∈ Set.Ioo
      (quarterLogLatticePoint (quarterLogLatticeIndex x))
      (quarterLogLatticePoint (quarterLogLatticeIndex x + 2)) := by
  let u : ℝ := 4 * Real.log x / Real.log 2
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu_log : u * (Real.log 2 / 4) = Real.log x := by
    dsimp [u]
    field_simp [hlogTwo.ne']
  have hfloorLower : ((⌊u⌋ : ℤ) : ℝ) - 1 < u := by
    exact (sub_lt_self _ (by norm_num)).trans_le (Int.floor_le u)
  have hfloorUpper : u < ((⌊u⌋ : ℤ) : ℝ) + 1 := by
    exact Int.lt_floor_add_one u
  constructor
  · unfold quarterLogLatticePoint
    rw [show quarterLogLatticeIndex x = ⌊u⌋ - 1 by rfl]
    simp only [Int.cast_sub, Int.cast_one]
    rw [← Real.exp_log hx]
    apply Real.exp_lt_exp.mpr
    calc
      (((⌊u⌋ : ℤ) : ℝ) - 1) * (Real.log 2 / 4) <
          u * (Real.log 2 / 4) :=
        mul_lt_mul_of_pos_right hfloorLower (by positivity)
      _ = Real.log x := hu_log
  · unfold quarterLogLatticePoint
    rw [show quarterLogLatticeIndex x = ⌊u⌋ - 1 by rfl]
    simp only [Int.cast_add, Int.cast_sub, Int.cast_ofNat, Int.cast_one]
    rw [← Real.exp_log hx]
    apply Real.exp_lt_exp.mpr
    calc
      Real.log x = u * (Real.log 2 / 4) := hu_log.symm
      _ < (((⌊u⌋ : ℤ) : ℝ) + 1) * (Real.log 2 / 4) :=
        mul_lt_mul_of_pos_right hfloorUpper (by positivity)
      _ = ((((⌊u⌋ : ℤ) : ℝ) - 1) + 2) *
          (Real.log 2 / 4) := by ring

/-- Normalize one physical quarter-lattice cell to the common base
interval. -/
def quarterLogLatticeNormalize (n : ℤ) (f : BombieriTest) : BombieriTest :=
  normalizedDilation (quarterLogLatticePoint n)
    (quarterLogLatticePoint_pos n) f

/-- Return a normalized seed to its physical quarter-lattice cell. -/
def quarterLogLatticeRescale (n : ℤ) (f : BombieriTest) : BombieriTest :=
  normalizedDilation (quarterLogLatticePoint n)⁻¹
    (inv_pos.mpr (quarterLogLatticePoint_pos n)) f

@[simp]
theorem quarterLogLatticeRescale_normalize
    (n : ℤ) (f : BombieriTest) :
    quarterLogLatticeRescale n (quarterLogLatticeNormalize n f) = f := by
  exact normalizedDilation_inv_comp
    (quarterLogLatticePoint n) (quarterLogLatticePoint_pos n) f

/-- Normalized quarter-lattice seeds are supported in the fixed interval
from scale one through two quarter steps. -/
theorem quarterLogLatticeNormalize_tsupport_subset_base
    (n : ℤ) (f : BombieriTest)
    (hf : tsupport f ⊆ Set.Icc
      (quarterLogLatticePoint n) (quarterLogLatticePoint (n + 2))) :
    tsupport (quarterLogLatticeNormalize n f) ⊆
      Set.Icc 1 (quarterLogLatticePoint 2) := by
  have hsupport := normalizedDilation_tsupport_subset_Icc
    (quarterLogLatticePoint n) (quarterLogLatticePoint_pos n) f hf
  simpa only [quarterLogLatticeNormalize, quarterLogLatticePoint_add_two,
    div_self (quarterLogLatticePoint_pos n).ne',
    mul_div_cancel_right₀ _ (quarterLogLatticePoint_pos n).ne'] using hsupport

/-- Rescaling a normalized seed places it in its physical two-step
quarter-lattice interval. -/
theorem quarterLogLatticeRescale_tsupport_subset
    (n : ℤ) (f : BombieriTest)
    (hf : tsupport f ⊆ Set.Icc 1 (quarterLogLatticePoint 2)) :
    tsupport (quarterLogLatticeRescale n f) ⊆ Set.Icc
      (quarterLogLatticePoint n) (quarterLogLatticePoint (n + 2)) := by
  have hsupport := normalizedDilation_tsupport_subset_Icc
    (quarterLogLatticePoint n)⁻¹
    (inv_pos.mpr (quarterLogLatticePoint_pos n)) f hf
  simpa only [quarterLogLatticeRescale, one_div, inv_inv, div_inv_eq_mul,
    one_mul, quarterLogLatticePoint_add_two] using hsupport

/-- Three consecutive physical quarter-lattice cells have common support
ratio exactly two. -/
theorem quarterLogLattice_threeWindow_ratioTwoCell
    (n : ℤ) (f₀ f₁ f₂ : BombieriTest)
    (hf₀ : tsupport f₀ ⊆ Set.Icc 1 (quarterLogLatticePoint 2))
    (hf₁ : tsupport f₁ ⊆ Set.Icc 1 (quarterLogLatticePoint 2))
    (hf₂ : tsupport f₂ ⊆ Set.Icc 1 (quarterLogLatticePoint 2)) :
    BombieriRatioTwoCell
      (quarterLogLatticeRescale n f₀ +
        quarterLogLatticeRescale (n + 1) f₁ +
        quarterLogLatticeRescale (n + 2) f₂) := by
  let c₀ := quarterLogLatticeRescale n f₀
  let c₁ := quarterLogLatticeRescale (n + 1) f₁
  let c₂ := quarterLogLatticeRescale (n + 2) f₂
  have hc₀ : tsupport c₀ ⊆ Set.Icc
      (quarterLogLatticePoint n) (quarterLogLatticePoint (n + 2)) := by
    simpa only [c₀] using
      quarterLogLatticeRescale_tsupport_subset n f₀ hf₀
  have hc₁ : tsupport c₁ ⊆ Set.Icc
      (quarterLogLatticePoint (n + 1))
      (quarterLogLatticePoint ((n + 1) + 2)) := by
    simpa only [c₁] using
      quarterLogLatticeRescale_tsupport_subset (n + 1) f₁ hf₁
  have hc₂ : tsupport c₂ ⊆ Set.Icc
      (quarterLogLatticePoint (n + 2))
      (quarterLogLatticePoint ((n + 2) + 2)) := by
    simpa only [c₂] using
      quarterLogLatticeRescale_tsupport_subset (n + 2) f₂ hf₂
  have hc₀wide : tsupport c₀ ⊆ Set.Icc
      (quarterLogLatticePoint n) (quarterLogLatticePoint (n + 4)) := by
    intro x hx
    have hx' := hc₀ hx
    exact ⟨hx'.1, hx'.2.trans
      (quarterLogLatticePoint_mono (m := n + 2) (n := n + 4) (by omega))⟩
  have hc₁wide : tsupport c₁ ⊆ Set.Icc
      (quarterLogLatticePoint n) (quarterLogLatticePoint (n + 4)) := by
    intro x hx
    have hx' := hc₁ hx
    exact ⟨(quarterLogLatticePoint_mono
        (m := n) (n := n + 1) (by omega)).trans hx'.1,
      hx'.2.trans (quarterLogLatticePoint_mono
        (m := (n + 1) + 2) (n := n + 4) (by omega))⟩
  have hc₂wide : tsupport c₂ ⊆ Set.Icc
      (quarterLogLatticePoint n) (quarterLogLatticePoint (n + 4)) := by
    intro x hx
    have hx' := hc₂ hx
    exact ⟨(quarterLogLatticePoint_mono
      (m := n) (n := n + 2) (by omega)).trans hx'.1, by
      simpa only [add_assoc] using hx'.2⟩
  have hsupport : tsupport (c₀ + c₁ + c₂ : ℝ → ℂ) ⊆ Set.Icc
      (quarterLogLatticePoint n) (quarterLogLatticePoint (n + 4)) := by
    exact (tsupport_add (c₀ + c₁ : ℝ → ℂ) c₂).trans
      (union_subset
        ((tsupport_add (c₀ : ℝ → ℂ) c₁).trans
          (union_subset hc₀wide hc₁wide))
        hc₂wide)
  refine ⟨quarterLogLatticePoint n, quarterLogLatticePoint (n + 4),
    quarterLogLatticePoint_pos n, quarterLogLatticePoint_mono (by omega), ?_, ?_⟩
  · simpa only [c₀, c₁, c₂] using hsupport
  · rw [quarterLogLatticePoint_add_four]
    field_simp [(quarterLogLatticePoint_pos n).ne']
    norm_num

/-- Consequently every three-consecutive-cell window has nonnegative
Bombieri quadratic value, with no assumption on its three normalized seeds. -/
theorem quarterLogLattice_threeWindow_quadratic_nonnegative
    (n : ℤ) (f₀ f₁ f₂ : BombieriTest)
    (hf₀ : tsupport f₀ ⊆ Set.Icc 1 (quarterLogLatticePoint 2))
    (hf₁ : tsupport f₁ ⊆ Set.Icc 1 (quarterLogLatticePoint 2))
    (hf₂ : tsupport f₂ ⊆ Set.Icc 1 (quarterLogLatticePoint 2)) :
    0 ≤ (bombieriFunctional (bombieriQuadraticTest
      (quarterLogLatticeRescale n f₀ +
        quarterLogLatticeRescale (n + 1) f₁ +
        quarterLogLatticeRescale (n + 2) f₂))).re := by
  exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
    (quarterLogLattice_threeWindow_ratioTwoCell n f₀ f₁ f₂ hf₀ hf₁ hf₂)

/-- Every Bombieri test is a finite sum of cells on the fixed
quarter-octave lattice.  Normalized seeds are supported in the common
ratio-`sqrt 2` base interval. -/
theorem exists_quarterLogLattice_decomposition (g : BombieriTest) :
    ∃ cells : List (ℤ × BombieriTest),
      (cells.map fun p ↦ quarterLogLatticeRescale p.1 p.2).sum = g ∧
        ∀ p ∈ cells,
          tsupport p.2 ⊆ Set.Icc 1 (quarterLogLatticePoint 2) := by
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
  let indexedCell : t → ℤ × BombieriTest := fun i ↦
    (quarterLogLatticeIndex i.1,
      quarterLogLatticeNormalize (quarterLogLatticeIndex i.1) (cell i))
  let cells : List (ℤ × BombieriTest) :=
    (Finset.univ : Finset t).toList.map indexedCell
  refine ⟨cells, ?_, ?_⟩
  · simpa only [cells, List.map_map, Function.comp_apply, indexedCell,
      quarterLogLatticeRescale_normalize, Finset.sum_map_toList] using hsum
  · intro p hp
    simp only [cells, List.mem_map, Finset.mem_toList, Finset.mem_univ,
      true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    exact quarterLogLatticeNormalize_tsupport_subset_base
      (quarterLogLatticeIndex i.1) (cell i) (hcell_lattice i)

end

end ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticePartitionStructural
