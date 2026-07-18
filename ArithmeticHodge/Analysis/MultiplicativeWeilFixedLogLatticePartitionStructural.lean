import ArithmeticHodge.Analysis.MultiplicativeWeilRatioTwoPartitionStructural

set_option autoImplicit false

open Complex Filter Real Set
open scoped ContDiff Distributions Manifold Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# A fixed half-octave lattice for Bombieri tests

The positive half-line is covered by the overlapping ratio-two intervals
whose logarithmic endpoints lie on the fixed lattice `(log 2 / 2) * ℤ`.
This module refines the arbitrary finite ratio-two partition to that fixed
lattice and records every resulting cell as a normalized dilation of a seed
supported in `[1, 2]`.
-/

/-- The multiplicative lattice point `exp (n * log 2 / 2)`. -/
def fixedLogLatticePoint (n : ℤ) : ℝ :=
  Real.exp ((n : ℝ) * (Real.log 2 / 2))

theorem fixedLogLatticePoint_pos (n : ℤ) :
    0 < fixedLogLatticePoint n := by
  exact Real.exp_pos _

theorem fixedLogLatticePoint_one :
    fixedLogLatticePoint 1 = Real.sqrt 2 := by
  unfold fixedLogLatticePoint
  simp only [Int.cast_one, one_mul]
  have hsqrt :
      Real.sqrt 2 = Real.exp (Real.log 2 / 2) := by
    rw [← Real.exp_log (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)),
      Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact hsqrt.symm

/-- Consecutive fixed lattice points differ by exactly `sqrt 2`. -/
theorem fixedLogLatticePoint_add_one (n : ℤ) :
    fixedLogLatticePoint (n + 1) =
      Real.sqrt 2 * fixedLogLatticePoint n := by
  unfold fixedLogLatticePoint
  rw [Int.cast_add, Int.cast_one, add_mul, Real.exp_add]
  have hone : Real.exp (1 * (Real.log 2 / 2)) = Real.sqrt 2 := by
    simpa only [fixedLogLatticePoint, Int.cast_one, one_mul] using
      fixedLogLatticePoint_one
  rw [hone]
  ring

/-- Two half-octave steps multiply a lattice point by two. -/
theorem fixedLogLatticePoint_add_two (n : ℤ) :
    fixedLogLatticePoint (n + 2) = 2 * fixedLogLatticePoint n := by
  unfold fixedLogLatticePoint
  rw [Int.cast_add, Int.cast_ofNat, add_mul]
  have htwo : Real.exp (2 * (Real.log 2 / 2)) = 2 := by
    rw [show 2 * (Real.log 2 / 2) = Real.log 2 by ring]
    exact Real.exp_log (by norm_num)
  rw [Real.exp_add, htwo]
  ring

/-- The canonical lattice index whose two-step interval contains `x` in its
interior.  Shifting the floor down by one avoids all endpoint cases. -/
def fixedLogLatticeIndex (x : ℝ) : ℤ :=
  ⌊2 * Real.log x / Real.log 2⌋ - 1

/-- Every positive real lies strictly inside its canonical fixed-lattice
ratio-two interval. -/
theorem mem_fixedLogLatticeInterval (x : ℝ) (hx : 0 < x) :
    x ∈ Set.Ioo
      (fixedLogLatticePoint (fixedLogLatticeIndex x))
      (fixedLogLatticePoint (fixedLogLatticeIndex x + 2)) := by
  let u : ℝ := 2 * Real.log x / Real.log 2
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu_log : u * (Real.log 2 / 2) = Real.log x := by
    dsimp [u]
    field_simp [hlogTwo.ne']
  have hfloorLower : ((⌊u⌋ : ℤ) : ℝ) - 1 < u := by
    exact (sub_lt_self _ (by norm_num)).trans_le (Int.floor_le u)
  have hfloorUpper : u < ((⌊u⌋ : ℤ) : ℝ) + 1 := by
    exact Int.lt_floor_add_one u
  constructor
  · unfold fixedLogLatticePoint
    rw [show fixedLogLatticeIndex x = ⌊u⌋ - 1 by rfl]
    simp only [Int.cast_sub, Int.cast_one]
    rw [← Real.exp_log hx]
    apply Real.exp_lt_exp.mpr
    calc
      (((⌊u⌋ : ℤ) : ℝ) - 1) * (Real.log 2 / 2) <
          u * (Real.log 2 / 2) :=
        mul_lt_mul_of_pos_right hfloorLower (by positivity)
      _ = Real.log x := hu_log
  · unfold fixedLogLatticePoint
    rw [show fixedLogLatticeIndex x = ⌊u⌋ - 1 by rfl]
    simp only [Int.cast_add, Int.cast_sub, Int.cast_ofNat, Int.cast_one]
    rw [← Real.exp_log hx]
    apply Real.exp_lt_exp.mpr
    calc
      Real.log x = u * (Real.log 2 / 2) := hu_log.symm
      _ < (((⌊u⌋ : ℤ) : ℝ) + 1) * (Real.log 2 / 2) :=
        mul_lt_mul_of_pos_right hfloorUpper (by positivity)
      _ = ((((⌊u⌋ : ℤ) : ℝ) - 1) + 2) *
          (Real.log 2 / 2) := by ring

/-- Dilation by a positive factor followed by dilation by its inverse is
exactly the original test. -/
theorem normalizedDilation_inv_comp
    (a : ℝ) (ha : 0 < a) (f : BombieriTest) :
    normalizedDilation a⁻¹ (inv_pos.mpr ha)
        (normalizedDilation a ha f) = f := by
  apply TestFunction.ext
  intro x
  simp only [normalizedDilation_apply]
  have hsqrt : Real.sqrt a⁻¹ * Real.sqrt a = 1 := by
    rw [Real.sqrt_inv]
    exact inv_mul_cancel₀ (Real.sqrt_pos.2 ha).ne'
  rw [show a * (a⁻¹ * x) = x by field_simp [ha.ne']]
  rw [← mul_assoc, ← Complex.ofReal_mul, hsqrt, Complex.ofReal_one, one_mul]

/-- Normalize a physical lattice cell to the common base interval. -/
def fixedLogLatticeNormalize (n : ℤ) (f : BombieriTest) : BombieriTest :=
  normalizedDilation (fixedLogLatticePoint n)
    (fixedLogLatticePoint_pos n) f

/-- Return a base seed to its physical lattice cell. -/
def fixedLogLatticeRescale (n : ℤ) (f : BombieriTest) : BombieriTest :=
  normalizedDilation (fixedLogLatticePoint n)⁻¹
    (inv_pos.mpr (fixedLogLatticePoint_pos n)) f

@[simp]
theorem fixedLogLatticeRescale_normalize
    (n : ℤ) (f : BombieriTest) :
    fixedLogLatticeRescale n (fixedLogLatticeNormalize n f) = f := by
  exact normalizedDilation_inv_comp
    (fixedLogLatticePoint n) (fixedLogLatticePoint_pos n) f

/-- A cell supported between lattice points two steps apart becomes a seed
supported in the fixed base interval `[1, 2]`. -/
theorem fixedLogLatticeNormalize_tsupport_subset_base
    (n : ℤ) (f : BombieriTest)
    (hf : tsupport f ⊆ Set.Icc
      (fixedLogLatticePoint n) (fixedLogLatticePoint (n + 2))) :
    tsupport (fixedLogLatticeNormalize n f) ⊆ Set.Icc 1 2 := by
  have hsupport := normalizedDilation_tsupport_subset_Icc
    (fixedLogLatticePoint n) (fixedLogLatticePoint_pos n) f hf
  simpa only [fixedLogLatticeNormalize, fixedLogLatticePoint_add_two,
    div_self (fixedLogLatticePoint_pos n).ne',
    mul_div_cancel_right₀ 2 (fixedLogLatticePoint_pos n).ne'] using hsupport

/-- Rescaling a base seed places it in the corresponding physical lattice
interval. -/
theorem fixedLogLatticeRescale_tsupport_subset
    (n : ℤ) (f : BombieriTest) (hf : tsupport f ⊆ Set.Icc 1 2) :
    tsupport (fixedLogLatticeRescale n f) ⊆ Set.Icc
      (fixedLogLatticePoint n) (fixedLogLatticePoint (n + 2)) := by
  have hsupport := normalizedDilation_tsupport_subset_Icc
    (fixedLogLatticePoint n)⁻¹
    (inv_pos.mpr (fixedLogLatticePoint_pos n)) f hf
  simpa only [fixedLogLatticeRescale, one_div, inv_inv, div_inv_eq_mul, one_mul,
    fixedLogLatticePoint_add_two] using hsupport

/-- Every rescaled base seed is, in particular, a ratio-two cell. -/
theorem fixedLogLatticeRescale_ratioTwoCell
    (n : ℤ) (f : BombieriTest) (hf : tsupport f ⊆ Set.Icc 1 2) :
    BombieriRatioTwoCell (fixedLogLatticeRescale n f) := by
  refine ⟨fixedLogLatticePoint n, fixedLogLatticePoint (n + 2),
    fixedLogLatticePoint_pos n, ?_,
    fixedLogLatticeRescale_tsupport_subset n f hf, ?_⟩
  · rw [fixedLogLatticePoint_add_two]
    nlinarith [fixedLogLatticePoint_pos n]
  · rw [fixedLogLatticePoint_add_two]
    field_simp [(fixedLogLatticePoint_pos n).ne']
    norm_num

/-- Every Bombieri test is a finite sum of cells on the single fixed
half-octave lattice.  The second component of each pair is a base seed
supported in `[1, 2]`; `fixedLogLatticeRescale` moves it to the physical cell
indexed by the first component. -/
theorem exists_fixedLogLattice_decomposition (g : BombieriTest) :
    ∃ cells : List (ℤ × BombieriTest),
      (cells.map fun p ↦ fixedLogLatticeRescale p.1 p.2).sum = g ∧
        ∀ p ∈ cells, tsupport p.2 ⊆ Set.Icc 1 2 := by
  classical
  let U : ℝ → Set ℝ := fun x ↦ Set.Ioo
    (fixedLogLatticePoint (fixedLogLatticeIndex x))
    (fixedLogLatticePoint (fixedLogLatticeIndex x + 2))
  have hU_nhds : ∀ x ∈ tsupport g, U x ∈ 𝓝 x := by
    intro x hx
    have hxpos : 0 < x := g.tsupport_subset hx
    exact Ioo_mem_nhds
      (mem_fixedLogLatticeInterval x hxpos).1
      (mem_fixedLogLatticeInterval x hxpos).2
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
        (fixedLogLatticePoint (fixedLogLatticeIndex i.1))
        (fixedLogLatticePoint (fixedLogLatticeIndex i.1 + 2)) := by
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
    (fixedLogLatticeIndex i.1,
      fixedLogLatticeNormalize (fixedLogLatticeIndex i.1) (cell i))
  let cells : List (ℤ × BombieriTest) :=
    (Finset.univ : Finset t).toList.map indexedCell
  refine ⟨cells, ?_, ?_⟩
  · simpa only [cells, List.map_map, Function.comp_apply, indexedCell,
      fixedLogLatticeRescale_normalize, Finset.sum_map_toList] using hsum
  · intro p hp
    simp only [cells, List.mem_map, Finset.mem_toList, Finset.mem_univ,
      true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    exact fixedLogLatticeNormalize_tsupport_subset_base
      (fixedLogLatticeIndex i.1) (cell i) (hcell_lattice i)

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
