import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticePartitionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilGlobalCrossAdditiveStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeGramStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilQuarterLogLatticePartitionStructural

/-!
# Exact Gram reduction on the quarter-log lattice

Common-dilation covariance removes the absolute locations of two physical
quarter-lattice cells.  Their complete local-minus-prime cross depends only
on the signed integer lag and the two normalized base seeds.  Combining this
with the finite quarter-lattice partition gives an exact finite Gram for every
Bombieri test.

These are identities for the complete coupled form; no local or prime term is
estimated separately.
-/

/-- Ratios of quarter-lattice points are quarter-lattice points at the
integer difference. -/
theorem quarterLogLatticePoint_div (n m : ℤ) :
    quarterLogLatticePoint n / quarterLogLatticePoint m =
      quarterLogLatticePoint (n - m) := by
  unfold quarterLogLatticePoint
  rw [← Real.exp_sub]
  congr 1
  push_cast
  ring

/-- The complete cross of two physical quarter-lattice cells depends only on
their signed integer lag and their normalized base seeds. -/
theorem bombieriTwoBlockGlobalCrossSymbol_quarterLogLatticeRescale
    (n m : ℤ) (f g : BombieriTest) :
    bombieriTwoBlockGlobalCrossSymbol
        (quarterLogLatticeRescale n f)
        (quarterLogLatticeRescale m g) =
      bombieriTwoBlockGlobalCrossSymbol f
        (normalizedDilation (quarterLogLatticePoint (n - m))
          (quarterLogLatticePoint_pos (n - m)) g) := by
  unfold quarterLogLatticeRescale
  rw [bombieriTwoBlockGlobalCrossSymbol_relativeDilation]
  have hratio :
      (quarterLogLatticePoint m)⁻¹ /
          (quarterLogLatticePoint n)⁻¹ =
        quarterLogLatticePoint (n - m) := by
    calc
      (quarterLogLatticePoint m)⁻¹ /
          (quarterLogLatticePoint n)⁻¹ =
          quarterLogLatticePoint n / quarterLogLatticePoint m := by
        rw [div_eq_mul_inv, inv_inv, div_eq_mul_inv]
        ring
      _ = quarterLogLatticePoint (n - m) :=
        quarterLogLatticePoint_div n m
  apply congrArg (bombieriTwoBlockGlobalCrossSymbol f)
  apply TestFunction.ext
  intro x
  simp only [normalizedDilation_apply]
  rw [hratio]

/-- The diagonal of a physical quarter-lattice cell is the diagonal of its
normalized base seed. -/
theorem bombieriGlobalDiagonal_quarterLogLatticeRescale
    (n : ℤ) (f : BombieriTest) :
    (bombieriFunctional
      (bombieriQuadraticTest (quarterLogLatticeRescale n f))).re =
        (bombieriFunctional (bombieriQuadraticTest f)).re := by
  unfold quarterLogLatticeRescale
  exact bombieriGlobalDiagonal_normalizedDilation
    (quarterLogLatticePoint n)⁻¹
    (inv_pos.mpr (quarterLogLatticePoint_pos n)) f

/-- Physical realization of a finite list of indexed normalized seeds. -/
def quarterLogLatticePhysicalCells
    (cells : List (ℤ × BombieriTest)) : List BombieriTest :=
  cells.map fun p ↦ quarterLogLatticeRescale p.1 p.2

@[simp]
theorem quarterLogLatticePhysicalCells_nil :
    quarterLogLatticePhysicalCells [] = [] := rfl

@[simp]
theorem quarterLogLatticePhysicalCells_cons
    (p : ℤ × BombieriTest) (tail : List (ℤ × BombieriTest)) :
    quarterLogLatticePhysicalCells (p :: tail) =
      quarterLogLatticeRescale p.1 p.2 ::
        quarterLogLatticePhysicalCells tail := rfl

/-- Every unordered cross, expressed through normalized base seeds and their
signed quarter-lattice lag. -/
def quarterLogLatticePairCrossSum : List (ℤ × BombieriTest) → ℝ
  | [] => 0
  | p :: tail =>
      (tail.map (fun q ↦
        2 * (bombieriTwoBlockGlobalCrossSymbol p.2
          (normalizedDilation (quarterLogLatticePoint (p.1 - q.1))
            (quarterLogLatticePoint_pos (p.1 - q.1)) q.2)).re)).sum +
        quarterLogLatticePairCrossSum tail

private theorem bombieriCellPairCrossSum_quarterLogLatticePhysicalCells
    (cells : List (ℤ × BombieriTest)) :
    bombieriCellPairCrossSum (quarterLogLatticePhysicalCells cells) =
      quarterLogLatticePairCrossSum cells := by
  induction cells with
  | nil =>
      simp [quarterLogLatticePhysicalCells, bombieriCellPairCrossSum,
        quarterLogLatticePairCrossSum]
  | cons p tail ih =>
      rw [quarterLogLatticePhysicalCells_cons]
      simp only [bombieriCellPairCrossSum, quarterLogLatticePairCrossSum]
      rw [ih]
      congr 1
      apply congrArg List.sum
      simp only [quarterLogLatticePhysicalCells, List.map_map]
      apply List.map_congr_left
      intro q hq
      change
        2 * (bombieriTwoBlockGlobalCrossSymbol
          (quarterLogLatticeRescale p.1 p.2)
          (quarterLogLatticeRescale q.1 q.2)).re = _
      rw [bombieriTwoBlockGlobalCrossSymbol_quarterLogLatticeRescale]

private theorem quarterLogLatticePhysicalCells_diagonal_sum
    (cells : List (ℤ × BombieriTest)) :
    ((quarterLogLatticePhysicalCells cells).map (fun f ↦
      (bombieriFunctional (bombieriQuadraticTest f)).re)).sum =
        (cells.map (fun p ↦
          (bombieriFunctional (bombieriQuadraticTest p.2)).re)).sum := by
  induction cells with
  | nil => simp [quarterLogLatticePhysicalCells]
  | cons p tail ih =>
      change
        (bombieriFunctional
            (bombieriQuadraticTest
              (quarterLogLatticeRescale p.1 p.2))).re +
            ((quarterLogLatticePhysicalCells tail).map (fun f ↦
              (bombieriFunctional (bombieriQuadraticTest f)).re)).sum =
          (bombieriFunctional (bombieriQuadraticTest p.2)).re +
            (tail.map (fun q ↦
              (bombieriFunctional (bombieriQuadraticTest q.2)).re)).sum
      rw [bombieriGlobalDiagonal_quarterLogLatticeRescale, ih]

/-- Every Bombieri quadratic is exactly a finite quarter-lattice Gram: the
base-seed diagonals plus the complete local-minus-prime cross at signed
integer lags. -/
theorem exists_quarterLogLattice_gram_decomposition (g : BombieriTest) :
    ∃ cells : List (ℤ × BombieriTest),
      (quarterLogLatticePhysicalCells cells).sum = g ∧
      (∀ p ∈ cells,
        tsupport p.2 ⊆ Set.Icc 1 (quarterLogLatticePoint 2)) ∧
      (bombieriFunctional (bombieriQuadraticTest g)).re =
        (cells.map (fun p ↦
          (bombieriFunctional (bombieriQuadraticTest p.2)).re)).sum +
          quarterLogLatticePairCrossSum cells := by
  obtain ⟨cells, hsum, hsupport⟩ :=
    exists_quarterLogLattice_decomposition g
  refine ⟨cells, hsum, hsupport, ?_⟩
  have hgram :=
    bombieriFunctional_list_sum_re_eq_diagonal_add_pairs
      (quarterLogLatticePhysicalCells cells)
  have hsum' : (quarterLogLatticePhysicalCells cells).sum = g := by
    simpa only [quarterLogLatticePhysicalCells] using hsum
  rw [hsum', quarterLogLatticePhysicalCells_diagonal_sum,
    bombieriCellPairCrossSum_quarterLogLatticePhysicalCells] at hgram
  exact hgram

end

end ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeGramStructural
