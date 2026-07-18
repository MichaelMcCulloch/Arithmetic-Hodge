import ArithmeticHodge.Analysis.MultiplicativeWeilFixedLogLatticePartitionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilGlobalCrossAdditiveStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Exact Gram reduction on the fixed half-octave lattice

The fixed partition writes every Bombieri test as finitely many rescaled base
seeds supported in `[1,2]`.  Common-dilation covariance now removes the
absolute lattice locations from every complete local-minus-prime cross: only
the integer lag and the two base seeds remain.

This is an exact reduction, not a positivity assumption.
-/

/-- Ratios of fixed lattice points are lattice points at the integer
difference. -/
theorem fixedLogLatticePoint_div
    (n m : ℤ) :
    fixedLogLatticePoint n / fixedLogLatticePoint m =
      fixedLogLatticePoint (n - m) := by
  unfold fixedLogLatticePoint
  rw [← Real.exp_sub]
  congr 1
  push_cast
  ring

/-- The complete cross of two physical lattice cells depends only on their
integer lag and their normalized base seeds. -/
theorem bombieriTwoBlockGlobalCrossSymbol_fixedLogLatticeRescale
    (n m : ℤ) (f g : BombieriTest) :
    bombieriTwoBlockGlobalCrossSymbol
        (fixedLogLatticeRescale n f)
        (fixedLogLatticeRescale m g) =
      bombieriTwoBlockGlobalCrossSymbol f
        (normalizedDilation (fixedLogLatticePoint (n - m))
          (fixedLogLatticePoint_pos (n - m)) g) := by
  unfold fixedLogLatticeRescale
  rw [bombieriTwoBlockGlobalCrossSymbol_relativeDilation]
  have hratio :
      (fixedLogLatticePoint m)⁻¹ /
          (fixedLogLatticePoint n)⁻¹ =
        fixedLogLatticePoint (n - m) := by
    calc
      (fixedLogLatticePoint m)⁻¹ /
          (fixedLogLatticePoint n)⁻¹ =
          fixedLogLatticePoint n / fixedLogLatticePoint m := by
        rw [div_eq_mul_inv, inv_inv, div_eq_mul_inv]
        ring
      _ = fixedLogLatticePoint (n - m) :=
        fixedLogLatticePoint_div n m
  apply congrArg (bombieriTwoBlockGlobalCrossSymbol f)
  apply TestFunction.ext
  intro x
  simp only [normalizedDilation_apply]
  rw [hratio]

/-- The diagonal of a physical lattice cell is the diagonal of its base
seed. -/
theorem bombieriGlobalDiagonal_fixedLogLatticeRescale
    (n : ℤ) (f : BombieriTest) :
    (bombieriFunctional
      (bombieriQuadraticTest (fixedLogLatticeRescale n f))).re =
        (bombieriFunctional (bombieriQuadraticTest f)).re := by
  unfold fixedLogLatticeRescale
  exact bombieriGlobalDiagonal_normalizedDilation
    (fixedLogLatticePoint n)⁻¹
    (inv_pos.mpr (fixedLogLatticePoint_pos n)) f

/-- Physical realization of a finite list of indexed base seeds. -/
def fixedLogLatticePhysicalCells
    (cells : List (ℤ × BombieriTest)) : List BombieriTest :=
  cells.map fun p ↦ fixedLogLatticeRescale p.1 p.2

@[simp]
theorem fixedLogLatticePhysicalCells_nil :
    fixedLogLatticePhysicalCells [] = [] := rfl

@[simp]
theorem fixedLogLatticePhysicalCells_cons
    (p : ℤ × BombieriTest) (tail : List (ℤ × BombieriTest)) :
    fixedLogLatticePhysicalCells (p :: tail) =
      fixedLogLatticeRescale p.1 p.2 ::
        fixedLogLatticePhysicalCells tail := rfl

/-- Every unordered cross, expressed entirely through normalized base seeds
and their signed lattice lag. -/
def fixedLogLatticePairCrossSum : List (ℤ × BombieriTest) → ℝ
  | [] => 0
  | p :: tail =>
      (tail.map (fun q ↦
        2 * (bombieriTwoBlockGlobalCrossSymbol p.2
          (normalizedDilation (fixedLogLatticePoint (p.1 - q.1))
            (fixedLogLatticePoint_pos (p.1 - q.1)) q.2)).re)).sum +
        fixedLogLatticePairCrossSum tail

private theorem bombieriCellPairCrossSum_fixedLogLatticePhysicalCells
    (cells : List (ℤ × BombieriTest)) :
    bombieriCellPairCrossSum (fixedLogLatticePhysicalCells cells) =
      fixedLogLatticePairCrossSum cells := by
  induction cells with
  | nil => simp [fixedLogLatticePhysicalCells, bombieriCellPairCrossSum,
      fixedLogLatticePairCrossSum]
  | cons p tail ih =>
      rw [fixedLogLatticePhysicalCells_cons]
      simp only [bombieriCellPairCrossSum, fixedLogLatticePairCrossSum]
      rw [ih]
      congr 1
      apply congrArg List.sum
      simp only [fixedLogLatticePhysicalCells, List.map_map]
      apply List.map_congr_left
      intro q hq
      change
        2 * (bombieriTwoBlockGlobalCrossSymbol
          (fixedLogLatticeRescale p.1 p.2)
          (fixedLogLatticeRescale q.1 q.2)).re = _
      rw [bombieriTwoBlockGlobalCrossSymbol_fixedLogLatticeRescale]

private theorem fixedLogLatticePhysicalCells_diagonal_sum
    (cells : List (ℤ × BombieriTest)) :
    ((fixedLogLatticePhysicalCells cells).map (fun f ↦
      (bombieriFunctional (bombieriQuadraticTest f)).re)).sum =
        (cells.map (fun p ↦
          (bombieriFunctional (bombieriQuadraticTest p.2)).re)).sum := by
  induction cells with
  | nil => simp [fixedLogLatticePhysicalCells]
  | cons p tail ih =>
      change
        (bombieriFunctional
            (bombieriQuadraticTest
              (fixedLogLatticeRescale p.1 p.2))).re +
            ((fixedLogLatticePhysicalCells tail).map (fun f ↦
              (bombieriFunctional (bombieriQuadraticTest f)).re)).sum =
          (bombieriFunctional (bombieriQuadraticTest p.2)).re +
            (tail.map (fun q ↦
              (bombieriFunctional (bombieriQuadraticTest q.2)).re)).sum
      rw [bombieriGlobalDiagonal_fixedLogLatticeRescale, ih]

/-- Every Bombieri quadratic is exactly a finite fixed-lattice Gram:
base-cell diagonals plus the complete local-minus-prime kernel at signed
integer lags. -/
theorem exists_fixedLogLattice_gram_decomposition (g : BombieriTest) :
    ∃ cells : List (ℤ × BombieriTest),
      (fixedLogLatticePhysicalCells cells).sum = g ∧
      (∀ p ∈ cells, tsupport p.2 ⊆ Set.Icc 1 2) ∧
      (bombieriFunctional (bombieriQuadraticTest g)).re =
        (cells.map (fun p ↦
          (bombieriFunctional (bombieriQuadraticTest p.2)).re)).sum +
          fixedLogLatticePairCrossSum cells := by
  obtain ⟨cells, hsum, hsupport⟩ :=
    exists_fixedLogLattice_decomposition g
  refine ⟨cells, hsum, hsupport, ?_⟩
  have hgram :=
    bombieriFunctional_list_sum_re_eq_diagonal_add_pairs
      (fixedLogLatticePhysicalCells cells)
  have hsum' : (fixedLogLatticePhysicalCells cells).sum = g := by
    simpa only [fixedLogLatticePhysicalCells] using hsum
  rw [hsum', fixedLogLatticePhysicalCells_diagonal_sum,
    bombieriCellPairCrossSum_fixedLogLatticePhysicalCells] at hgram
  exact hgram

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
