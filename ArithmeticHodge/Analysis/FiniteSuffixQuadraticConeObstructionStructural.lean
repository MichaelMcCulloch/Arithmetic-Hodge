import Mathlib

set_option autoImplicit false

open LinearMap

namespace ArithmeticHodge.Analysis.FiniteSuffixQuadraticConeObstructionStructural

noncomputable section

/-!
# Proper suffix positivity does not close the full suffix

For a symmetric real bilinear form `B`, write `Q(x) = B(x,x)`.  At one
backward-induction step the exact identity is

`Q(head + tail) = Q(head) + Q(tail) + 2 B(head,tail)`.

Thus nonnegative cell diagonals and a nonnegative proper tail do not determine
the sign after adjoining the new head.  The missing datum is exactly the
one-sided row-to-whole-tail bound

`-(Q(head) + Q(tail)) / 2 <= B(head,tail)`.

The three-cell rational form below has every cell diagonal equal to `1`, its
two proper suffix values equal to `1` and `2`, but its full suffix value equal
to `-1`.  No numerical search or approximation enters the witness.
-/

section AbstractStep

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Quadratic value associated with a real bilinear form. -/
def symmetricQuadraticValue (B : LinearMap.BilinForm ℝ V) (x : V) : ℝ :=
  B x x

/-- Quadratic value of the sum of a finite ordered cell list. -/
def finiteSuffixQuadraticValue
    (B : LinearMap.BilinForm ℝ V) (cells : List V) : ℝ :=
  symmetricQuadraticValue B cells.sum

/-- Exact head--tail expansion for a symmetric real bilinear form. -/
theorem symmetricQuadraticValue_add
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) (head tail : V) :
    symmetricQuadraticValue B (head + tail) =
      symmetricQuadraticValue B head +
        symmetricQuadraticValue B tail + 2 * B head tail := by
  unfold symmetricQuadraticValue
  simp only [map_add, LinearMap.add_apply]
  have hsymm : B tail head = B head tail := by
    simpa using (hB.eq head tail).symm
  rw [hsymm]
  ring

/-- List form of the same identity at one suffix-induction step. -/
theorem finiteSuffixQuadraticValue_cons
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (head : V) (tail : List V) :
    finiteSuffixQuadraticValue B (head :: tail) =
      symmetricQuadraticValue B head +
        finiteSuffixQuadraticValue B tail +
          2 * B head tail.sum := by
  rw [finiteSuffixQuadraticValue, List.sum_cons,
    symmetricQuadraticValue_add B hB]
  rfl

/-- The missing row/cross inequality is necessary and sufficient for adjoining
one cell to a proper suffix. -/
theorem finiteSuffixQuadraticValue_cons_nonnegative_iff_row_bound
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (head : V) (tail : List V) :
    0 ≤ finiteSuffixQuadraticValue B (head :: tail) ↔
      -(symmetricQuadraticValue B head +
          finiteSuffixQuadraticValue B tail) / 2 ≤
        B head tail.sum := by
  rw [finiteSuffixQuadraticValue_cons B hB]
  constructor <;> intro h <;> linarith

/-- Nonnegative head and tail values close the next suffix once, and only
once, the row-to-tail cross satisfies the displayed lower bound. -/
theorem finiteSuffixQuadraticValue_cons_nonnegative_of_row_bound
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (head : V) (tail : List V)
    (_hhead : 0 ≤ symmetricQuadraticValue B head)
    (_htail : 0 ≤ finiteSuffixQuadraticValue B tail)
    (hrow : -(symmetricQuadraticValue B head +
        finiteSuffixQuadraticValue B tail) / 2 ≤ B head tail.sum) :
    0 ≤ finiteSuffixQuadraticValue B (head :: tail) := by
  exact (finiteSuffixQuadraticValue_cons_nonnegative_iff_row_bound
    B hB head tail).2 hrow

end AbstractStep

/-! ## Exact three-cell witness -/

/-- Three ordered real cell coordinates. -/
abbrev ThreeCellVector := ℝ × ℝ × ℝ

/-- Symmetric rational bilinear form with matrix

`[[1,-2,0],[-2,1,0],[0,0,1]]`.
-/
def finiteSuffixObstructionForm :
    LinearMap.BilinForm ℝ ThreeCellVector :=
  LinearMap.mk₂ ℝ
    (fun x y : ThreeCellVector ↦
      x.1 * y.1 + x.2.1 * y.2.1 + x.2.2 * y.2.2 -
        2 * (x.1 * y.2.1 + x.2.1 * y.1))
    (by
      intro x₁ x₂ y
      simp only [Prod.fst_add, Prod.snd_add]
      ring)
    (by
      intro c x y
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring)
    (by
      intro x y₁ y₂
      simp only [Prod.fst_add, Prod.snd_add]
      ring)
    (by
      intro c x y
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring)

theorem finiteSuffixObstructionForm_isSymm :
    finiteSuffixObstructionForm.IsSymm := by
  constructor
  intro x y
  change RingHom.id ℝ
      (x.1 * y.1 + x.2.1 * y.2.1 + x.2.2 * y.2.2 -
        2 * (x.1 * y.2.1 + x.2.1 * y.1)) =
    y.1 * x.1 + y.2.1 * x.2.1 + y.2.2 * x.2.2 -
      2 * (y.1 * x.2.1 + y.2.1 * x.1)
  rw [RingHom.id_apply]
  ring

/-- First, second, and third coordinate cells. -/
def obstructionCell₀ : ThreeCellVector := (1, 0, 0)
def obstructionCell₁ : ThreeCellVector := (0, 1, 0)
def obstructionCell₂ : ThreeCellVector := (0, 0, 1)

/-- Every individual cell diagonal is strictly positive, in fact equal to
one. -/
theorem finiteSuffixObstruction_cell_diagonals :
    symmetricQuadraticValue finiteSuffixObstructionForm obstructionCell₀ = 1 ∧
      symmetricQuadraticValue finiteSuffixObstructionForm obstructionCell₁ = 1 ∧
        symmetricQuadraticValue finiteSuffixObstructionForm obstructionCell₂ = 1 := by
  norm_num [symmetricQuadraticValue, finiteSuffixObstructionForm,
    obstructionCell₀, obstructionCell₁, obstructionCell₂]

/-- The last one-cell proper suffix is positive. -/
theorem finiteSuffixObstruction_last_suffix :
    finiteSuffixQuadraticValue finiteSuffixObstructionForm
      [obstructionCell₂] = 1 := by
  norm_num [finiteSuffixQuadraticValue, symmetricQuadraticValue,
    finiteSuffixObstructionForm, obstructionCell₂]

/-- The terminal empty suffix has the expected zero value. -/
theorem finiteSuffixObstruction_empty_suffix :
    finiteSuffixQuadraticValue finiteSuffixObstructionForm [] = 0 := by
  norm_num [finiteSuffixQuadraticValue, symmetricQuadraticValue]

/-- The two-cell proper suffix is also positive. -/
theorem finiteSuffixObstruction_twoCell_suffix :
    finiteSuffixQuadraticValue finiteSuffixObstructionForm
      [obstructionCell₁, obstructionCell₂] = 2 := by
  norm_num [finiteSuffixQuadraticValue, symmetricQuadraticValue,
    finiteSuffixObstructionForm, obstructionCell₁, obstructionCell₂]

/-- Nevertheless the full three-cell suffix is strictly negative. -/
theorem finiteSuffixObstruction_full_suffix :
    finiteSuffixQuadraticValue finiteSuffixObstructionForm
      [obstructionCell₀, obstructionCell₁, obstructionCell₂] = -1 := by
  norm_num [finiteSuffixQuadraticValue, symmetricQuadraticValue,
    finiteSuffixObstructionForm, obstructionCell₀, obstructionCell₁,
    obstructionCell₂]

/-- The precise failed inequality: the first row pairs with the whole proper
tail by `-2`, below the required threshold `-3/2`. -/
theorem finiteSuffixObstruction_missing_row_bound :
    finiteSuffixObstructionForm obstructionCell₀
        ([obstructionCell₁, obstructionCell₂] : List ThreeCellVector).sum <
      -(symmetricQuadraticValue finiteSuffixObstructionForm obstructionCell₀ +
          finiteSuffixQuadraticValue finiteSuffixObstructionForm
            [obstructionCell₁, obstructionCell₂]) / 2 := by
  norm_num [finiteSuffixQuadraticValue, symmetricQuadraticValue,
    finiteSuffixObstructionForm, obstructionCell₀, obstructionCell₁,
    obstructionCell₂]

/-- Exact existential counterexample to the proposed suffix induction:
positive cell diagonals and all proper suffix values do not force the full
suffix value to be nonnegative. -/
theorem exists_threeCell_properSuffixes_positive_fullSuffix_negative :
    ∃ (B : LinearMap.BilinForm ℝ ThreeCellVector)
        (e₀ e₁ e₂ : ThreeCellVector),
      B.IsSymm ∧
        0 < symmetricQuadraticValue B e₀ ∧
        0 < symmetricQuadraticValue B e₁ ∧
        0 < symmetricQuadraticValue B e₂ ∧
        0 < finiteSuffixQuadraticValue B [e₂] ∧
        0 < finiteSuffixQuadraticValue B [e₁, e₂] ∧
        0 ≤ finiteSuffixQuadraticValue B [] ∧
        finiteSuffixQuadraticValue B [e₀, e₁, e₂] < 0 := by
  refine ⟨finiteSuffixObstructionForm, obstructionCell₀,
    obstructionCell₁, obstructionCell₂,
    finiteSuffixObstructionForm_isSymm, ?_⟩
  rw [finiteSuffixObstruction_cell_diagonals.1,
    finiteSuffixObstruction_cell_diagonals.2.1,
    finiteSuffixObstruction_cell_diagonals.2.2,
    finiteSuffixObstruction_last_suffix,
    finiteSuffixObstruction_twoCell_suffix,
    finiteSuffixObstruction_empty_suffix,
    finiteSuffixObstruction_full_suffix]
  norm_num

end

end ArithmeticHodge.Analysis.FiniteSuffixQuadraticConeObstructionStructural
