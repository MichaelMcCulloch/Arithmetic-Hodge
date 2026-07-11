import ArithmeticHodge.Analysis.RationalInterval
import Mathlib.Data.Matrix.Basic

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.RationalIntervalSchur

open RatInterval

noncomputable section

/-!
# Interval-certified Schur elimination

`intervalSchurStep` performs exact rational interval arithmetic, while
`realSchurStep` records the corresponding real Schur update.  The main
containment theorems show that a kernel-computed sequence of positive pivot
intervals encloses every real elimination stage and certifies positivity of
the corresponding real pivots.
-/

variable {n : Type*}

def realSchurStep (p : n) (A : Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j ↦ A i j - A i p * A p j / A p p

def intervalSchurStep (p : n) (M : Matrix n n RatInterval) :
    Matrix n n RatInterval :=
  fun i j ↦ M i j - M i p * M p j / M p p

theorem intervalSchurStep_contains
    (p : n) (M : Matrix n n RatInterval) (A : Matrix n n ℝ)
    (hp : 0 < (M p p).lower)
    (hM : ∀ i j, (M i j).Contains (A i j)) :
    ∀ i j, (intervalSchurStep p M i j).Contains
      (realSchurStep p A i j) := by
  intro i j
  apply contains_sub (hM i j)
  exact contains_div_of_pos hp
    (contains_mul (hM i p) (hM p j)) (hM p p)

def realEliminate : List n → Matrix n n ℝ → Matrix n n ℝ
  | [], A => A
  | p :: ps, A => realEliminate ps (realSchurStep p A)

def intervalEliminate : List n → Matrix n n RatInterval →
    Matrix n n RatInterval
  | [], M => M
  | p :: ps, M => intervalEliminate ps (intervalSchurStep p M)

def PositivePivots : List n → Matrix n n RatInterval → Prop
  | [], _ => True
  | p :: ps, M =>
      0 < (M p p).lower ∧ PositivePivots ps (intervalSchurStep p M)

instance positivePivotsDecidable
    (ps : List n) (M : Matrix n n RatInterval) :
    Decidable (PositivePivots ps M) := by
  induction ps generalizing M with
  | nil => exact isTrue trivial
  | cons p ps ih =>
      rw [PositivePivots]
      letI : Decidable (PositivePivots ps (intervalSchurStep p M)) :=
        ih (intervalSchurStep p M)
      infer_instance

def RealPositivePivots : List n → Matrix n n ℝ → Prop
  | [], _ => True
  | p :: ps, A =>
      0 < A p p ∧ RealPositivePivots ps (realSchurStep p A)

theorem intervalEliminate_contains
    (ps : List n) (M : Matrix n n RatInterval) (A : Matrix n n ℝ)
    (hpos : PositivePivots ps M)
    (hM : ∀ i j, (M i j).Contains (A i j)) :
    ∀ i j, (intervalEliminate ps M i j).Contains
      (realEliminate ps A i j) := by
  induction ps generalizing M A with
  | nil => exact hM
  | cons p ps ih =>
      exact ih (M := intervalSchurStep p M) (A := realSchurStep p A)
        hpos.2 (intervalSchurStep_contains p M A hpos.1 hM)

theorem realPositivePivots_of_interval
    (ps : List n) (M : Matrix n n RatInterval) (A : Matrix n n ℝ)
    (hpos : PositivePivots ps M)
    (hM : ∀ i j, (M i j).Contains (A i j)) :
    RealPositivePivots ps A := by
  induction ps generalizing M A with
  | nil => trivial
  | cons p ps ih =>
      constructor
      · exact ((Rat.cast_pos (K := ℝ)).2 hpos.1).trans_le (hM p p).1
      · exact ih (M := intervalSchurStep p M) (A := realSchurStep p A)
          hpos.2 (intervalSchurStep_contains p M A hpos.1 hM)

end

end ArithmeticHodge.Analysis.RationalIntervalSchur
