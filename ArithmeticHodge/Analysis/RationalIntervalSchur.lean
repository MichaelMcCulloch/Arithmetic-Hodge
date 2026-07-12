import ArithmeticHodge.Analysis.RationalInterval
import Mathlib.Analysis.Matrix.PosDef
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

section PosDef

open Matrix
open scoped BigOperators ComplexOrder

variable [Fintype n]

/-- The real quadratic form associated with a matrix. -/
def realQuadratic (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x)

/-- Completing the square at one pivot gives the exact Schur decomposition
of the real quadratic form. -/
theorem realQuadratic_schurStep
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (p : n) (x : n → ℝ) :
    realQuadratic A x =
      (∑ j, A p j * x j) ^ 2 / A p p +
        realQuadratic (realSchurStep p A) x := by
  have hsym (i : n) : A i p = A p i := by
    simpa using hA.apply p i
  have hcorr :
      (∑ i, x i * ∑ j, (A i p * A p j / A p p) * x j) =
        (∑ j, A p j * x j) ^ 2 / A p p := by
    calc
      (∑ i, x i * ∑ j, (A i p * A p j / A p p) * x j) =
          ∑ i, ∑ j,
            ((A p i * x i) * (A p j * x j)) / A p p := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hsym i]
        ring
      _ = ((∑ i, A p i * x i) * ∑ j, A p j * x j) / A p p := by
        rw [Fintype.sum_mul_sum]
        simp_rw [Finset.sum_div]
      _ = (∑ j, A p j * x j) ^ 2 / A p p := by ring
  unfold realQuadratic realSchurStep
  simp only [dotProduct, mulVec]
  simp_rw [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [hcorr]
  simp_rw [Finset.mul_sum]
  ring

omit [Fintype n] in
theorem realSchurStep_isHermitian
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (p : n) :
    (realSchurStep p A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [realSchurStep, star_trivial]
  rw [show A j i = A i j by simpa using hA.apply i j,
    show A j p = A p j by simpa using hA.apply p j,
    show A p i = A i p by simpa using hA.apply i p]
  ring

omit [Fintype n] in
theorem realSchurStep_pivot_row_zero
    (A : Matrix n n ℝ) (p j : n) (hp : A p p ≠ 0) :
    realSchurStep p A p j = 0 := by
  unfold realSchurStep
  field_simp [hp]
  ring

omit [Fintype n] in
theorem realSchurStep_pivot_column_zero
    (A : Matrix n n ℝ) (p i : n) (hp : A p p ≠ 0) :
    realSchurStep p A i p = 0 := by
  unfold realSchurStep
  field_simp [hp]
  ring

omit [Fintype n] in
theorem realSchurStep_row_zero
    (A : Matrix n n ℝ) (p i : n) (hi : ∀ j, A i j = 0) :
    ∀ j, realSchurStep p A i j = 0 := by
  intro j
  simp [realSchurStep, hi]

/-- The matrix has no nonzero rows outside the listed active indices. -/
def RowsZeroOutside (ps : List n) (A : Matrix n n ℝ) : Prop :=
  ∀ i, i ∉ ps → ∀ j, A i j = 0

omit [Fintype n] in
theorem rowsZeroOutside_schurStep
    (A : Matrix n n ℝ) (p : n) (ps : List n)
    (hp : A p p ≠ 0) (hrows : RowsZeroOutside (p :: ps) A) :
    RowsZeroOutside ps (realSchurStep p A) := by
  intro i hi j
  by_cases hip : i = p
  · subst i
    exact realSchurStep_pivot_row_zero A p j hp
  · apply realSchurStep_row_zero A p i
    exact hrows i (by simp [hip, hi])

/-- Recursive positivity and kernel control for a Hermitian matrix supported
on the pivot list. -/
theorem realQuadratic_nonneg_and_eq_zero_on_pivots
    (ps : List n) (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (hpos : RealPositivePivots ps A)
    (hnodup : ps.Nodup) (hrows : RowsZeroOutside ps A)
    (x : n → ℝ) :
    0 ≤ realQuadratic A x ∧
      (realQuadratic A x = 0 → ∀ i ∈ ps, x i = 0) := by
  classical
  induction ps generalizing A with
  | nil =>
      have hAzero : A = 0 := by
        ext i j
        exact hrows i (by simp) j
      subst A
      simp [realQuadratic]
  | cons p ps ih =>
      have hd : 0 < A p p := hpos.1
      have hdne : A p p ≠ 0 := hd.ne'
      have hSsym : (realSchurStep p A).IsHermitian :=
        realSchurStep_isHermitian A hA p
      have hSrows : RowsZeroOutside ps (realSchurStep p A) :=
        rowsZeroOutside_schurStep A p ps hdne hrows
      have hrec := ih (realSchurStep p A) hSsym hpos.2
        (List.nodup_cons.mp hnodup).2 hSrows
      have hid := realQuadratic_schurStep A hA p x
      let s : ℝ := ∑ j, A p j * x j
      have hterm : 0 ≤ s ^ 2 / A p p := div_nonneg (sq_nonneg s) hd.le
      constructor
      · change 0 ≤ realQuadratic A x
        change realQuadratic A x = s ^ 2 / A p p +
          realQuadratic (realSchurStep p A) x at hid
        linarith [hrec.1]
      · intro hq i hi
        change realQuadratic A x = s ^ 2 / A p p +
          realQuadratic (realSchurStep p A) x at hid
        have htermZero : s ^ 2 / A p p = 0 := by
          linarith [hrec.1]
        have hSzero : realQuadratic (realSchurStep p A) x = 0 := by
          linarith
        have hxps : ∀ j ∈ ps, x j = 0 := hrec.2 hSzero
        simp only [List.mem_cons] at hi
        rcases hi with hip | hi
        · subst i
          have hsSq : s ^ 2 = 0 :=
            (div_eq_zero_iff.mp htermZero).resolve_right hdne
          have hsZero : s = 0 := sq_eq_zero_iff.mp hsSq
          have hsum : s = A p p * x p := by
            dsimp [s]
            apply Fintype.sum_eq_single p
            intro j hjp
            by_cases hjps : j ∈ ps
            · rw [hxps j hjps, mul_zero]
            · have hjout : j ∉ p :: ps := by simp [hjp, hjps]
              have hzero : A p j = 0 := by
                calc
                  A p j = A j p := by simpa using hA.apply j p
                  _ = 0 := hrows j hjout p
              rw [hzero, zero_mul]
          rw [hsum] at hsZero
          exact (mul_eq_zero.mp hsZero).resolve_left hdne
        · exact hxps i hi

/-- Positive real Schur pivots over a duplicate-free exhaustive list certify
positive definiteness. -/
theorem posDef_of_realPositivePivots
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (ps : List n)
    (hpos : RealPositivePivots ps A) (hnodup : ps.Nodup)
    (hcover : ∀ i, i ∈ ps) : A.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hA fun x hx ↦ ?_
  have hrows : RowsZeroOutside ps A := by
    intro i hi
    exact (hi (hcover i)).elim
  have hq := realQuadratic_nonneg_and_eq_zero_on_pivots
    ps A hA hpos hnodup hrows x
  have hqne : realQuadratic A x ≠ 0 := by
    intro hzero
    apply hx
    funext i
    exact hq.2 hzero i (hcover i)
  have hqpos : 0 < realQuadratic A x :=
    lt_of_le_of_ne hq.1 hqne.symm
  simpa [realQuadratic] using hqpos

/-- A kernel-checked sequence of positive rational interval pivots certifies
positive definiteness of every enclosed Hermitian real matrix. -/
theorem posDef_of_intervalPositivePivots
    (M : Matrix n n RatInterval) (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (ps : List n)
    (hpos : PositivePivots ps M) (hnodup : ps.Nodup)
    (hcover : ∀ i, i ∈ ps)
    (hM : ∀ i j, (M i j).Contains (A i j)) : A.PosDef :=
  posDef_of_realPositivePivots A hA ps
    (realPositivePivots_of_interval ps M A hpos hM) hnodup hcover

/-- Entrywise coercion of a real matrix to a complex matrix. -/
def complexOfRealMatrix (A : Matrix n n ℝ) : Matrix n n ℂ :=
  fun i j ↦ (A i j : ℂ)

omit [Fintype n] in
/-- A Hermitian real matrix remains Hermitian after entrywise coercion to
complex scalars. -/
theorem complexOfRealMatrix_isHermitian
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (complexOfRealMatrix A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [complexOfRealMatrix]
  rw [Complex.star_def, Complex.conj_ofReal]
  norm_cast
  simpa using hA.apply i j

private theorem star_mul_ofReal_mul_re (z w : ℂ) (a : ℝ) :
    (star z * (a : ℂ) * w).re =
      a * (z.re * w.re + z.im * w.im) := by
  rw [Complex.star_def]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The complex quadratic form of a real matrix splits into its real- and
imaginary-coordinate real quadratic forms. -/
theorem complexOfRealMatrix_quadratic_re
    (A : Matrix n n ℝ) (z : n → ℂ) :
    (star z ⬝ᵥ (complexOfRealMatrix A *ᵥ z)).re =
      realQuadratic A (fun i ↦ (z i).re) +
        realQuadratic A (fun i ↦ (z i).im) := by
  have hleft :
      (star z ⬝ᵥ (complexOfRealMatrix A *ᵥ z)).re =
        ∑ i, ∑ j, (star (z i) * (A i j : ℂ) * z j).re := by
    simp only [dotProduct, mulVec, complexOfRealMatrix, Finset.mul_sum,
      Complex.re_sum, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    congr 1
    ring
  rw [hleft]
  simp_rw [star_mul_ofReal_mul_re]
  unfold realQuadratic
  simp only [dotProduct, mulVec]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Real positive definiteness implies complex positive definiteness after
entrywise coercion. -/
theorem Matrix.PosDef.complexOfReal
    {A : Matrix n n ℝ} (hA : A.PosDef) :
    (complexOfRealMatrix A).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (complexOfRealMatrix_isHermitian hA.1) fun z hz ↦ ?_
  apply RCLike.pos_iff.mpr
  refine ⟨?_,
    (complexOfRealMatrix_isHermitian hA.1).im_star_dotProduct_mulVec_self z⟩
  change 0 < (star z ⬝ᵥ (complexOfRealMatrix A *ᵥ z)).re
  rw [complexOfRealMatrix_quadratic_re]
  by_cases hre : (fun i ↦ (z i).re) = 0
  · have him : (fun i ↦ (z i).im) ≠ 0 := by
      intro him
      apply hz
      funext i
      apply Complex.ext
      · exact congr_fun hre i
      · exact congr_fun him i
    have hreZero : realQuadratic A (fun i ↦ (z i).re) = 0 := by
      rw [hre]
      simp [realQuadratic]
    rw [hreZero, zero_add]
    simpa [realQuadratic] using hA.re_dotProduct_pos him
  · have himNonneg : 0 ≤ realQuadratic A (fun i ↦ (z i).im) := by
      by_cases him : (fun i ↦ (z i).im) = 0
      · rw [him]
        simp [realQuadratic]
      · exact (hA.re_dotProduct_pos him).le
    exact add_pos_of_pos_of_nonneg
      (by simpa [realQuadratic] using hA.re_dotProduct_pos hre) himNonneg

/-- A rational interval Schur certificate for a real Hermitian matrix also
certifies positive definiteness of its complex entrywise coercion. -/
theorem complexPosDef_of_intervalPositivePivots
    (M : Matrix n n RatInterval) (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (ps : List n)
    (hpos : PositivePivots ps M) (hnodup : ps.Nodup)
    (hcover : ∀ i, i ∈ ps)
    (hM : ∀ i j, (M i j).Contains (A i j)) :
    (complexOfRealMatrix A).PosDef :=
  Matrix.PosDef.complexOfReal
    (posDef_of_intervalPositivePivots M A hA ps hpos hnodup hcover hM)

end PosDef

end

end ArithmeticHodge.Analysis.RationalIntervalSchur
