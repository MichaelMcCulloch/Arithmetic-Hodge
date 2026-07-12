import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false

open Matrix
open scoped BigOperators InnerProductSpace

namespace ArithmeticHodge.Analysis

noncomputable section

/-!
# Structural positivity of Stieltjes--Loewner kernels

This file contains no numerical certificates.  It records the algebra behind
the positive kernels obtained by taking divided differences of
`t \mapsto a * t / (t + lambda)`, and realizes finite sums of those kernels as
honest Gram matrices.
-/

private theorem real_inner_scalar (x y : ℝ) :
    ⟪x, y⟫_ℝ = x * y := by
  change y * x = x * y
  ring

/-- A single summand of `t` times a Stieltjes transform. -/
def stieltjesAtomTransform (a lambda t : ℝ) : ℝ :=
  a * t / (t + lambda)

/-- The Loewner kernel associated to one Stieltjes atom. -/
def stieltjesLoewnerAtom (a lambda x y : ℝ) : ℝ :=
  a * lambda / ((x + lambda) * (y + lambda))

theorem stieltjesAtomTransform_dividedDifference
    {a lambda x y : ℝ} (hxy : x ≠ y)
    (hx : x + lambda ≠ 0) (hy : y + lambda ≠ 0) :
    (stieltjesAtomTransform a lambda x -
        stieltjesAtomTransform a lambda y) / (x - y) =
      stieltjesLoewnerAtom a lambda x y := by
  unfold stieltjesAtomTransform stieltjesLoewnerAtom
  field_simp [sub_ne_zero.mpr hxy, hx, hy]
  ring

theorem hasDerivAt_stieltjesAtomTransform
    {a lambda t : ℝ} (h : t + lambda ≠ 0) :
    HasDerivAt (stieltjesAtomTransform a lambda)
      (a * lambda / (t + lambda) ^ 2) t := by
  have hnum : HasDerivAt (fun x : ℝ ↦ a * x) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have hden : HasDerivAt (fun x : ℝ ↦ x + lambda) 1 t := by
    simpa using (hasDerivAt_id t).add_const lambda
  convert hnum.div hden h using 1 <;> ring

/-- The matrix contributed by one Stieltjes atom. -/
def stieltjesLoewnerAtomMatrix
    {ι : Type*} (node : ι → ℝ) (a lambda : ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ stieltjesLoewnerAtom a lambda (node i) (node j)

/-- The scalar feature whose Gram matrix is one Stieltjes atom matrix. -/
def stieltjesLoewnerAtomFeature
    {ι : Type*} (node : ι → ℝ) (a lambda : ℝ) (i : ι) : ℝ :=
  Real.sqrt (a * lambda) / (node i + lambda)

theorem stieltjesLoewnerAtomMatrix_eq_gram
    {ι : Type*} (node : ι → ℝ) {a lambda : ℝ}
    (hweight : 0 ≤ a * lambda) :
    stieltjesLoewnerAtomMatrix node a lambda =
      Matrix.gram ℝ (stieltjesLoewnerAtomFeature node a lambda) := by
  ext i j
  simp only [stieltjesLoewnerAtomMatrix, stieltjesLoewnerAtom,
    Matrix.gram_apply, stieltjesLoewnerAtomFeature]
  rw [real_inner_scalar]
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hweight]

theorem stieltjesLoewnerAtomMatrix_posSemidef
    {ι : Type*} [Finite ι] (node : ι → ℝ) {a lambda : ℝ}
    (hweight : 0 ≤ a * lambda) :
    (stieltjesLoewnerAtomMatrix node a lambda).PosSemidef := by
  rw [stieltjesLoewnerAtomMatrix_eq_gram node hweight]
  exact Matrix.posSemidef_gram ℝ _

/-- A finite Stieltjes--Loewner kernel, expressed as a sum of atom matrices. -/
def finiteStieltjesLoewnerMatrix
    {ι κ : Type*} [Fintype κ]
    (node : ι → ℝ) (weight pole : κ → ℝ) : Matrix ι ι ℝ :=
  ∑ k, stieltjesLoewnerAtomMatrix node (weight k) (pole k)

/-- The vector-valued Stieltjes feature for a finite collection of atoms. -/
def finiteStieltjesLoewnerFeature
    {ι κ : Type*} [Fintype κ]
    (node : ι → ℝ) (weight pole : κ → ℝ) (i : ι) :
    EuclideanSpace ℝ κ :=
  WithLp.toLp 2 fun k ↦
    Real.sqrt (weight k * pole k) / (node i + pole k)

theorem finiteStieltjesLoewnerMatrix_eq_gram
    {ι κ : Type*} [Fintype κ]
    (node : ι → ℝ) (weight pole : κ → ℝ)
    (hweight : ∀ k, 0 ≤ weight k * pole k) :
    finiteStieltjesLoewnerMatrix node weight pole =
      Matrix.gram ℝ (finiteStieltjesLoewnerFeature node weight pole) := by
  classical
  ext i j
  rw [Matrix.gram_apply, PiLp.inner_apply]
  simp_rw [real_inner_scalar]
  simp only [finiteStieltjesLoewnerMatrix]
  rw [Matrix.sum_apply]
  simp only [stieltjesLoewnerAtomMatrix, stieltjesLoewnerAtom,
    finiteStieltjesLoewnerFeature, WithLp.ofLp_toLp]
  change
    (∑ k, weight k * pole k /
      ((node i + pole k) * (node j + pole k))) =
    ∑ k,
      (Real.sqrt (weight k * pole k) / (node i + pole k)) *
        (Real.sqrt (weight k * pole k) / (node j + pole k))
  apply Finset.sum_congr rfl
  intro k _
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt (hweight k)]

theorem finiteStieltjesLoewnerMatrix_posSemidef
    {ι κ : Type*} [Finite ι] [Fintype κ]
    (node : ι → ℝ) (weight pole : κ → ℝ)
    (hweight : ∀ k, 0 ≤ weight k * pole k) :
    (finiteStieltjesLoewnerMatrix node weight pole).PosSemidef := by
  rw [finiteStieltjesLoewnerMatrix_eq_gram node weight pole hweight]
  exact Matrix.posSemidef_gram ℝ _

/-- Strict positivity is reduced to the structural statement that the
Stieltjes feature vectors are linearly independent. -/
theorem finiteStieltjesLoewnerMatrix_posDef
    {ι κ : Type*} [Finite ι] [Fintype κ]
    (node : ι → ℝ) (weight pole : κ → ℝ)
    (hweight : ∀ k, 0 ≤ weight k * pole k)
    (hlinear : LinearIndependent ℝ
      (finiteStieltjesLoewnerFeature node weight pole)) :
    (finiteStieltjesLoewnerMatrix node weight pole).PosDef := by
  rw [finiteStieltjesLoewnerMatrix_eq_gram node weight pole hweight]
  exact Matrix.posDef_gram_of_linearIndependent hlinear

end

end ArithmeticHodge.Analysis
