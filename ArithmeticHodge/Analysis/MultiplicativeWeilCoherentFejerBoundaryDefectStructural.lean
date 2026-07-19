import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFejerResidualParentMaskStructural

set_option autoImplicit false

open Complex Filter Real Set
open scoped BigOperators ContDiff Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFejerBoundaryDefectStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilFejerLinearResidualStructural

/-!
# The coherent Fejer boundary defect

Differentiating a coherent parent mask in its first slot produces derivatives
of the partition weights.  For the complete quadratic mask those derivatives
cancel against partition unity.  This module identifies exactly what remains
after splitting that mask into the order-three Fejer reserve and its residual:
the residual boundary is the negative of the reserve boundary.
-/

def weightValueSum : List (ℝ → ℝ) → ℝ → ℝ
  | [], _z => 0
  | eta :: tail, z => eta z + weightValueSum tail z

def weightDerivativeSum : List (ℝ → ℝ) → ℝ → ℝ
  | [], _z => 0
  | eta :: tail, z => deriv eta z + weightDerivativeSum tail z

def diagonalBoundaryMask
    (etas : List (ℝ → ℝ)) (x y : ℝ) : ℝ :=
  match etas with
  | [] => 0
  | eta :: tail =>
      deriv eta (x * y) * eta y + diagonalBoundaryMask tail x y

def pairSymmetricLagBoundaryMask
    (c : ℝ) (eta theta : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (c / 2) *
    (deriv eta (x * y) * theta y +
      deriv theta (x * y) * eta y)

def headSymmetricLagBoundaryMask
    (w : ℕ → ℝ) (eta : ℝ → ℝ) :
    ℕ → List (ℝ → ℝ) → ℝ → ℝ → ℝ
  | _k, [], _x, _y => 0
  | k, theta :: tail, x, y =>
      pairSymmetricLagBoundaryMask (w k) eta theta x y +
        headSymmetricLagBoundaryMask w eta (k + 1) tail x y

def symmetricLinearLagBoundaryMask
    (w : ℕ → ℝ) :
    List (ℝ → ℝ) → ℝ → ℝ → ℝ
  | [], _x, _y => 0
  | eta :: tail, x, y =>
      headSymmetricLagBoundaryMask w eta 1 tail x y +
        symmetricLinearLagBoundaryMask w tail x y

def linearFejerThreeBoundaryMask
    (etas : List (ℝ → ℝ)) (x y : ℝ) : ℝ :=
  diagonalBoundaryMask etas x y +
    symmetricLinearLagBoundaryMask bombieriFejerThreeLagWeight etas x y

private theorem headBoundaryMask_two
    (eta : ℝ → ℝ) (k : ℕ) (tail : List (ℝ → ℝ)) (x y : ℝ) :
    headSymmetricLagBoundaryMask (fun _n ↦ 2) eta k tail x y =
      deriv eta (x * y) * weightValueSum tail y +
        weightDerivativeSum tail (x * y) * eta y := by
  induction tail generalizing k with
  | nil => simp [headSymmetricLagBoundaryMask, weightValueSum,
      weightDerivativeSum]
  | cons theta tail ih =>
      simp only [headSymmetricLagBoundaryMask, pairSymmetricLagBoundaryMask,
        weightValueSum, weightDerivativeSum]
      rw [ih]
      ring

private theorem fullBoundaryMask_eq_product
    (etas : List (ℝ → ℝ)) (x y : ℝ) :
    diagonalBoundaryMask etas x y +
        symmetricLinearLagBoundaryMask (fun _n ↦ 2) etas x y =
      weightDerivativeSum etas (x * y) * weightValueSum etas y := by
  induction etas with
  | nil => simp [diagonalBoundaryMask, symmetricLinearLagBoundaryMask,
      weightDerivativeSum, weightValueSum]
  | cons eta tail ih =>
      simp only [diagonalBoundaryMask, symmetricLinearLagBoundaryMask,
        weightDerivativeSum, weightValueSum]
      rw [headBoundaryMask_two]
      linear_combination ih

private theorem headBoundaryMask_add
    (u v : ℕ → ℝ) (eta : ℝ → ℝ) (k : ℕ)
    (tail : List (ℝ → ℝ)) (x y : ℝ) :
    headSymmetricLagBoundaryMask (fun n ↦ u n + v n)
        eta k tail x y =
      headSymmetricLagBoundaryMask u eta k tail x y +
        headSymmetricLagBoundaryMask v eta k tail x y := by
  induction tail generalizing k with
  | nil => simp [headSymmetricLagBoundaryMask]
  | cons theta tail ih =>
      simp only [headSymmetricLagBoundaryMask, pairSymmetricLagBoundaryMask]
      rw [ih]
      ring

private theorem boundaryMask_add
    (u v : ℕ → ℝ) (etas : List (ℝ → ℝ)) (x y : ℝ) :
    symmetricLinearLagBoundaryMask (fun n ↦ u n + v n) etas x y =
      symmetricLinearLagBoundaryMask u etas x y +
        symmetricLinearLagBoundaryMask v etas x y := by
  induction etas with
  | nil => simp [symmetricLinearLagBoundaryMask]
  | cons eta tail ih =>
      simp only [symmetricLinearLagBoundaryMask]
      rw [headBoundaryMask_add, ih]
      ring

/-- Before using partition unity, the reserve and residual first-slot
boundaries add to the derivative of the complete rank-one parent mask. -/
theorem linearFejerThreeBoundary_add_residual_eq_full
    (etas : List (ℝ → ℝ)) (x y : ℝ) :
    linearFejerThreeBoundaryMask etas x y +
        symmetricLinearLagBoundaryMask
          bombieriFejerThreeResidualLagWeight etas x y =
      weightDerivativeSum etas (x * y) * weightValueSum etas y := by
  rw [← fullBoundaryMask_eq_product]
  unfold linearFejerThreeBoundaryMask
  rw [add_assoc]
  congr 1
  rw [← boundaryMask_add]
  apply congrArg (fun w : ℕ → ℝ ↦
    symmetricLinearLagBoundaryMask w etas x y)
  funext k
  exact bombieriFejerThreeLagWeight_add_residual k

private theorem weightValueSum_hasDerivAt
    (etas : List (ℝ → ℝ))
    (hsmooth : ∀ eta ∈ etas, ContDiff ℝ ∞ eta)
    (z : ℝ) :
    HasDerivAt (weightValueSum etas)
      (weightDerivativeSum etas z) z := by
  induction etas with
  | nil =>
      simpa [weightValueSum, weightDerivativeSum] using
        (hasDerivAt_const z (0 : ℝ))
  | cons eta tail ih =>
      have heta : HasDerivAt eta (deriv eta z) z :=
        ((hsmooth eta (by simp)).differentiable (by simp) z).hasDerivAt
      have htail := ih (fun theta htheta ↦ hsmooth theta (by simp [htheta]))
      simpa [weightValueSum, weightDerivativeSum] using heta.add htail

/-- Partition unity on the parent's topological support forces the derivative
of the total partition weight to vanish wherever the parent is nonzero. -/
theorem weightDerivativeSum_eq_zero_of_parent_ne_zero
    (parent : BombieriTest) (etas : List (ℝ → ℝ))
    (hsmooth : ∀ eta ∈ etas, ContDiff ℝ ∞ eta)
    (hsum : ∀ z ∈ tsupport parent, weightValueSum etas z = 1)
    {z : ℝ} (hz : parent z ≠ 0) :
    weightDerivativeSum etas z = 0 := by
  have heq : weightValueSum etas =ᶠ[𝓝 z] (fun _w : ℝ ↦ 1) := by
    filter_upwards
      [parent.contDiff.continuous.continuousAt.eventually_ne hz] with w hw
    exact hsum w (subset_tsupport parent (Function.mem_support.mpr hw))
  have hderiv := heq.deriv_eq
  rw [(weightValueSum_hasDerivAt etas hsmooth z).deriv] at hderiv
  simpa using hderiv

/-- Against a coherent parent, the residual boundary is exactly the negative
of the Fejer-reserve boundary.  This is the boundary defect that survives
when the residual is treated by itself. -/
theorem parent_mul_residualBoundary_eq_neg_fejerBoundary
    (parent : BombieriTest) (etas : List (ℝ → ℝ))
    (hsmooth : ∀ eta ∈ etas, ContDiff ℝ ∞ eta)
    (hsum : ∀ z ∈ tsupport parent, weightValueSum etas z = 1)
    (x y : ℝ) :
    parent (x * y) *
        symmetricLinearLagBoundaryMask
          bombieriFejerThreeResidualLagWeight etas x y =
      -parent (x * y) * linearFejerThreeBoundaryMask etas x y := by
  by_cases hp : parent (x * y) = 0
  · simp [hp]
  · have hzero := weightDerivativeSum_eq_zero_of_parent_ne_zero
      parent etas hsmooth hsum hp
    have hsplit := linearFejerThreeBoundary_add_residual_eq_full etas x y
    rw [hzero, zero_mul] at hsplit
    rw [show symmetricLinearLagBoundaryMask
          bombieriFejerThreeResidualLagWeight etas x y =
        -linearFejerThreeBoundaryMask etas x y by linarith]
    push_cast
    ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFejerBoundaryDefectStructural
