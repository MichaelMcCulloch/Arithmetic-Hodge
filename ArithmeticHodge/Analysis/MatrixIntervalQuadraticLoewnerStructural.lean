import ArithmeticHodge.Analysis.MatrixIntervalQuadraticSOS

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.MatrixIntervalQuadraticLoewnerStructural

open MatrixIntervalQuadraticSOS

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-!
# Loewner forms of interval quadratic SOS certificates

Exact matrix identities are not necessary for the interval SOS handoff.  A
positive-semidefinite lower gap transfers positive definiteness just as well,
which permits analytic Grams to be replaced by structural upper certificates.
-/

/-- Increasing both the affine-lift Gram and the interval reserve increases
the represented matrix quadratic in the Loewner order on `[-1,1]`. -/
theorem intervalQuadratic_loewner
    (Qzero Qone : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (Rzero Rone : Matrix n n ℝ) (a : ℝ)
    (hQ : (Qone - Qzero).PosSemidef)
    (hR : (Rone - Rzero).PosSemidef)
    (ha : a ^ 2 ≤ 1) :
    (((affineLiftMatrix (n := n) a)ᴴ * Qone *
          affineLiftMatrix (n := n) a +
        (1 - a ^ 2) • Rone) -
      ((affineLiftMatrix (n := n) a)ᴴ * Qzero *
          affineLiftMatrix (n := n) a +
        (1 - a ^ 2) • Rzero)).PosSemidef := by
  have hGram := hQ.conjTranspose_mul_mul_same
    (affineLiftMatrix (n := n) a)
  have hReserve := hR.smul (sub_nonneg.mpr ha)
  have hsum := hGram.add hReserve
  have heq :
      ((affineLiftMatrix (n := n) a)ᴴ * Qone *
            affineLiftMatrix (n := n) a +
          (1 - a ^ 2) • Rone) -
        ((affineLiftMatrix (n := n) a)ᴴ * Qzero *
            affineLiftMatrix (n := n) a +
          (1 - a ^ 2) • Rzero) =
      (affineLiftMatrix (n := n) a)ᴴ * (Qone - Qzero) *
          affineLiftMatrix (n := n) a +
        (1 - a ^ 2) • (Rone - Rzero) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    module
  rw [heq]
  exact hsum

/-- A matrix lying above an interval quadratic SOS expression is positive
definite whenever the fixed Gram is positive definite and the reserve is
positive semidefinite. -/
theorem posDef_of_intervalQuadratic_sos_loewner_lower
    (Q : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (R H : Matrix n n ℝ) (a : ℝ)
    (hQ : Q.PosDef) (hR : R.PosSemidef)
    (ha : a ^ 2 ≤ 1)
    (hLower :
      (H - ((affineLiftMatrix (n := n) a)ᴴ * Q *
          affineLiftMatrix (n := n) a +
        (1 - a ^ 2) • R)).PosSemidef) :
    H.PosDef := by
  let base : Matrix n n ℝ :=
    (affineLiftMatrix (n := n) a)ᴴ * Q *
        affineLiftMatrix (n := n) a +
      (1 - a ^ 2) • R
  have hBase : base.PosDef := by
    apply posDef_of_intervalQuadratic_sos Q R base a hQ hR ha
    rfl
  have hsum := hBase.add_posSemidef hLower
  have heq : base + (H - base) = H := by module
  rwa [heq] at hsum

/-- It is enough to prove positive definiteness of any fixed Loewner lower
bound for the affine-lift Gram appearing in an exact interval SOS identity. -/
theorem posDef_of_intervalQuadratic_sos_of_fixedGram_lower
    (Q lowerQ : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (R H : Matrix n n ℝ) (a : ℝ)
    (hLowerQ : lowerQ.PosDef)
    (hGap : (Q - lowerQ).PosSemidef)
    (hR : R.PosSemidef)
    (ha : a ^ 2 ≤ 1)
    (hH : H =
      (affineLiftMatrix (n := n) a)ᴴ * Q *
          affineLiftMatrix (n := n) a +
        (1 - a ^ 2) • R) :
    H.PosDef := by
  have hQsum := hLowerQ.add_posSemidef hGap
  have heq : lowerQ + (Q - lowerQ) = Q := by module
  have hQ : Q.PosDef := by rwa [heq] at hQsum
  exact posDef_of_intervalQuadratic_sos Q R H a hQ hR ha hH

end

end ArithmeticHodge.Analysis.MatrixIntervalQuadraticLoewnerStructural
