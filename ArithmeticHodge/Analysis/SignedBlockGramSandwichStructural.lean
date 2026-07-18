import ArithmeticHodge.Analysis.MatrixPosSemidefTraceDominationStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.SignedBlockGramSandwichStructural

noncomputable section

/-!
# Two-sided sandwiches for signed block Grams

An auxiliary Gram may occur negatively on one block and positively on another.
An upper certificate is sound for the negative occurrence, while a lower
certificate is sound for the positive occurrence.  The identities below
package the resulting exact positive-semidefinite error.
-/

/-- A block diagonal matrix is positive semidefinite when both diagonal
blocks are positive semidefinite. -/
theorem posSemidef_fromBlocks_zero_offDiagonal
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℝ} {D : Matrix κ κ ℝ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.IsHermitian.fromBlocks hA.isHermitian (by simp) hD.isHermitian
  · intro x
    have hAquad := hA.re_dotProduct_nonneg (x ∘ Sum.inl)
    have hDquad := hD.re_dotProduct_nonneg (x ∘ Sum.inr)
    simpa [dotProduct, mulVec, Fintype.sum_sum_type] using
      add_nonneg hAquad hDquad

/-- Lift a matrix with a negative upper and positive lower diagonal block. -/
def signedDiagonalLift {ι : Type*} (G : Matrix ι ι ℝ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks (-G) 0 0 G

/-- Exact matrix containing a whole negative Gram and a signed auxiliary
Gram. -/
def exactSignedBlockGram
    {ι : Type*}
    (low nonquotientEven evenGram : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (nonquotientOdd oddGram : Matrix ι ι ℝ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  low - nonquotientEven - evenGram +
    signedDiagonalLift nonquotientOdd + signedDiagonalLift oddGram

/-- Inverse-free lower sandwich using upper certificates for the whole and
upper-block Grams and a lower certificate for the favorable lower block. -/
def signedBlockGramSandwich
    {ι : Type*}
    (low nonquotientEven upperEven : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (nonquotientOdd upperOdd lowerOdd : Matrix ι ι ℝ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  low - nonquotientEven - upperEven +
    signedDiagonalLift nonquotientOdd +
    Matrix.fromBlocks (-upperOdd) 0 0 lowerOdd

/-- The exact signed-block Gram is its sandwich plus exactly the three
Loewner certificate gaps. -/
theorem exactSignedBlockGram_eq_sandwich_add_gaps
    {ι : Type*}
    (low nonquotientEven evenGram upperEven :
      Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (nonquotientOdd oddGram upperOdd lowerOdd : Matrix ι ι ℝ) :
    exactSignedBlockGram low nonquotientEven evenGram
        nonquotientOdd oddGram =
      signedBlockGramSandwich low nonquotientEven upperEven
          nonquotientOdd upperOdd lowerOdd +
        ((upperEven - evenGram) +
          Matrix.fromBlocks (upperOdd - oddGram) 0 0
            (oddGram - lowerOdd)) := by
  unfold exactSignedBlockGram signedBlockGramSandwich signedDiagonalLift
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp <;> module

/-- Positive definiteness of the sandwich transfers to the exact signed-block
Gram when the two upper and one lower Loewner certificates are sound. -/
theorem exactSignedBlockGram_posDef_of_sandwich
    {ι : Type*} [Fintype ι]
    (low nonquotientEven evenGram upperEven :
      Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (nonquotientOdd oddGram upperOdd lowerOdd : Matrix ι ι ℝ)
    (hUpperEven : (upperEven - evenGram).PosSemidef)
    (hUpperOdd : (upperOdd - oddGram).PosSemidef)
    (hLowerOdd : (oddGram - lowerOdd).PosSemidef)
    (hSandwich :
      (signedBlockGramSandwich low nonquotientEven upperEven
        nonquotientOdd upperOdd lowerOdd).PosDef) :
    (exactSignedBlockGram low nonquotientEven evenGram
      nonquotientOdd oddGram).PosDef := by
  rw [exactSignedBlockGram_eq_sandwich_add_gaps]
  exact hSandwich.add_posSemidef
    (hUpperEven.add
      (posSemidef_fromBlocks_zero_offDiagonal hUpperOdd hLowerOdd))

/-- Scalar specialization using trace multiples of the identity for both
upper Gram certificates. -/
def scalarTraceSignedBlockGramSandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (low nonquotientEven : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (nonquotientOdd lowerOdd : Matrix ι ι ℝ)
    (gammaEven gammaOdd : ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  signedBlockGramSandwich low nonquotientEven
    (gammaEven • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ))
    nonquotientOdd (gammaOdd • (1 : Matrix ι ι ℝ)) lowerOdd

/-- Trace bounds reduce both negative Gram occurrences to scalar identity
reserves; only the favorable lower Gram certificate remains matrix-valued. -/
theorem exactSignedBlockGram_posDef_of_scalarTraceSandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (low nonquotientEven evenGram : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (nonquotientOdd oddGram lowerOdd : Matrix ι ι ℝ)
    (gammaEven gammaOdd : ℝ)
    (hEven : evenGram.PosSemidef) (hOdd : oddGram.PosSemidef)
    (hEvenTrace : evenGram.trace ≤ gammaEven)
    (hOddTrace : oddGram.trace ≤ gammaOdd)
    (hLowerOdd : (oddGram - lowerOdd).PosSemidef)
    (hSandwich :
      (scalarTraceSignedBlockGramSandwich low nonquotientEven
        nonquotientOdd lowerOdd gammaEven gammaOdd).PosDef) :
    (exactSignedBlockGram low nonquotientEven evenGram
      nonquotientOdd oddGram).PosDef := by
  apply exactSignedBlockGram_posDef_of_sandwich
    low nonquotientEven evenGram
    (gammaEven • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ))
    nonquotientOdd oddGram (gammaOdd • (1 : Matrix ι ι ℝ)) lowerOdd
  · exact Matrix.PosSemidef.scalar_smul_one_sub_of_trace_le hEven hEvenTrace
  · exact Matrix.PosSemidef.scalar_smul_one_sub_of_trace_le hOdd hOddTrace
  · exact hLowerOdd
  · exact hSandwich

/-! ## Sharper sandwich around an existing lower projection -/

/-- Lower sandwich that reuses a lower odd certificate and upper-bounds only
its projection defect, rather than the entire odd Gram. -/
def projectedDefectSignedBlockGramSandwich
    {ι : Type*}
    (low nonquotientEven upperEven : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (nonquotientOdd lowerOdd upperOddDefect : Matrix ι ι ℝ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  low - nonquotientEven - upperEven +
    signedDiagonalLift nonquotientOdd +
    Matrix.fromBlocks (-(lowerOdd + upperOddDefect)) 0 0 lowerOdd

/-- The exact Gram differs from the projected-defect sandwich by the even
upper-certificate gap and a block diagonal pair consisting of the odd defect
upper-certificate gap and the favorable odd projection defect itself. -/
theorem exactSignedBlockGram_eq_projectedDefectSandwich_add_gaps
    {ι : Type*}
    (low nonquotientEven evenGram upperEven :
      Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (nonquotientOdd oddGram lowerOdd upperOddDefect : Matrix ι ι ℝ) :
    exactSignedBlockGram low nonquotientEven evenGram
        nonquotientOdd oddGram =
      projectedDefectSignedBlockGramSandwich low nonquotientEven upperEven
          nonquotientOdd lowerOdd upperOddDefect +
        ((upperEven - evenGram) +
          Matrix.fromBlocks
            (upperOddDefect - (oddGram - lowerOdd)) 0 0
            (oddGram - lowerOdd)) := by
  unfold exactSignedBlockGram projectedDefectSignedBlockGramSandwich
    signedDiagonalLift
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp <;> module

/-- Soundness of the sharper sandwich: only the odd projection defect needs
an upper certificate. -/
theorem exactSignedBlockGram_posDef_of_projectedDefectSandwich
    {ι : Type*} [Fintype ι]
    (low nonquotientEven evenGram upperEven :
      Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (nonquotientOdd oddGram lowerOdd upperOddDefect : Matrix ι ι ℝ)
    (hUpperEven : (upperEven - evenGram).PosSemidef)
    (hOddDefect : (oddGram - lowerOdd).PosSemidef)
    (hUpperOddDefect :
      (upperOddDefect - (oddGram - lowerOdd)).PosSemidef)
    (hSandwich :
      (projectedDefectSignedBlockGramSandwich low nonquotientEven upperEven
        nonquotientOdd lowerOdd upperOddDefect).PosDef) :
    (exactSignedBlockGram low nonquotientEven evenGram
      nonquotientOdd oddGram).PosDef := by
  rw [exactSignedBlockGram_eq_projectedDefectSandwich_add_gaps]
  exact hSandwich.add_posSemidef
    (hUpperEven.add
      (posSemidef_fromBlocks_zero_offDiagonal hUpperOddDefect hOddDefect))

/-- Scalar-trace specialization of the projection-defect sandwich. -/
def scalarTraceProjectedDefectSignedBlockGramSandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (low nonquotientEven : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (nonquotientOdd lowerOdd : Matrix ι ι ℝ)
    (gammaEven gammaOddDefect : ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  projectedDefectSignedBlockGramSandwich low nonquotientEven
    (gammaEven • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ))
    nonquotientOdd lowerOdd
    (gammaOddDefect • (1 : Matrix ι ι ℝ))

/-- Trace domination reduces the sharp projected-defect route to one even
trace bound, one odd residual trace bound, and positivity of an inverse-free
fixed sandwich. -/
theorem exactSignedBlockGram_posDef_of_scalarTraceProjectedDefectSandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (low nonquotientEven evenGram : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (nonquotientOdd oddGram lowerOdd : Matrix ι ι ℝ)
    (gammaEven gammaOddDefect : ℝ)
    (hEven : evenGram.PosSemidef)
    (hOddDefect : (oddGram - lowerOdd).PosSemidef)
    (hEvenTrace : evenGram.trace ≤ gammaEven)
    (hOddDefectTrace : (oddGram - lowerOdd).trace ≤ gammaOddDefect)
    (hSandwich :
      (scalarTraceProjectedDefectSignedBlockGramSandwich
        low nonquotientEven nonquotientOdd lowerOdd
        gammaEven gammaOddDefect).PosDef) :
    (exactSignedBlockGram low nonquotientEven evenGram
      nonquotientOdd oddGram).PosDef := by
  apply exactSignedBlockGram_posDef_of_projectedDefectSandwich
    low nonquotientEven evenGram
    (gammaEven • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ))
    nonquotientOdd oddGram lowerOdd
    (gammaOddDefect • (1 : Matrix ι ι ℝ))
  · exact Matrix.PosSemidef.scalar_smul_one_sub_of_trace_le hEven hEvenTrace
  · exact hOddDefect
  · exact Matrix.PosSemidef.scalar_smul_one_sub_of_trace_le
      hOddDefect hOddDefectTrace
  · exact hSandwich

end

end ArithmeticHodge.Analysis.SignedBlockGramSandwichStructural
