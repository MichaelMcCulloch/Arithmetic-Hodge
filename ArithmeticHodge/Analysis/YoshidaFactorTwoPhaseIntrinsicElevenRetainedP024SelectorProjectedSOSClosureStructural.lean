import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddMixedProjectionStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorProjectedSOSClosureStructural

open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddMixedProjectionStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderGramStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural

noncomputable section

/-!
# Projected closure of the retained P024 asymmetric SOS Gram

The bad upper alternating block is kept exact.  Only the favorable lower
shifted-remainder block is replaced by a sound finite projection.  The gap
between the exact and projected SOS Grams is therefore a single positive
block diagonal correction.
-/

/-- A positive semidefinite matrix remains positive semidefinite after it is
embedded as the lower diagonal block of a larger zero matrix. -/
theorem posSemidef_fromBlocks_zero_zero_right
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {D : Matrix κ κ ℝ} (hD : D.PosSemidef) :
    (Matrix.fromBlocks (0 : Matrix ι ι ℝ) 0 0 D).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.IsHermitian.fromBlocks (by simp) (by simp) hD.isHermitian
  · intro x
    have h := hD.re_dotProduct_nonneg (x ∘ Sum.inr)
    simpa [dotProduct, mulVec, Fintype.sum_sum_type] using h

/-- Fixed asymmetric SOS Gram with only the favorable lower odd remainder
replaced by an arbitrary matrix `N`. -/
def retainedP024SelectorProjectedAsymmetricSOSGram
    (N : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  retainedP024SharpLowSOSGram - retainedP024SelectorWholeEvenGram +
    Matrix.fromBlocks
      (-retainedP024SelectorAlternatingGram) 0 0
      (retainedP024SelectorAlternatingNonquotientGram + N)

/-- The exact asymmetric SOS Gram is the projected Gram plus the single
lower-block projection residual. -/
theorem retainedP024SelectorAsymmetricSOSGram_eq_projected_add
    (N : Matrix (Fin 3) (Fin 3) ℝ) :
    retainedP024SelectorAsymmetricSOSGram =
      retainedP024SelectorProjectedAsymmetricSOSGram N +
        Matrix.fromBlocks 0 0 0
          (retainedP024SelectorAlternatingShiftedRemainderGram - N) := by
  rw [retainedP024SelectorAsymmetricSOSGram_eq_structural]
  unfold retainedP024SelectorAlternatingSignedLiftGram
  rw [retainedP024SelectorAlternatingGram_eq_nonquotient_add_remainder]
  unfold retainedP024SelectorProjectedAsymmetricSOSGram
  rw [retainedP024SelectorAlternatingGram_eq_nonquotient_add_remainder]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp <;> module

/-- Positive definiteness of the fixed projected Gram transfers to the exact
asymmetric SOS Gram whenever `N` is a sound lower Gram. -/
theorem retainedP024SelectorAsymmetricSOSGram_posDef_of_projected
    (N : Matrix (Fin 3) (Fin 3) ℝ)
    (hN : (retainedP024SelectorAlternatingShiftedRemainderGram - N).PosSemidef)
    (hProjected : (retainedP024SelectorProjectedAsymmetricSOSGram N).PosDef) :
    retainedP024SelectorAsymmetricSOSGram.PosDef := by
  rw [retainedP024SelectorAsymmetricSOSGram_eq_projected_add]
  exact hProjected.add_posSemidef
    (posSemidef_fromBlocks_zero_zero_right hN)

/-- The concrete denominator-`10^4` mixed projection reduces the analytic
P024 closure to one fixed `6 x 6` positive-definiteness theorem. -/
def retainedP024SelectorMixedProjectedAsymmetricSOSGram :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  retainedP024SelectorProjectedAsymmetricSOSGram
    retainedP024OddMixedProjectionCertificateGram

theorem retainedP024SelectorAsymmetricSOSGram_posDef_of_mixedProjected
    (hProjected : retainedP024SelectorMixedProjectedAsymmetricSOSGram.PosDef) :
    retainedP024SelectorAsymmetricSOSGram.PosDef := by
  exact retainedP024SelectorAsymmetricSOSGram_posDef_of_projected
    retainedP024OddMixedProjectionCertificateGram
    retainedP024OddMixedProjectionCertificateGram_le hProjected

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorProjectedSOSClosureStructural
