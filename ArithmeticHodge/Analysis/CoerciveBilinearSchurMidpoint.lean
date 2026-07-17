import ArithmeticHodge.Analysis.CoerciveBilinearSchurCharacterization

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis

noncomputable section

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]

/-!
# Midpoint curvature of a bilinear Schur complement

The finite and tail blocks of a phase pencil are affine in the phase, but
the Schur complement is not: taking a Riesz representative introduces an
inverse of the tail form.  The identities below give the exact midpoint
defect.  It is the sum of the energies of the two phase-response movements
of the Riesz representative.
-/

/-- Exact midpoint variance identity for Riesz representatives of three
symmetric bilinear forms.  `hmidRiesz` is the affine midpoint identity for
the represented functionals; no inverse or coordinate choice occurs in the
statement. -/
theorem symmetricBilinear_riesz_midpoint_energy_defect
    (Bplus Bminus Bzero : K →L[ℝ] K →L[ℝ] ℝ)
    (rplus rminus rzero : K)
    (hplusSymm : ∀ x y, Bplus x y = Bplus y x)
    (hminusSymm : ∀ x y, Bminus x y = Bminus y x)
    (hmidB : ∀ x y,
      Bplus x y + Bminus x y = 2 * Bzero x y)
    (hmidRiesz : ∀ z,
      Bplus rplus z + Bminus rminus z = 2 * Bzero rzero z) :
    Bplus rplus rplus + Bminus rminus rminus -
          2 * Bzero rzero rzero =
      Bplus (rplus - rzero) (rplus - rzero) +
        Bminus (rminus - rzero) (rminus - rzero) := by
  have hr := hmidRiesz rzero
  have hB := hmidB rzero rzero
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [hplusSymm rzero rplus, hminusSymm rzero rminus]
  linarith

/-- Exact midpoint defect for the corresponding scalar Schur quadratics.
If the two phase-tail forms are positive, the right-hand side is
nonnegative, so the Schur complement bends downward away from the midpoint. -/
theorem symmetricBilinear_schur_midpoint_defect
    (Bplus Bminus Bzero : K →L[ℝ] K →L[ℝ] ℝ)
    (rplus rminus rzero : K) (qplus qminus qzero : ℝ)
    (hplusSymm : ∀ x y, Bplus x y = Bplus y x)
    (hminusSymm : ∀ x y, Bminus x y = Bminus y x)
    (hmidB : ∀ x y,
      Bplus x y + Bminus x y = 2 * Bzero x y)
    (hmidRiesz : ∀ z,
      Bplus rplus z + Bminus rminus z = 2 * Bzero rzero z)
    (hmidQ : qplus + qminus = 2 * qzero) :
    2 * (qzero - Bzero rzero rzero) -
          ((qplus - Bplus rplus rplus) +
            (qminus - Bminus rminus rminus)) =
      Bplus (rplus - rzero) (rplus - rzero) +
        Bminus (rminus - rzero) (rminus - rzero) := by
  have henergy := symmetricBilinear_riesz_midpoint_energy_defect
    Bplus Bminus Bzero rplus rminus rzero
    hplusSymm hminusSymm hmidB hmidRiesz
  linarith

/-- Positivity of the two phase-tail energies turns the exact identity into
midpoint concavity of the scalar Schur quadratic. -/
theorem symmetricBilinear_schur_add_le_two_mul_midpoint
    (Bplus Bminus Bzero : K →L[ℝ] K →L[ℝ] ℝ)
    (rplus rminus rzero : K) (qplus qminus qzero : ℝ)
    (hplusSymm : ∀ x y, Bplus x y = Bplus y x)
    (hminusSymm : ∀ x y, Bminus x y = Bminus y x)
    (hmidB : ∀ x y,
      Bplus x y + Bminus x y = 2 * Bzero x y)
    (hmidRiesz : ∀ z,
      Bplus rplus z + Bminus rminus z = 2 * Bzero rzero z)
    (hmidQ : qplus + qminus = 2 * qzero)
    (hplusNonneg : 0 ≤
      Bplus (rplus - rzero) (rplus - rzero))
    (hminusNonneg : 0 ≤
      Bminus (rminus - rzero) (rminus - rzero)) :
    (qplus - Bplus rplus rplus) +
        (qminus - Bminus rminus rminus) ≤
      2 * (qzero - Bzero rzero rzero) := by
  have hdefect := symmetricBilinear_schur_midpoint_defect
    Bplus Bminus Bzero rplus rminus rzero qplus qminus qzero
    hplusSymm hminusSymm hmidB hmidRiesz hmidQ
  linarith

/-- Matrix form of the exact midpoint defect.  The hypotheses say that the
finite block, tail form, and low--tail functional family are all affine at
the chosen midpoint.  The conclusion shows exactly how much curvature is
introduced by eliminating the coercive tail block. -/
theorem coerciveBilinearCorrectedGram_midpoint_defect
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [Fintype ι]
    (Aplus Aminus Azero : Matrix ι ι ℝ)
    (Bplus Bminus Bzero : H →L[ℝ] H →L[ℝ] ℝ)
    (hBplus : IsCoercive Bplus) (hBminus : IsCoercive Bminus)
    (hBzero : IsCoercive Bzero)
    (hplusSymm : ∀ x y, Bplus x y = Bplus y x)
    (hminusSymm : ∀ x y, Bminus x y = Bminus y x)
    (ellPlus ellMinus ellZero : ι → StrongDual ℝ H)
    (hmidA : ∀ i j, Aplus i j + Aminus i j = 2 * Azero i j)
    (hmidB : ∀ x y,
      Bplus x y + Bminus x y = 2 * Bzero x y)
    (hmidEll : ∀ i x,
      ellPlus i x + ellMinus i x = 2 * ellZero i x)
    (c : ι → ℝ) :
    let rplus := ∑ i, c i • coerciveRieszCorrection hBplus (ellPlus i)
    let rminus := ∑ i, c i • coerciveRieszCorrection hBminus (ellMinus i)
    let rzero := ∑ i, c i • coerciveRieszCorrection hBzero (ellZero i)
    2 * (c ⬝ᵥ
          (coerciveBilinearCorrectedGram
            Azero Bzero hBzero ellZero *ᵥ c)) -
        (c ⬝ᵥ
            (coerciveBilinearCorrectedGram
              Aplus Bplus hBplus ellPlus *ᵥ c) +
          c ⬝ᵥ
            (coerciveBilinearCorrectedGram
              Aminus Bminus hBminus ellMinus *ᵥ c)) =
      Bplus (rplus - rzero) (rplus - rzero) +
        Bminus (rminus - rzero) (rminus - rzero) := by
  classical
  dsimp only
  let rplus : H :=
    ∑ i, c i • coerciveRieszCorrection hBplus (ellPlus i)
  let rminus : H :=
    ∑ i, c i • coerciveRieszCorrection hBminus (ellMinus i)
  let rzero : H :=
    ∑ i, c i • coerciveRieszCorrection hBzero (ellZero i)
  have hrepPlus (z : H) :
      Bplus rplus z = ∑ i, c i * ellPlus i z := by
    dsimp only [rplus]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [coerciveRieszCorrection_apply]
  have hrepMinus (z : H) :
      Bminus rminus z = ∑ i, c i * ellMinus i z := by
    dsimp only [rminus]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [coerciveRieszCorrection_apply]
  have hrepZero (z : H) :
      Bzero rzero z = ∑ i, c i * ellZero i z := by
    dsimp only [rzero]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [coerciveRieszCorrection_apply]
  have hmidEllSum (z : H) :
      (∑ i, c i * ellPlus i z) + (∑ i, c i * ellMinus i z) =
        2 * ∑ i, c i * ellZero i z := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← mul_add, hmidEll i z]
    ring
  have hmidRiesz (z : H) :
      Bplus rplus z + Bminus rminus z = 2 * Bzero rzero z := by
    rw [hrepPlus, hrepMinus, hmidEllSum, hrepZero]
  have hmatrix : Aplus + Aminus = (2 : ℝ) • Azero := by
    ext i j
    simp only [add_apply, smul_apply, smul_eq_mul]
    exact hmidA i j
  have hmidQ :
      c ⬝ᵥ (Aplus *ᵥ c) + c ⬝ᵥ (Aminus *ᵥ c) =
        2 * (c ⬝ᵥ (Azero *ᵥ c)) := by
    rw [← dotProduct_add, ← add_mulVec, hmatrix, smul_mulVec,
      dotProduct_smul]
    rfl
  have hdefect := symmetricBilinear_schur_midpoint_defect
    Bplus Bminus Bzero rplus rminus rzero
    (c ⬝ᵥ (Aplus *ᵥ c)) (c ⬝ᵥ (Aminus *ᵥ c))
    (c ⬝ᵥ (Azero *ᵥ c))
    hplusSymm hminusSymm hmidB hmidRiesz hmidQ
  rw [coerciveBilinearCorrectedGram_quadratic,
    coerciveBilinearCorrectedGram_quadratic,
    coerciveBilinearCorrectedGram_quadratic]
  simpa only [rplus, rminus, rzero] using hdefect

end

end ArithmeticHodge.Analysis
