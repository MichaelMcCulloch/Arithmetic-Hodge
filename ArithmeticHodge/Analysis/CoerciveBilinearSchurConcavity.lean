import ArithmeticHodge.Analysis.CoerciveBilinearSchurCharacterization

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis

noncomputable section

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]

/-!
# Concavity of a bilinear Schur complement

Along an affine segment of symmetric coercive tail forms and affine
low--tail functionals, eliminating the tail is Loewner-concave.  The exact
defect is a weighted variance of the endpoint Riesz representatives around
the representative at the interpolated point.
-/

/-- Exact weighted variance identity for Riesz representatives along an
affine segment of symmetric bilinear forms.  No positivity or restriction on
`t` is needed for the identity. -/
theorem symmetricBilinear_riesz_convex_energy_defect
    (t : ℝ)
    (B0 B1 Bt : K →L[ℝ] K →L[ℝ] ℝ)
    (r0 r1 rt : K)
    (h0Symm : ∀ x y, B0 x y = B0 y x)
    (h1Symm : ∀ x y, B1 x y = B1 y x)
    (haffineB : ∀ x y,
      Bt x y = (1 - t) * B0 x y + t * B1 x y)
    (haffineRiesz : ∀ z,
      Bt rt z = (1 - t) * B0 r0 z + t * B1 r1 z) :
    (1 - t) * B0 r0 r0 + t * B1 r1 r1 - Bt rt rt =
      (1 - t) * B0 (r0 - rt) (r0 - rt) +
        t * B1 (r1 - rt) (r1 - rt) := by
  have hr := haffineRiesz rt
  have hBt := haffineB rt rt
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [h0Symm rt r0, h1Symm rt r1]
  linarith

/-- Exact concavity defect for the scalar Schur quadratic `q - B(r,r)`.
The finite scalar block and represented functional are affine at `t`; the
curvature comes entirely from eliminating the tail variable. -/
theorem symmetricBilinear_schur_convex_defect
    (t : ℝ)
    (B0 B1 Bt : K →L[ℝ] K →L[ℝ] ℝ)
    (r0 r1 rt : K) (q0 q1 qt : ℝ)
    (h0Symm : ∀ x y, B0 x y = B0 y x)
    (h1Symm : ∀ x y, B1 x y = B1 y x)
    (haffineB : ∀ x y,
      Bt x y = (1 - t) * B0 x y + t * B1 x y)
    (haffineRiesz : ∀ z,
      Bt rt z = (1 - t) * B0 r0 z + t * B1 r1 z)
    (haffineQ : qt = (1 - t) * q0 + t * q1) :
    (qt - Bt rt rt) -
          ((1 - t) * (q0 - B0 r0 r0) +
            t * (q1 - B1 r1 r1)) =
      (1 - t) * B0 (r0 - rt) (r0 - rt) +
        t * B1 (r1 - rt) (r1 - rt) := by
  have henergy := symmetricBilinear_riesz_convex_energy_defect
    t B0 B1 Bt r0 r1 rt h0Symm h1Symm haffineB haffineRiesz
  linarith

/-- Nonnegative endpoint energies turn the exact weighted variance identity
into concavity on the whole closed segment. -/
theorem symmetricBilinear_schur_convexCombination_le
    (t : ℝ)
    (B0 B1 Bt : K →L[ℝ] K →L[ℝ] ℝ)
    (r0 r1 rt : K) (q0 q1 qt : ℝ)
    (h0Symm : ∀ x y, B0 x y = B0 y x)
    (h1Symm : ∀ x y, B1 x y = B1 y x)
    (haffineB : ∀ x y,
      Bt x y = (1 - t) * B0 x y + t * B1 x y)
    (haffineRiesz : ∀ z,
      Bt rt z = (1 - t) * B0 r0 z + t * B1 r1 z)
    (haffineQ : qt = (1 - t) * q0 + t * q1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h0Nonneg : 0 ≤ B0 (r0 - rt) (r0 - rt))
    (h1Nonneg : 0 ≤ B1 (r1 - rt) (r1 - rt)) :
    (1 - t) * (q0 - B0 r0 r0) +
        t * (q1 - B1 r1 r1) ≤
      qt - Bt rt rt := by
  have hdefect := symmetricBilinear_schur_convex_defect
    t B0 B1 Bt r0 r1 rt q0 q1 qt
    h0Symm h1Symm haffineB haffineRiesz haffineQ
  have hweight0 : 0 ≤ (1 - t) * B0 (r0 - rt) (r0 - rt) :=
    mul_nonneg (sub_nonneg.mpr ht1) h0Nonneg
  have hweight1 : 0 ≤ t * B1 (r1 - rt) (r1 - rt) :=
    mul_nonneg ht0 h1Nonneg
  linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
private theorem isCoercive_diagonal_nonneg
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : IsCoercive B) (x : H) :
    0 ≤ B x x := by
  obtain ⟨mu, hmu, hdiag⟩ := hB
  exact (by positivity : 0 ≤ mu * ‖x‖ * ‖x‖).trans (hdiag x)

/-- Matrix form of the exact weighted variance defect.  The hypotheses say
that the finite block, tail form, and low--tail functional family are affine
at `t`. -/
theorem coerciveBilinearCorrectedGram_convex_defect
    {ι : Type*} [Fintype ι]
    (t : ℝ)
    (A0 A1 At : Matrix ι ι ℝ)
    (B0 B1 Bt : H →L[ℝ] H →L[ℝ] ℝ)
    (hB0 : IsCoercive B0) (hB1 : IsCoercive B1)
    (hBt : IsCoercive Bt)
    (h0Symm : ∀ x y, B0 x y = B0 y x)
    (h1Symm : ∀ x y, B1 x y = B1 y x)
    (ell0 ell1 ellt : ι → StrongDual ℝ H)
    (haffineA : ∀ i j,
      At i j = (1 - t) * A0 i j + t * A1 i j)
    (haffineB : ∀ x y,
      Bt x y = (1 - t) * B0 x y + t * B1 x y)
    (haffineEll : ∀ i x,
      ellt i x = (1 - t) * ell0 i x + t * ell1 i x)
    (c : ι → ℝ) :
    let r0 := ∑ i, c i • coerciveRieszCorrection hB0 (ell0 i)
    let r1 := ∑ i, c i • coerciveRieszCorrection hB1 (ell1 i)
    let rt := ∑ i, c i • coerciveRieszCorrection hBt (ellt i)
    c ⬝ᵥ
          (coerciveBilinearCorrectedGram At Bt hBt ellt *ᵥ c) -
        ((1 - t) *
            (c ⬝ᵥ
              (coerciveBilinearCorrectedGram A0 B0 hB0 ell0 *ᵥ c)) +
          t *
            (c ⬝ᵥ
              (coerciveBilinearCorrectedGram A1 B1 hB1 ell1 *ᵥ c))) =
      (1 - t) * B0 (r0 - rt) (r0 - rt) +
        t * B1 (r1 - rt) (r1 - rt) := by
  classical
  dsimp only
  let r0 : H :=
    ∑ i, c i • coerciveRieszCorrection hB0 (ell0 i)
  let r1 : H :=
    ∑ i, c i • coerciveRieszCorrection hB1 (ell1 i)
  let rt : H :=
    ∑ i, c i • coerciveRieszCorrection hBt (ellt i)
  have hrep0 (z : H) : B0 r0 z = ∑ i, c i * ell0 i z := by
    dsimp only [r0]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [coerciveRieszCorrection_apply]
  have hrep1 (z : H) : B1 r1 z = ∑ i, c i * ell1 i z := by
    dsimp only [r1]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [coerciveRieszCorrection_apply]
  have hrept (z : H) : Bt rt z = ∑ i, c i * ellt i z := by
    dsimp only [rt]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [coerciveRieszCorrection_apply]
  have haffineEllSum (z : H) :
      (∑ i, c i * ellt i z) =
        (1 - t) * (∑ i, c i * ell0 i z) +
          t * (∑ i, c i * ell1 i z) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [haffineEll i z]
    ring
  have haffineRiesz (z : H) :
      Bt rt z = (1 - t) * B0 r0 z + t * B1 r1 z := by
    rw [hrept, haffineEllSum, hrep0, hrep1]
  have hmatrix : At = (1 - t) • A0 + t • A1 := by
    ext i j
    simp only [add_apply, smul_apply, smul_eq_mul]
    exact haffineA i j
  have haffineQ :
      c ⬝ᵥ (At *ᵥ c) =
        (1 - t) * (c ⬝ᵥ (A0 *ᵥ c)) +
          t * (c ⬝ᵥ (A1 *ᵥ c)) := by
    rw [hmatrix, add_mulVec, smul_mulVec, smul_mulVec,
      dotProduct_add, dotProduct_smul, dotProduct_smul]
    simp only [smul_eq_mul]
  have hdefect := symmetricBilinear_schur_convex_defect
    t B0 B1 Bt r0 r1 rt
    (c ⬝ᵥ (A0 *ᵥ c)) (c ⬝ᵥ (A1 *ᵥ c)) (c ⬝ᵥ (At *ᵥ c))
    h0Symm h1Symm haffineB haffineRiesz haffineQ
  rw [coerciveBilinearCorrectedGram_quadratic,
    coerciveBilinearCorrectedGram_quadratic,
    coerciveBilinearCorrectedGram_quadratic]
  simpa only [r0, r1, rt] using hdefect

/-- Loewner concavity of the corrected Gram along an affine segment.  This
is the quadratic-form statement and therefore does not require choosing
coordinates or inverting any finite matrix. -/
theorem coerciveBilinearCorrectedGram_convexCombination_le
    {ι : Type*} [Fintype ι]
    (t : ℝ)
    (A0 A1 At : Matrix ι ι ℝ)
    (B0 B1 Bt : H →L[ℝ] H →L[ℝ] ℝ)
    (hB0 : IsCoercive B0) (hB1 : IsCoercive B1)
    (hBt : IsCoercive Bt)
    (h0Symm : ∀ x y, B0 x y = B0 y x)
    (h1Symm : ∀ x y, B1 x y = B1 y x)
    (ell0 ell1 ellt : ι → StrongDual ℝ H)
    (haffineA : ∀ i j,
      At i j = (1 - t) * A0 i j + t * A1 i j)
    (haffineB : ∀ x y,
      Bt x y = (1 - t) * B0 x y + t * B1 x y)
    (haffineEll : ∀ i x,
      ellt i x = (1 - t) * ell0 i x + t * ell1 i x)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (c : ι → ℝ) :
    (1 - t) *
          (c ⬝ᵥ
            (coerciveBilinearCorrectedGram A0 B0 hB0 ell0 *ᵥ c)) +
        t *
          (c ⬝ᵥ
            (coerciveBilinearCorrectedGram A1 B1 hB1 ell1 *ᵥ c)) ≤
      c ⬝ᵥ
        (coerciveBilinearCorrectedGram At Bt hBt ellt *ᵥ c) := by
  classical
  have hdefect := coerciveBilinearCorrectedGram_convex_defect
    t A0 A1 At B0 B1 Bt hB0 hB1 hBt h0Symm h1Symm
    ell0 ell1 ellt haffineA haffineB haffineEll c
  dsimp only at hdefect
  let r0 : H :=
    ∑ i, c i • coerciveRieszCorrection hB0 (ell0 i)
  let r1 : H :=
    ∑ i, c i • coerciveRieszCorrection hB1 (ell1 i)
  let rt : H :=
    ∑ i, c i • coerciveRieszCorrection hBt (ellt i)
  have hvariance0 : 0 ≤ B0 (r0 - rt) (r0 - rt) :=
    isCoercive_diagonal_nonneg B0 hB0 (r0 - rt)
  have hvariance1 : 0 ≤ B1 (r1 - rt) (r1 - rt) :=
    isCoercive_diagonal_nonneg B1 hB1 (r1 - rt)
  have hweight0 : 0 ≤ (1 - t) * B0 (r0 - rt) (r0 - rt) :=
    mul_nonneg (sub_nonneg.mpr ht1) hvariance0
  have hweight1 : 0 ≤ t * B1 (r1 - rt) (r1 - rt) :=
    mul_nonneg ht0 hvariance1
  change
    (1 - t) *
          (c ⬝ᵥ
            (coerciveBilinearCorrectedGram A0 B0 hB0 ell0 *ᵥ c)) +
        t *
          (c ⬝ᵥ
            (coerciveBilinearCorrectedGram A1 B1 hB1 ell1 *ᵥ c)) ≤
      c ⬝ᵥ
        (coerciveBilinearCorrectedGram At Bt hBt ellt *ᵥ c)
  dsimp only [r0, r1, rt] at hweight0 hweight1
  linarith

end

end ArithmeticHodge.Analysis
