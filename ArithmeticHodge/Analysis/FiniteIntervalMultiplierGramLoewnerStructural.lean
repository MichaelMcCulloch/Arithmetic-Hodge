import ArithmeticHodge.Analysis.FiniteIntervalWeightedGramTraceInteriorStructural

set_option autoImplicit false

open Matrix MeasureTheory Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.FiniteIntervalMultiplierGramLoewnerStructural

open FiniteIntervalWeightedGramTraceStructural

noncomputable section

/-!
# Loewner comparison for finite interval multiplier Grams

Pointwise comparison of two scalar multipliers compares the complete finite
Gram matrices.  Testing against an arbitrary synthesized row preserves every
matrix direction, unlike a trace-to-identity estimate.
-/

/-- Gram of a finite real row family against a scalar interval multiplier. -/
def finiteIntervalMultiplierGram
    {ι : Type*} (a b : ℝ) (M : ℝ → ℝ) (F : ι → ℝ → ℝ) :
    Matrix ι ι ℝ := fun i j ↦
  ∫ x : ℝ in a..b, M x * F i x * F j x

/-- A finite multiplier Gram is Hermitian over the real scalars. -/
theorem finiteIntervalMultiplierGram_isHermitian
    {ι : Type*} (a b : ℝ) (M : ℝ → ℝ) (F : ι → ℝ → ℝ) :
    (finiteIntervalMultiplierGram a b M F).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change (∫ x : ℝ in a..b, M x * F j x * F i x) =
    ∫ x : ℝ in a..b, M x * F i x * F j x
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

/-- The quadratic form of a multiplier Gram is the multiplier-weighted square
of the synthesized row. -/
theorem finiteIntervalMultiplierGram_quadratic
    {ι : Type*} [Fintype ι]
    (a b : ℝ) (M : ℝ → ℝ) (F : ι → ℝ → ℝ)
    (hInt : ∀ i j, IntervalIntegrable
      (fun x ↦ M x * F i x * F j x) volume a b)
    (c : ι → ℝ) :
    star c ⬝ᵥ (finiteIntervalMultiplierGram a b M F *ᵥ c) =
      ∫ x : ℝ in a..b, M x * (∑ i, c i * F i x) ^ 2 := by
  classical
  rw [show (fun x : ℝ ↦ M x * (∑ i, c i * F i x) ^ 2) =
      fun x ↦ ∑ i, ∑ j,
        (c i * c j) * (M x * F i x * F j x) by
    funext x
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  rw [intervalIntegral.integral_finset_sum]
  · simp only [dotProduct, mulVec, finiteIntervalMultiplierGram,
      star_trivial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j _hj
      rw [intervalIntegral.integral_const_mul]
      ring
    · intro j _hj
      exact (hInt i j).const_mul (c i * c j)
  · intro i _hi
    have hsum := IntervalIntegrable.sum Finset.univ fun j _hj ↦
      (hInt i j).const_mul (c i * c j)
    convert hsum using 1
    funext x
    simp only [Finset.sum_apply]

/-- Pairwise integrability implies integrability of every synthesized
multiplier-weighted square. -/
theorem intervalIntegrable_multiplier_mul_synthesis_sq
    {ι : Type*} [Fintype ι]
    (a b : ℝ) (M : ℝ → ℝ) (F : ι → ℝ → ℝ)
    (hInt : ∀ i j, IntervalIntegrable
      (fun x ↦ M x * F i x * F j x) volume a b)
    (c : ι → ℝ) :
    IntervalIntegrable
      (fun x ↦ M x * (∑ i, c i * F i x) ^ 2) volume a b := by
  classical
  have hsum := IntervalIntegrable.sum Finset.univ fun i _hi ↦
    IntervalIntegrable.sum Finset.univ fun j _hj ↦
      (hInt i j).const_mul (c i * c j)
  convert hsum using 1
  funext x
  simp only [Finset.sum_apply, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Interior pointwise domination of multipliers gives a Loewner comparison
of their complete finite interval Grams. -/
theorem finiteIntervalMultiplierGram_sub_posSemidef_of_le_Ioo
    {ι : Type*} [Fintype ι]
    (a b : ℝ) (hab : a ≤ b)
    (M₀ M₁ : ℝ → ℝ) (F : ι → ℝ → ℝ)
    (hInt₀ : ∀ i j, IntervalIntegrable
      (fun x ↦ M₀ x * F i x * F j x) volume a b)
    (hInt₁ : ∀ i j, IntervalIntegrable
      (fun x ↦ M₁ x * F i x * F j x) volume a b)
    (hPoint : ∀ x ∈ Ioo a b, M₀ x ≤ M₁ x) :
    (finiteIntervalMultiplierGram a b M₁ F -
      finiteIntervalMultiplierGram a b M₀ F).PosSemidef := by
  have hHermitian :
      (finiteIntervalMultiplierGram a b M₁ F -
        finiteIntervalMultiplierGram a b M₀ F).IsHermitian :=
    (finiteIntervalMultiplierGram_isHermitian a b M₁ F).sub
      (finiteIntervalMultiplierGram_isHermitian a b M₀ F)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHermitian
  intro c
  have hmono :
      (∫ x : ℝ in a..b, M₀ x * (∑ i, c i * F i x) ^ 2) ≤
        ∫ x : ℝ in a..b, M₁ x * (∑ i, c i * F i x) ^ 2 := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hab
    · exact intervalIntegrable_multiplier_mul_synthesis_sq
        a b M₀ F hInt₀ c
    · exact intervalIntegrable_multiplier_mul_synthesis_sq
        a b M₁ F hInt₁ c
    · intro x hx
      exact mul_le_mul_of_nonneg_right (hPoint x hx) (sq_nonneg _)
  rw [sub_mulVec, dotProduct_sub,
    finiteIntervalMultiplierGram_quadratic a b M₁ F hInt₁ c,
    finiteIntervalMultiplierGram_quadratic a b M₀ F hInt₀ c]
  exact sub_nonneg.mpr hmono

/-- A weighted interval Gram is the multiplier Gram for the reciprocal
weight. -/
theorem finiteIntervalWeightedGram_eq_multiplierGram_inv
    {ι : Type*} (a b : ℝ) (W : ℝ → ℝ) (F : ι → ℝ → ℝ) :
    finiteIntervalWeightedGram a b W F =
      finiteIntervalMultiplierGram a b (fun x ↦ (W x)⁻¹) F := by
  ext i j
  unfold finiteIntervalWeightedGram finiteIntervalMultiplierGram
  apply intervalIntegral.integral_congr
  intro x _hx
  change F i x * F j x / W x = (W x)⁻¹ * F i x * F j x
  rw [div_eq_mul_inv]
  ring

/-- A pointwise reciprocal majorant gives a full-matrix Loewner upper
certificate for a weighted interval Gram. -/
theorem finiteIntervalMultiplierGram_sub_weightedGram_posSemidef_of_inv_le_Ioo
    {ι : Type*} [Fintype ι]
    (a b : ℝ) (hab : a ≤ b)
    (W U : ℝ → ℝ) (F : ι → ℝ → ℝ)
    (hWeightedInt : ∀ i j, IntervalIntegrable
      (fun x ↦ F i x * F j x / W x) volume a b)
    (hUpperInt : ∀ i j, IntervalIntegrable
      (fun x ↦ U x * F i x * F j x) volume a b)
    (hPoint : ∀ x ∈ Ioo a b, (W x)⁻¹ ≤ U x) :
    (finiteIntervalMultiplierGram a b U F -
      finiteIntervalWeightedGram a b W F).PosSemidef := by
  rw [finiteIntervalWeightedGram_eq_multiplierGram_inv]
  apply finiteIntervalMultiplierGram_sub_posSemidef_of_le_Ioo
    a b hab (fun x ↦ (W x)⁻¹) U F
  · intro i j
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hWeightedInt i j
  · exact hUpperInt
  · exact hPoint

end

end ArithmeticHodge.Analysis.FiniteIntervalMultiplierGramLoewnerStructural
