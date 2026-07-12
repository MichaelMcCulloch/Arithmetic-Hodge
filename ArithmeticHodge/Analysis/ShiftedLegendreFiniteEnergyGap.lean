import ArithmeticHodge.Analysis.ShiftedLegendreL2SpectralGap
import ArithmeticHodge.Analysis.UnitIntervalLogEnergyProjection

set_option autoImplicit false

open Finset MeasureTheory Polynomial
open scoped BigOperators InnerProductSpace unitInterval

namespace ArithmeticHodge.Analysis.ShiftedLegendreFiniteEnergyGap

open ShiftedLegendreL2Basis
open ShiftedLegendreL2SpectralGap
open ShiftedLegendreLogEigen
open ShiftedLegendreLogKernel
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyProjection

noncomputable section

/-!
# Finite shifted-Legendre projections in the raw logarithmic form

Each finite Hilbert projection has an explicit polynomial representative.
The exact polynomial logarithmic spectrum then identifies its raw pairing
with the corresponding finite Hilbert spectral energy.  Residual positivity
and convergence of the Hilbert projections give the full finite-energy gap.
-/

/-- The polynomial representative of the normalized `n`th shifted-Legendre
`L²` basis vector. -/
def normalizedShiftedLegendrePolynomial (n : ℕ) : ℝ[X] :=
  ‖shiftedLegendreL2 n‖⁻¹ • shiftedLegendreReal n

/-- The polynomial representative of the finite Hilbert projection through
indices `< N`. -/
def shiftedLegendrePartialProjectionPolynomial
    (F : UnitIntervalL2) (N : ℕ) : ℝ[X] :=
  ∑ n ∈ Finset.range N,
    shiftedLegendreHilbertBasis.repr F n •
      normalizedShiftedLegendrePolynomial n

/-- The logarithmically weighted finite Hilbert projection. -/
def shiftedLegendrePartialLogProjection
    (F : UnitIntervalL2) (N : ℕ) : UnitIntervalL2 :=
  ∑ n ∈ Finset.range N,
    ((2 * (harmonic n : ℝ)) *
      shiftedLegendreHilbertBasis.repr F n) •
        shiftedLegendreHilbertBasis n

@[simp]
theorem polynomialToL2_normalizedShiftedLegendrePolynomial (n : ℕ) :
    polynomialToL2 (normalizedShiftedLegendrePolynomial n) =
      shiftedLegendreHilbertBasis n := by
  rw [normalizedShiftedLegendrePolynomial, LinearMap.map_smul,
    shiftedLegendreHilbertBasis_apply, normalizedShiftedLegendreL2,
    shiftedLegendreL2]

/-- The finite projection polynomial represents exactly the finite Hilbert
projection in `L²`. -/
theorem polynomialToL2_shiftedLegendrePartialProjectionPolynomial
    (F : UnitIntervalL2) (N : ℕ) :
    polynomialToL2 (shiftedLegendrePartialProjectionPolynomial F N) =
      shiftedLegendrePartialProjection F N := by
  simp [shiftedLegendrePartialProjectionPolynomial,
    shiftedLegendrePartialProjection]

/-- Normalization commutes with the exact shifted-Legendre logarithmic
eigenvalue identity. -/
theorem shiftedLogKernel_normalizedShiftedLegendrePolynomial (n : ℕ) :
    shiftedLogKernel (normalizedShiftedLegendrePolynomial n) =
      (2 * (harmonic n : ℝ)) •
        normalizedShiftedLegendrePolynomial n := by
  rw [normalizedShiftedLegendrePolynomial, LinearMap.map_smul,
    shiftedLogKernel_shiftedLegendreReal]
  simp only [Polynomial.smul_eq_C_mul]
  ring

/-- The logarithmic operator maps the finite projection polynomial by the
exact harmonic weights. -/
theorem shiftedLogKernel_shiftedLegendrePartialProjectionPolynomial
    (F : UnitIntervalL2) (N : ℕ) :
    shiftedLogKernel (shiftedLegendrePartialProjectionPolynomial F N) =
      ∑ n ∈ Finset.range N,
        ((2 * (harmonic n : ℝ)) *
          shiftedLegendreHilbertBasis.repr F n) •
            normalizedShiftedLegendrePolynomial n := by
  simp [shiftedLegendrePartialProjectionPolynomial,
    shiftedLogKernel_normalizedShiftedLegendrePolynomial,
    smul_smul, mul_comm]

/-- After passing to `L²`, the logarithmic image is the weighted finite
Hilbert projection. -/
theorem polynomialToL2_shiftedLogKernel_partialProjectionPolynomial
    (F : UnitIntervalL2) (N : ℕ) :
    polynomialToL2
        (shiftedLogKernel
          (shiftedLegendrePartialProjectionPolynomial F N)) =
      shiftedLegendrePartialLogProjection F N := by
  rw [shiftedLogKernel_shiftedLegendrePartialProjectionPolynomial]
  simp [shiftedLegendrePartialLogProjection]

/-- Pairing an `L²` representative with a polynomial is its real Hilbert
inner product with the polynomial's `L²` class. -/
theorem integral_mul_polynomial_eq_inner
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval))
    (q : ℝ[X]) :
    (∫ x : unitInterval, f x * q.eval (x : ℝ)) =
      inner ℝ (hf.toLp f) (polynomialToL2 q) := by
  rw [MeasureTheory.L2.inner_def]
  have hf_ae := hf.coeFn_toLp
  have hq_ae := ContinuousMap.coeFn_toLp
    (p := (2 : ENNReal)) (μ := (volume : Measure unitInterval))
      (𝕜 := ℝ) (polynomialToContinuous q)
  apply integral_congr_ae
  filter_upwards [hf_ae, hq_ae] with x hfx hqx
  change f x * q.eval (x : ℝ) =
    inner ℝ ((hf.toLp f : unitInterval → ℝ) x)
      ((polynomialToL2 q : unitInterval → ℝ) x)
  rw [hfx]
  change f x * q.eval (x : ℝ) =
    inner ℝ (f x)
      ((ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ
        (polynomialToContinuous q) : unitInterval → ℝ) x)
  rw [hqx]
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
  simp only [RCLike.re_to_real, starRingEnd_apply, star_trivial]
  rw [polynomialToContinuous_apply]
  ring

/-- Polynomial pairing on the unit interval is the corresponding `L²`
inner product. -/
theorem integral_polynomial_mul_eq_inner (p q : ℝ[X]) :
    (∫ x : unitInterval, p.eval (x : ℝ) * q.eval (x : ℝ)) =
      inner ℝ (polynomialToL2 p) (polynomialToL2 q) := by
  have hinner := MeasureTheory.ContinuousMap.inner_toLp
    (𝕜 := ℝ) (volume : Measure unitInterval)
    (polynomialToContinuous p) (polynomialToContinuous q)
  change inner ℝ (polynomialToL2 p) (polynomialToL2 q) =
    ∫ x : unitInterval, q.eval (x : ℝ) * p.eval (x : ℝ) at hinner
  calc
    _ = ∫ x : unitInterval, q.eval (x : ℝ) * p.eval (x : ℝ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := hinner.symm

/-- Pairing an arbitrary `L²` vector with the weighted finite projection
is exactly the finite shifted-Legendre spectral energy. -/
theorem inner_partialLogProjection_eq_partialSpectralEnergy
    (F : UnitIntervalL2) (N : ℕ) :
    inner ℝ F (shiftedLegendrePartialLogProjection F N) =
      shiftedLegendrePartialSpectralEnergy F N := by
  have hcoeff : ∀ n : ℕ,
      inner ℝ F (shiftedLegendreHilbertBasis n) =
        shiftedLegendreHilbertBasis.repr F n := by
    intro n
    rw [real_inner_comm]
    exact (shiftedLegendreHilbertBasis.repr_apply_apply F n).symm
  rw [shiftedLegendrePartialLogProjection, inner_sum,
    shiftedLegendrePartialSpectralEnergy]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [real_inner_smul_right, hcoeff]
  ring

/-- The logarithmic self-pairing of the finite projection polynomial is
exactly its finite Hilbert spectral energy. -/
theorem integral_projectionPolynomial_mul_shiftedLogKernel_eq_partialSpectralEnergy
    (F : UnitIntervalL2) (N : ℕ) :
    (∫ x : unitInterval,
      (shiftedLegendrePartialProjectionPolynomial F N).eval (x : ℝ) *
        (shiftedLogKernel
          (shiftedLegendrePartialProjectionPolynomial F N)).eval (x : ℝ)) =
      shiftedLegendrePartialSpectralEnergy F N := by
  rw [integral_polynomial_mul_eq_inner,
    polynomialToL2_shiftedLegendrePartialProjectionPolynomial,
    polynomialToL2_shiftedLogKernel_partialProjectionPolynomial]
  have hinner := shiftedLegendreHilbertBasis.orthonormal.inner_sum
    (fun n ↦ shiftedLegendreHilbertBasis.repr F n)
    (fun n ↦ (2 * (harmonic n : ℝ)) *
      shiftedLegendreHilbertBasis.repr F n)
    (Finset.range N)
  rw [shiftedLegendrePartialProjection,
    shiftedLegendrePartialLogProjection,
    shiftedLegendrePartialSpectralEnergy]
  calc
    _ = ∑ n ∈ Finset.range N,
        shiftedLegendreHilbertBasis.repr F n *
          ((2 * (harmonic n : ℝ)) *
            shiftedLegendreHilbertBasis.repr F n) := by
      simpa only [RCLike.star_def, RCLike.conj_to_real,
        map_id, id_eq] using hinner
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _hn
      ring

/-- Pairing `f` against the logarithmic image of its finite projection
polynomial gives the same finite spectral energy. -/
theorem integral_mul_shiftedLogKernel_projectionPolynomial_eq_partialSpectralEnergy
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval))
    (N : ℕ) :
    (∫ x : unitInterval,
      f x *
        (shiftedLogKernel
          (shiftedLegendrePartialProjectionPolynomial (hf.toLp f) N)).eval
            (x : ℝ)) =
      shiftedLegendrePartialSpectralEnergy (hf.toLp f) N := by
  rw [integral_mul_polynomial_eq_inner,
    polynomialToL2_shiftedLogKernel_partialProjectionPolynomial,
    inner_partialLogProjection_eq_partialSpectralEnergy]

/-- The finite projection polynomial satisfies the exact projection pairing
required by residual positivity. -/
theorem integral_mul_shiftedLogKernel_projectionPolynomial_eq_self
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval))
    (N : ℕ) :
    (∫ x : unitInterval,
      f x *
        (shiftedLogKernel
          (shiftedLegendrePartialProjectionPolynomial (hf.toLp f) N)).eval
            (x : ℝ)) =
      ∫ x : unitInterval,
        (shiftedLegendrePartialProjectionPolynomial (hf.toLp f) N).eval
            (x : ℝ) *
          (shiftedLogKernel
            (shiftedLegendrePartialProjectionPolynomial (hf.toLp f) N)).eval
              (x : ℝ) := by
  rw [integral_mul_shiftedLogKernel_projectionPolynomial_eq_partialSpectralEnergy,
    integral_projectionPolynomial_mul_shiftedLogKernel_eq_partialSpectralEnergy]

/-- Every finite shifted-Legendre spectral energy is bounded by the
normalized unit-interval logarithmic energy. -/
theorem partialSpectralEnergy_le_unitIntervalLogEnergy
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval))
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand f))
    (N : ℕ) :
    shiftedLegendrePartialSpectralEnergy (hf.toLp f) N ≤
      unitIntervalLogEnergy f := by
  let p := shiftedLegendrePartialProjectionPolynomial (hf.toLp f) N
  rw [← integral_projectionPolynomial_mul_shiftedLogKernel_eq_partialSpectralEnergy
    (hf.toLp f) N]
  exact polynomial_pairing_le_unitIntervalLogEnergy f
    (hf.integrable (by norm_num)) henergy p
      (by
        dsimp only [p]
        exact integral_mul_shiftedLogKernel_projectionPolynomial_eq_self
          f hf N)

/-- The normalized unit-interval logarithmic energy controls twice the full `L²` norm
once the constant shifted-Legendre coefficient vanishes. -/
theorem two_mul_norm_sq_le_unitIntervalLogEnergy
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval))
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand f))
    (hzero : shiftedLegendreHilbertBasis.repr (hf.toLp f) 0 = 0) :
    2 * ‖hf.toLp f‖ ^ 2 ≤ unitIntervalLogEnergy f := by
  exact two_mul_norm_sq_le_of_partialSpectralEnergy_le
    (hf.toLp f) hzero (unitIntervalLogEnergy f)
      (partialSpectralEnergy_le_unitIntervalLogEnergy f hf henergy)

/-- The zeroth Hilbert coefficient is the mean, up to the nonzero
normalizing scalar of the constant shifted-Legendre polynomial. -/
theorem shiftedLegendreHilbertBasis_repr_zero_eq
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval)) :
    shiftedLegendreHilbertBasis.repr (hf.toLp f) 0 =
      ‖shiftedLegendreL2 0‖⁻¹ * ∫ x : unitInterval, f x := by
  rw [shiftedLegendreHilbertBasis.repr_apply_apply,
    shiftedLegendreHilbertBasis_apply, normalizedShiftedLegendreL2,
    real_inner_smul_left, real_inner_comm, shiftedLegendreL2,
    ← integral_mul_polynomial_eq_inner f hf]
  simp [shiftedLegendreReal, Polynomial.shiftedLegendre]

/-- A zero integral removes the constant shifted-Legendre Hilbert mode. -/
theorem shiftedLegendreHilbertBasis_repr_zero_eq_zero_of_integral_eq_zero
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval))
    (hmean : (∫ x : unitInterval, f x) = 0) :
    shiftedLegendreHilbertBasis.repr (hf.toLp f) 0 = 0 := by
  rw [shiftedLegendreHilbertBasis_repr_zero_eq f hf, hmean, mul_zero]

/-- The abstract `L²` norm-square of a chosen representative is its
pointwise square integral. -/
theorem norm_sq_toLp_eq_integral_sq
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval)) :
    ‖hf.toLp f‖ ^ 2 = ∫ x : unitInterval, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_eq_re_inner ℝ, RCLike.inner_apply]
  simp only [RCLike.re_to_real, starRingEnd_apply, star_trivial]
  ring

/-- Mean-zero finite-energy functions satisfy the normalized unit-interval
logarithmic spectral gap in pointwise integral form. -/
theorem two_mul_integral_sq_le_unitIntervalLogEnergy
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval))
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand f))
    (hmean : (∫ x : unitInterval, f x) = 0) :
    2 * (∫ x : unitInterval, f x ^ 2) ≤ unitIntervalLogEnergy f := by
  rw [← norm_sq_toLp_eq_integral_sq f hf]
  exact two_mul_norm_sq_le_unitIntervalLogEnergy f hf henergy
    (shiftedLegendreHilbertBasis_repr_zero_eq_zero_of_integral_eq_zero
      f hf hmean)

end

end ArithmeticHodge.Analysis.ShiftedLegendreFiniteEnergyGap
