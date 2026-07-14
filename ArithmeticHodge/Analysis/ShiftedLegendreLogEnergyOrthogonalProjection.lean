import ArithmeticHodge.Analysis.ShiftedLegendreFiniteEnergyGap
import ArithmeticHodge.Analysis.UnitIntervalIntegralBridge

set_option autoImplicit false

open MeasureTheory Polynomial
open scoped unitInterval

namespace ArithmeticHodge.Analysis.ShiftedLegendreLogEnergyOrthogonalProjection

open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2SpectralGap
open ShiftedLegendreLogKernel
open ShiftedLogKernelCrossEnergy
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection

noncomputable section

/-!
# Exact logarithmic orthogonality of finite Legendre projections

The shifted-Legendre partial projection is an orthogonal projection for the
singular logarithmic-difference form as well as for `L²`.  The proof expands
the residual energy and uses the polynomial logarithmic eigenvalue identity.
It is uniform in the cutoff and contains no modewise estimate.
-/

/-- The pointwise residual after subtracting a polynomial on the unit
interval. -/
def unitIntervalPolynomialResidual
    (f : unitInterval → ℝ) (p : ℝ[X]) : unitInterval → ℝ :=
  fun x ↦ f x - p.eval (x : ℝ)

private theorem integrable_polynomial_eval (p : ℝ[X]) :
    Integrable (fun x : unitInterval ↦ p.eval (x : ℝ)) := by
  exact (p.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Subtracting a polynomial preserves the logarithmic form domain. -/
theorem integrable_rawLogEnergy_polynomialResidual
    (f : unitInterval → ℝ) (hf : Integrable f)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand f))
    (p : ℝ[X]) :
    Integrable (unitIntervalRawLogEnergyIntegrand
      (unitIntervalPolynomialResidual f p)) := by
  let pf : unitInterval → ℝ := fun x ↦ p.eval (x : ℝ)
  let cross : unitInterval × unitInterval → ℝ := fun z ↦
    (f z.1 - f z.2) * unitIntervalRawPolynomialLogKernel p z
  have hpolyEnergy : Integrable
      (unitIntervalRawLogEnergyIntegrand pf) := by
    simpa only [pf] using
      integrable_unitIntervalRawLogEnergyIntegrand_polynomial p
  have hcross : Integrable cross := by
    simpa only [cross] using
      integrable_sub_mul_unitIntervalRawPolynomialLogKernel f hf p
  have hcombo : Integrable (fun z : unitInterval × unitInterval ↦
      unitIntervalRawLogEnergyIntegrand f z +
        unitIntervalRawLogEnergyIntegrand pf z - 2 * cross z) :=
    (henergy.add hpolyEnergy).sub (hcross.const_mul 2)
  apply hcombo.congr
  filter_upwards [] with z
  change
    (f z.1 - f z.2) ^ 2 / |(z.1 : ℝ) - (z.2 : ℝ)| +
          (p.eval (z.1 : ℝ) - p.eval (z.2 : ℝ)) ^ 2 /
            |(z.1 : ℝ) - (z.2 : ℝ)| -
        2 * ((f z.1 - f z.2) *
          ((p.eval (z.1 : ℝ) - p.eval (z.2 : ℝ)) /
            |(z.1 : ℝ) - (z.2 : ℝ)|)) =
      ((f z.1 - p.eval (z.1 : ℝ)) -
          (f z.2 - p.eval (z.2 : ℝ))) ^ 2 /
        |(z.1 : ℝ) - (z.2 : ℝ)|
  ring

/-- Exact Pythagorean identity in the logarithmic-difference energy.  The
single projection-pairing hypothesis is precisely the vanishing of the
low--residual logarithmic cross term. -/
theorem unitIntervalLogEnergy_eq_polynomial_add_residual
    (f : unitInterval → ℝ) (hf : Integrable f)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand f))
    (p : ℝ[X])
    (hprojection :
      (∫ x : unitInterval,
        f x * (shiftedLogKernel p).eval (x : ℝ)) =
      ∫ x : unitInterval,
        p.eval (x : ℝ) * (shiftedLogKernel p).eval (x : ℝ)) :
    unitIntervalLogEnergy f =
      (∫ x : unitInterval,
        p.eval (x : ℝ) * (shiftedLogKernel p).eval (x : ℝ)) +
      unitIntervalLogEnergy (unitIntervalPolynomialResidual f p) := by
  let pf : unitInterval → ℝ := fun x ↦ p.eval (x : ℝ)
  let cross : unitInterval × unitInterval → ℝ := fun z ↦
    (f z.1 - f z.2) * unitIntervalRawPolynomialLogKernel p z
  let residual := unitIntervalPolynomialResidual f p
  have hpolyEnergy : Integrable
      (unitIntervalRawLogEnergyIntegrand pf) := by
    simpa only [pf] using
      integrable_unitIntervalRawLogEnergyIntegrand_polynomial p
  have hcross : Integrable cross := by
    simpa only [cross] using
      integrable_sub_mul_unitIntervalRawPolynomialLogKernel f hf p
  have hresidualExpand :
      (∫ z : unitInterval × unitInterval,
        unitIntervalRawLogEnergyIntegrand residual z) =
      (∫ z : unitInterval × unitInterval,
        unitIntervalRawLogEnergyIntegrand f z) +
      (∫ z : unitInterval × unitInterval,
        unitIntervalRawLogEnergyIntegrand pf z) -
      2 * ∫ z : unitInterval × unitInterval, cross z := by
    calc
      _ = ∫ z : unitInterval × unitInterval,
          unitIntervalRawLogEnergyIntegrand f z +
            unitIntervalRawLogEnergyIntegrand pf z - 2 * cross z := by
        apply integral_congr_ae
        filter_upwards [] with z
        change
          ((f z.1 - p.eval (z.1 : ℝ)) -
              (f z.2 - p.eval (z.2 : ℝ))) ^ 2 /
              |(z.1 : ℝ) - (z.2 : ℝ)| =
            (f z.1 - f z.2) ^ 2 / |(z.1 : ℝ) - (z.2 : ℝ)| +
                (p.eval (z.1 : ℝ) - p.eval (z.2 : ℝ)) ^ 2 /
                  |(z.1 : ℝ) - (z.2 : ℝ)| -
              2 * ((f z.1 - f z.2) *
                ((p.eval (z.1 : ℝ) - p.eval (z.2 : ℝ)) /
                  |(z.1 : ℝ) - (z.2 : ℝ)|))
        ring
      _ = (∫ z : unitInterval × unitInterval,
            unitIntervalRawLogEnergyIntegrand f z +
              unitIntervalRawLogEnergyIntegrand pf z) -
          ∫ z : unitInterval × unitInterval, 2 * cross z := by
        exact integral_sub (henergy.add hpolyEnergy) (hcross.const_mul 2)
      _ = ((∫ z : unitInterval × unitInterval,
              unitIntervalRawLogEnergyIntegrand f z) +
            ∫ z : unitInterval × unitInterval,
              unitIntervalRawLogEnergyIntegrand pf z) -
          ∫ z : unitInterval × unitInterval, 2 * cross z := by
        rw [integral_add henergy hpolyEnergy]
      _ = _ := by rw [integral_const_mul]
  have hpolyIdentity :
      (∫ z : unitInterval × unitInterval,
        unitIntervalRawLogEnergyIntegrand pf z) =
      2 * ∫ x : unitInterval,
        p.eval (x : ℝ) * (shiftedLogKernel p).eval (x : ℝ) := by
    simpa only [pf] using
      integral_unitIntervalRawLogEnergyIntegrand_polynomial p
  have hcrossIdentity :
      (∫ z : unitInterval × unitInterval, cross z) =
      2 * ∫ x : unitInterval,
        f x * (shiftedLogKernel p).eval (x : ℝ) := by
    simpa only [cross] using
      integral_sub_mul_unitIntervalRawPolynomialLogKernel_eq f hf p
  unfold unitIntervalLogEnergy
  rw [hresidualExpand, hpolyIdentity, hcrossIdentity, hprojection]
  ring

/-- The logarithmic cross energy of a projection residual with the
projection polynomial vanishes exactly. -/
theorem polynomialResidual_rawLogCross_eq_zero
    (f : unitInterval → ℝ) (hf : Integrable f) (p : ℝ[X])
    (hprojection :
      (∫ x : unitInterval,
        f x * (shiftedLogKernel p).eval (x : ℝ)) =
      ∫ x : unitInterval,
        p.eval (x : ℝ) * (shiftedLogKernel p).eval (x : ℝ)) :
    (∫ z : unitInterval × unitInterval,
      (unitIntervalPolynomialResidual f p z.1 -
          unitIntervalPolynomialResidual f p z.2) *
        unitIntervalRawPolynomialLogKernel p z) = 0 := by
  have hfpoly : Integrable (unitIntervalPolynomialResidual f p) := by
    exact hf.sub (integrable_polynomial_eval p)
  rw [integral_sub_mul_unitIntervalRawPolynomialLogKernel_eq
    (unitIntervalPolynomialResidual f p) hfpoly p]
  have hpoly : Integrable (fun x : unitInterval ↦
      p.eval (x : ℝ) * (shiftedLogKernel p).eval (x : ℝ)) := by
    exact ((p.continuous.mul (shiftedLogKernel p).continuous).comp
      continuous_subtype_val).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hsplit :
      (∫ x : unitInterval,
        unitIntervalPolynomialResidual f p x *
          (shiftedLogKernel p).eval (x : ℝ)) =
      (∫ x : unitInterval,
        f x * (shiftedLogKernel p).eval (x : ℝ)) -
      ∫ x : unitInterval,
        p.eval (x : ℝ) * (shiftedLogKernel p).eval (x : ℝ) := by
    rw [← integral_sub]
    · apply integral_congr_ae
      filter_upwards [] with x
      unfold unitIntervalPolynomialResidual
      ring
    · let q : unitInterval → ℝ := fun x ↦
        (shiftedLogKernel p).eval (x : ℝ)
      have hq : Continuous q := by
        dsimp only [q]
        fun_prop
      obtain ⟨C, hC⟩ :=
        isCompact_univ.bddAbove_image hq.norm.continuousOn
      have hqBound : ∀ x : unitInterval, ‖q x‖ ≤ C := by
        intro x
        exact hC (Set.mem_image_of_mem _ (Set.mem_univ x))
      exact hf.mul_bdd hq.aestronglyMeasurable
        (Filter.Eventually.of_forall hqBound)
    · exact hpoly
  rw [hsplit, hprojection]
  ring

/-- Every shifted-Legendre partial projection is logarithmically orthogonal
to its residual, with no restriction on the cutoff. -/
theorem unitIntervalLogEnergy_eq_partialSpectral_add_residual
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval))
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand f))
    (N : ℕ) :
    unitIntervalLogEnergy f =
      shiftedLegendrePartialSpectralEnergy (hf.toLp f) N +
      unitIntervalLogEnergy
        (unitIntervalPolynomialResidual f
          (shiftedLegendrePartialProjectionPolynomial (hf.toLp f) N)) := by
  let p := shiftedLegendrePartialProjectionPolynomial (hf.toLp f) N
  have h := unitIntervalLogEnergy_eq_polynomial_add_residual
    f (hf.integrable (by norm_num)) henergy p
      (integral_mul_shiftedLogKernel_projectionPolynomial_eq_self f hf N)
  rw [integral_projectionPolynomial_mul_shiftedLogKernel_eq_partialSpectralEnergy]
    at h
  simpa only [p] using h

/-- The corresponding partial-projection residual cross term is exactly
zero. -/
theorem partialProjectionResidual_rawLogCross_eq_zero
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval))
    (N : ℕ) :
    let p := shiftedLegendrePartialProjectionPolynomial (hf.toLp f) N
    (∫ z : unitInterval × unitInterval,
      (unitIntervalPolynomialResidual f p z.1 -
          unitIntervalPolynomialResidual f p z.2) *
        unitIntervalRawPolynomialLogKernel p z) = 0 := by
  dsimp only
  exact polynomialResidual_rawLogCross_eq_zero
    f (hf.integrable (by norm_num)) _
      (integral_mul_shiftedLogKernel_projectionPolynomial_eq_self f hf N)

/-! ## Exact affine transport to the centered endpoint interval -/

/-- A unit-interval polynomial transported to the centered interval. -/
def centeredPolynomialLift (p : ℝ[X]) : ℝ → ℝ :=
  fun x ↦ p.eval ((x + 1) / 2)

/-- The centered residual after subtracting a transported polynomial. -/
def centeredPolynomialResidual (w : ℝ → ℝ) (p : ℝ[X]) : ℝ → ℝ :=
  fun x ↦ w x - centeredPolynomialLift p x

@[simp]
theorem centeredPullback_centeredPolynomialLift
    (p : ℝ[X]) (t : ℝ) :
    centeredPullback (centeredPolynomialLift p) t = p.eval t := by
  unfold centeredPullback centeredPolynomialLift
  congr 1
  ring

theorem centeredPullback_centeredPolynomialResidual
    (w : ℝ → ℝ) (p : ℝ[X]) (t : unitInterval) :
    centeredPullback (centeredPolynomialResidual w p) (t : ℝ) =
      unitIntervalPolynomialResidual
        (fun s : unitInterval ↦ centeredPullback w (s : ℝ)) p t := by
  change
    w (2 * (t : ℝ) - 1) -
        p.eval (((2 * (t : ℝ) - 1) + 1) / 2) =
      w (2 * (t : ℝ) - 1) - p.eval (t : ℝ)
  rw [show ((2 * (t : ℝ) - 1) + 1) / 2 = (t : ℝ) by ring]

/-- Exact centered Pythagorean identity for any polynomial satisfying the
logarithmic projection pairing.  The factor four is the affine Jacobian and
kernel scaling from `[0,1]` to `[-1,1]`. -/
theorem centeredRawLogEnergy_eq_polynomial_add_residual
    (w : ℝ → ℝ) (p : ℝ[X])
    (hf : Integrable
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ)))
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hprojection :
      (∫ t : unitInterval,
        centeredPullback w (t : ℝ) *
          (shiftedLogKernel p).eval (t : ℝ)) =
      ∫ t : unitInterval,
        p.eval (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ)) :
    centeredRawLogEnergy w =
      4 * (∫ t : unitInterval,
        p.eval (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ)) +
      centeredRawLogEnergy (centeredPolynomialResidual w p) := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  have hunit := unitIntervalLogEnergy_eq_polynomial_add_residual
    f hf henergy p (by simpa only [f] using hprojection)
  have hresEnergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (unitIntervalPolynomialResidual f p)) :=
    integrable_rawLogEnergy_polynomialResidual f hf henergy p
  have hresEq : unitIntervalPolynomialResidual f p =
      fun t : unitInterval ↦
        centeredPullback (centeredPolynomialResidual w p) (t : ℝ) := by
    funext t
    exact (centeredPullback_centeredPolynomialResidual w p t).symm
  rw [hresEq] at hunit hresEnergy
  have hwBridge := unitIntervalLogEnergy_centeredPullback w henergy
  have hresBridge := unitIntervalLogEnergy_centeredPullback
    (centeredPolynomialResidual w p) hresEnergy
  dsimp only [f] at hunit
  rw [hwBridge, hresBridge] at hunit
  linarith

/-- The canonical finite shifted-Legendre projection splits the centered raw
energy into its exact finite spectral energy and an orthogonal centered
residual, uniformly in the cutoff. -/
theorem centeredRawLogEnergy_eq_partialSpectral_add_residual
    (w : ℝ → ℝ)
    (hf : MemLp
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (N : ℕ) :
    let p := shiftedLegendrePartialProjectionPolynomial
      (hf.toLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ))) N
    centeredRawLogEnergy w =
      4 * shiftedLegendrePartialSpectralEnergy
        (hf.toLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ))) N +
      centeredRawLogEnergy (centeredPolynomialResidual w p) := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  let p := shiftedLegendrePartialProjectionPolynomial (hf.toLp f) N
  have h := centeredRawLogEnergy_eq_polynomial_add_residual
    w p (hf.integrable (by norm_num)) henergy
      (by
        dsimp only [f, p]
        exact integral_mul_shiftedLogKernel_projectionPolynomial_eq_self
          (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) hf N)
  rw [integral_projectionPolynomial_mul_shiftedLogKernel_eq_partialSpectralEnergy]
    at h
  simpa only [f, p] using h

end

end ArithmeticHodge.Analysis.ShiftedLegendreLogEnergyOrthogonalProjection
