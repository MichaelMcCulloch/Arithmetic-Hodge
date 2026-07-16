import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDirectionalTail
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLowSchur

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointTailBilinearContinuityStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointScaledCorrelation
open YoshidaEvenHomogeneousCoercivity
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseEvenSchurClosure
open YoshidaFactorTwoPhaseEvenSymmetricBound
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddSymmetricBound
open YoshidaFactorTwoPhaseRadiusClosure
open YoshidaOddSpectralMassBridge
open YoshidaWeightedTailBounds

/-!
# Structural continuity of the same-parity endpoint-tail perturbations

The diagonal symmetric perturbation has spectral interval `[-3, 1]` on the
even sector and `[-1, 3 / 2]` on the odd sector.  Comparing the diagonal
estimates on `r • u + s • v` and `r • u - s • v` cancels both diagonal
perturbations and the ordinary-mass cross term.  The remaining scalar pencil
gives the sharp operator-radius bounds `3` and `3 / 2` by its determinant.

No Fourier-mode enumeration enters this argument.
-/

/-- A scalar pencil formulation of the off-diagonal operator bound. -/
theorem offDiagonal_sq_le_of_two_mul_le_scaled_diagonal
    (Eu Ev B K : ℝ)
    (hscaled : ∀ r s : ℝ,
      2 * B * r * s ≤ K * (Eu * r ^ 2 + Ev * s ^ 2)) :
    B ^ 2 ≤ K ^ 2 * Eu * Ev := by
  have hquad : ∀ r s : ℝ,
      0 ≤ (K * Eu) * r ^ 2 + 2 * (-B) * r * s +
        (K * Ev) * s ^ 2 := by
    intro r s
    calc
      0 ≤ K * (Eu * r ^ 2 + Ev * s ^ 2) - 2 * B * r * s :=
        sub_nonneg.mpr (hscaled r s)
      _ = (K * Eu) * r ^ 2 + 2 * (-B) * r * s +
          (K * Ev) * s ^ 2 := by ring
  have hdet :=
    (real_quadratic_pencil_nonneg_iff (K * Eu) (K * Ev) (-B)).mp hquad
  calc
    B ^ 2 = (-B) ^ 2 := by ring
    _ ≤ (K * Eu) * (K * Ev) := hdet.2.2
    _ = K ^ 2 * Eu * Ev := by ring

private theorem endpointL2Energy_smul_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (r s : ℝ) :
    (∫ x : ℝ in -1..1, (r • u + s • v) x ^ 2) =
      r ^ 2 * (∫ x : ℝ in -1..1, u x ^ 2) +
        2 * r * s * (∫ x : ℝ in -1..1, u x * v x) +
        s ^ 2 * (∫ x : ℝ in -1..1, v x ^ 2) := by
  have huu : IntervalIntegrable (fun x : ℝ ↦ u x ^ 2)
      volume (-1) 1 := (hu.pow 2).intervalIntegrable (-1) 1
  have huv : IntervalIntegrable (fun x : ℝ ↦ u x * v x)
      volume (-1) 1 := (hu.mul hv).intervalIntegrable (-1) 1
  have hvv : IntervalIntegrable (fun x : ℝ ↦ v x ^ 2)
      volume (-1) 1 := (hv.pow 2).intervalIntegrable (-1) 1
  rw [show (fun x : ℝ ↦ (r • u + s • v) x ^ 2) =
      fun x ↦ r ^ 2 * u x ^ 2 +
        ((2 * r * s) * (u x * v x) + s ^ 2 * v x ^ 2) by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring,
    intervalIntegral.integral_add (huu.const_mul (r ^ 2))
      ((huv.const_mul (2 * r * s)).add (hvv.const_mul (s ^ 2))),
    intervalIntegral.integral_add (huv.const_mul (2 * r * s))
      (hvv.const_mul (s ^ 2)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

private theorem symmetricPerturbation_smul_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (r s : ℝ) :
    factorTwoCenteredSymmetricPerturbation (r • u + s • v) =
      r ^ 2 * factorTwoCenteredSymmetricPerturbation u +
        2 * r * s *
          factorTwoCenteredSymmetricPerturbationBilinear u v +
        s ^ 2 * factorTwoCenteredSymmetricPerturbation v := by
  rw [factorTwoCenteredSymmetricPerturbation_add_eq_bilinear
      (r • u) (s • v) (hu.const_smul r) (hv.const_smul s),
    factorTwoCenteredSymmetricPerturbation_smul,
    factorTwoCenteredSymmetricPerturbation_smul,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_smul]
  ring

/-- The polarized symmetric perturbation has operator radius at most `3` on
the continuous even sector.  This is the structural polarization of the
existing diagonal spectral interval `[-3, 1]`. -/
theorem factorTwoCenteredSymmetricPerturbationBilinear_sq_le_even_energy_mul
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (huEven : Function.Even u) (hvEven : Function.Even v) :
    factorTwoCenteredSymmetricPerturbationBilinear u v ^ 2 ≤
      9 * (∫ x : ℝ in -1..1, u x ^ 2) *
        (∫ x : ℝ in -1..1, v x ^ 2) := by
  let Eu : ℝ := ∫ x : ℝ in -1..1, u x ^ 2
  let Ev : ℝ := ∫ x : ℝ in -1..1, v x ^ 2
  let B : ℝ := factorTwoCenteredSymmetricPerturbationBilinear u v
  have hscaled : ∀ r s : ℝ,
      2 * B * r * s ≤ (3 : ℝ) * (Eu * r ^ 2 + Ev * s ^ 2) := by
    intro r s
    have hplusEven : Function.Even (r • u + s • v) := by
      intro x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [huEven x, hvEven x]
    have hminusEven : Function.Even (r • u + (-s) • v) := by
      intro x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [huEven x, hvEven x]
    have hplusEnergy :
        0 ≤ ∫ x : ℝ in -1..1, (r • u + s • v) x ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num)
        (fun x _hx ↦ sq_nonneg ((r • u + s • v) x))
    have hplusUpper0 := even_symmetricPerturbation_le_energy
      (r • u + s • v) ((hu.const_smul r).add (hv.const_smul s))
      hplusEven
    have hplusUpper :
        factorTwoCenteredSymmetricPerturbation (r • u + s • v) ≤
          (3 : ℝ) *
            (∫ x : ℝ in -1..1, (r • u + s • v) x ^ 2) := by
      nlinarith
    have hminusLower0 := neg_three_energy_le_even_symmetricPerturbation
      (r • u + (-s) • v)
      ((hu.const_smul r).add (hv.const_smul (-s))) hminusEven
    have hminusLower :
        -factorTwoCenteredSymmetricPerturbation (r • u + (-s) • v) ≤
          (3 : ℝ) *
            (∫ x : ℝ in -1..1, (r • u + (-s) • v) x ^ 2) := by
      nlinarith
    have hPplus := symmetricPerturbation_smul_add u v hu hv r s
    have hPminus := symmetricPerturbation_smul_add u v hu hv r (-s)
    have hEplus := endpointL2Energy_smul_add u v hu hv r s
    have hEminus := endpointL2Energy_smul_add u v hu hv r (-s)
    rw [hPplus, hEplus] at hplusUpper
    rw [hPminus, hEminus] at hminusLower
    dsimp only [Eu, Ev, B]
    nlinarith
  have hdet := offDiagonal_sq_le_of_two_mul_le_scaled_diagonal
    Eu Ev B 3 hscaled
  norm_num at hdet
  simpa only [Eu, Ev, B] using hdet

/-- The polarized symmetric perturbation has operator radius at most `3 / 2`
on the continuous odd sector.  This is the structural polarization of the
existing diagonal spectral interval `[-1, 3 / 2]`. -/
theorem factorTwoCenteredSymmetricPerturbationBilinear_sq_le_odd_energy_mul
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (huOdd : Function.Odd u) (hvOdd : Function.Odd v) :
    factorTwoCenteredSymmetricPerturbationBilinear u v ^ 2 ≤
      (9 / 4 : ℝ) * (∫ x : ℝ in -1..1, u x ^ 2) *
        (∫ x : ℝ in -1..1, v x ^ 2) := by
  let Eu : ℝ := ∫ x : ℝ in -1..1, u x ^ 2
  let Ev : ℝ := ∫ x : ℝ in -1..1, v x ^ 2
  let B : ℝ := factorTwoCenteredSymmetricPerturbationBilinear u v
  have hscaled : ∀ r s : ℝ,
      2 * B * r * s ≤ (3 / 2 : ℝ) * (Eu * r ^ 2 + Ev * s ^ 2) := by
    intro r s
    have hplusOdd : Function.Odd (r • u + s • v) := by
      intro x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [huOdd x, hvOdd x]
      ring
    have hminusOdd : Function.Odd (r • u + (-s) • v) := by
      intro x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [huOdd x, hvOdd x]
      ring
    have hminusEnergy :
        0 ≤ ∫ x : ℝ in -1..1, (r • u + (-s) • v) x ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num)
        (fun x _hx ↦ sq_nonneg ((r • u + (-s) • v) x))
    have hplusUpper := odd_symmetricPerturbation_le_three_halves_energy
      (r • u + s • v) ((hu.const_smul r).add (hv.const_smul s))
      hplusOdd
    have hminusLower0 := neg_energy_le_odd_symmetricPerturbation
      (r • u + (-s) • v)
      ((hu.const_smul r).add (hv.const_smul (-s))) hminusOdd
    have hminusLower :
        -factorTwoCenteredSymmetricPerturbation (r • u + (-s) • v) ≤
          (3 / 2 : ℝ) *
            (∫ x : ℝ in -1..1, (r • u + (-s) • v) x ^ 2) := by
      nlinarith
    have hPplus := symmetricPerturbation_smul_add u v hu hv r s
    have hPminus := symmetricPerturbation_smul_add u v hu hv r (-s)
    have hEplus := endpointL2Energy_smul_add u v hu hv r s
    have hEminus := endpointL2Energy_smul_add u v hu hv r (-s)
    rw [hPplus, hEplus] at hplusUpper
    rw [hPminus, hEminus] at hminusLower
    dsimp only [Eu, Ev, B]
    nlinarith
  have hdet := offDiagonal_sq_le_of_two_mul_le_scaled_diagonal
    Eu Ev B (3 / 2) hscaled
  norm_num at hdet
  simpa only [Eu, Ev, B] using hdet

/-- The even operator-radius estimate on two genuine production Fourier
tails with zero endpoint trace. -/
theorem factorTwoCenteredSymmetricPerturbationBilinear_sq_le_evenTail_energy_mul
    (r s : YoshidaClippedPeriodicCore yoshidaA)
    (hrTail : r ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)
    (hsTail : s ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)
    (hrNeg : (r : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hrPos : (r : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hsNeg : (s : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hsPos : (s : YoshidaClippedSmooth yoshidaA) yoshidaA = 0) :
    let u := centeredRescale yoshidaA (fun x ↦
      ((r : YoshidaClippedSmooth yoshidaA) x).re)
    let v := centeredRescale yoshidaA (fun x ↦
      ((s : YoshidaClippedSmooth yoshidaA) x).re)
    factorTwoCenteredSymmetricPerturbationBilinear u v ^ 2 ≤
      9 * (∫ x : ℝ in -1..1, u x ^ 2) *
        (∫ x : ℝ in -1..1, v x ^ 2) := by
  dsimp only
  let u : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((r : YoshidaClippedSmooth yoshidaA) x).re)
  let v : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((s : YoshidaClippedSmooth yoshidaA) x).re)
  have hu : Continuous u := by
    simpa only [u] using continuous_centeredRescale_re_of_endpoints_zero
      yoshidaA_pos r hrNeg hrPos
  have hv : Continuous v := by
    simpa only [v] using continuous_centeredRescale_re_of_endpoints_zero
      yoshidaA_pos s hsNeg hsPos
  have huEven : Function.Even u := by
    intro x
    dsimp only [u, centeredRescale]
    rw [show yoshidaA * -x = -(yoshidaA * x) by ring,
      evenTail_pointwise_even yoshidaA_pos 199 r hrTail (yoshidaA * x)]
  have hvEven : Function.Even v := by
    intro x
    dsimp only [v, centeredRescale]
    rw [show yoshidaA * -x = -(yoshidaA * x) by ring,
      evenTail_pointwise_even yoshidaA_pos 199 s hsTail (yoshidaA * x)]
  exact factorTwoCenteredSymmetricPerturbationBilinear_sq_le_even_energy_mul
    u v hu hv huEven hvEven

/-- The odd operator-radius estimate on two genuine production Fourier tails
with zero endpoint trace. -/
theorem factorTwoCenteredSymmetricPerturbationBilinear_sq_le_oddTail_energy_mul
    (r s : YoshidaClippedPeriodicCore yoshidaA)
    (hrTail : r ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)
    (hsTail : s ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)
    (hrNeg : (r : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hrPos : (r : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hsNeg : (s : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hsPos : (s : YoshidaClippedSmooth yoshidaA) yoshidaA = 0) :
    let u := centeredRescale yoshidaA (fun x ↦
      ((r : YoshidaClippedSmooth yoshidaA) x).re)
    let v := centeredRescale yoshidaA (fun x ↦
      ((s : YoshidaClippedSmooth yoshidaA) x).re)
    factorTwoCenteredSymmetricPerturbationBilinear u v ^ 2 ≤
      (9 / 4 : ℝ) * (∫ x : ℝ in -1..1, u x ^ 2) *
        (∫ x : ℝ in -1..1, v x ^ 2) := by
  dsimp only
  let u : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((r : YoshidaClippedSmooth yoshidaA) x).re)
  let v : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((s : YoshidaClippedSmooth yoshidaA) x).re)
  have hu : Continuous u := by
    simpa only [u] using continuous_centeredRescale_re_of_endpoints_zero
      yoshidaA_pos r hrNeg hrPos
  have hv : Continuous v := by
    simpa only [v] using continuous_centeredRescale_re_of_endpoints_zero
      yoshidaA_pos s hsNeg hsPos
  have huOdd : Function.Odd u := by
    intro x
    dsimp only [u, centeredRescale]
    rw [show yoshidaA * -x = -(yoshidaA * x) by ring,
      oddTail_pointwise_odd yoshidaA_pos 10 r hrTail (yoshidaA * x)]
    rfl
  have hvOdd : Function.Odd v := by
    intro x
    dsimp only [v, centeredRescale]
    rw [show yoshidaA * -x = -(yoshidaA * x) by ring,
      oddTail_pointwise_odd yoshidaA_pos 10 s hsTail (yoshidaA * x)]
    rfl
  exact factorTwoCenteredSymmetricPerturbationBilinear_sq_le_odd_energy_mul
    u v hu hv huOdd hvOdd

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointTailBilinearContinuityStructural
