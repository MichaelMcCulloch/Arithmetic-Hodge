import ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailMiddleReductionStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP51RawMassCancellationStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailRawStripSchurStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreLogKernel
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddP51HighTailMiddleReductionStructural
open YoshidaFourCellOddP51RawMassCancellationStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Exact local Schur form of the P51 raw-strip surplus

The global raw-log and scalar-mass mixed rows vanish between the retained
`P3,...,P51` block and a genuine `P53+` tail.  Consequently the outstanding
one-eighth surplus has only one mixed row: the endpoint-strip raw
polarization coupled to the retained prime/potential polarization.

This module records that exact decomposition and reduces positivity to the
two genuine Schur obligations: positivity of the tail diagonal after the
`1/256` raw reservation, and one local mixed determinant inequality.  No
Legendre mode is enumerated.
-/

private theorem odd_const_mul
    {v : ℝ → ℝ} (hv : Function.Odd v) (t : ℝ) :
    Function.Odd (fun x ↦ t * v x) := by
  intro x
  change t * v (-x) = -(t * v x)
  rw [hv]
  ring

/-- Exact polarization of the nineteen-twentieths retained quadratic. -/
def fourCellOddP51RetainedSurplusPolarization
    (u v : ℝ → ℝ) : ℝ :=
  (fourCellOddNineteenTwentiethsRetainedQuadratic (u + v) -
      fourCellOddNineteenTwentiethsRetainedQuadratic u -
      fourCellOddNineteenTwentiethsRetainedQuadratic v) / 2

/-- Exact polarization of the positive prime/potential diagonal. -/
def fourCellOddP51PrimePotentialPolarization
    (u v : ℝ → ℝ) : ℝ :=
  (fourCellOddRetainedPrimePotentialQuadratic (u + v) -
      fourCellOddRetainedPrimePotentialQuadratic u -
      fourCellOddRetainedPrimePotentialQuadratic v) / 2

/-- The only mixed row left after global raw and scalar-mass orthogonality. -/
def fourCellOddP51HighTailLocalMixed
    (u v : ℝ → ℝ) : ℝ :=
  -(19 / 40 : ℝ) *
      fourCellOddEndpointStripOddRawPolarization u v +
    fourCellOddRetainedPrimePotentialBilinear u v

/-- Tail diagonal after reserving one sixty-fourth of the raw-div-four
gap. -/
def fourCellOddP51OneEighthTailDiagonal (v : ℝ → ℝ) : ℝ :=
  fourCellOddNineteenTwentiethsRetainedQuadratic v -
    centeredRawLogEnergy v / 256

private theorem positiveHalfMass_polarization_eq
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    ((∫ x : ℝ in 0..1, (u + v) x ^ 2) -
        (∫ x : ℝ in 0..1, u x ^ 2) -
        (∫ x : ℝ in 0..1, v x ^ 2)) / 2 =
      ∫ x : ℝ in 0..1, u x * v x := by
  have huu : IntervalIntegrable (fun x : ℝ ↦ u x ^ 2) volume 0 1 :=
    (hu.pow 2).intervalIntegrable _ _
  have huv : IntervalIntegrable (fun x : ℝ ↦ 2 * (u x * v x))
      volume 0 1 :=
    (continuous_const.mul (hu.mul hv)).intervalIntegrable _ _
  have hvv : IntervalIntegrable (fun x : ℝ ↦ v x ^ 2) volume 0 1 :=
    (hv.pow 2).intervalIntegrable _ _
  rw [show (fun x : ℝ ↦ (u + v) x ^ 2) =
      fun x ↦ u x ^ 2 + 2 * (u x * v x) + v x ^ 2 by
    funext x
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add (huu.add huv) hvv,
    intervalIntegral.integral_add huu huv,
    intervalIntegral.integral_const_mul]
  ring

private theorem intervalMass_polarization_eq
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) :
    ((∫ x : ℝ in a..b, (f x + g x) ^ 2) -
        (∫ x : ℝ in a..b, f x ^ 2) -
        (∫ x : ℝ in a..b, g x ^ 2)) / 2 =
      ∫ x : ℝ in a..b, f x * g x := by
  have hff : IntervalIntegrable (fun x : ℝ ↦ f x ^ 2) volume a b :=
    (hf.pow 2).intervalIntegrable _ _
  have hfg : IntervalIntegrable (fun x : ℝ ↦ 2 * (f x * g x))
      volume a b :=
    (continuous_const.mul (hf.mul hg)).intervalIntegrable _ _
  have hgg : IntervalIntegrable (fun x : ℝ ↦ g x ^ 2) volume a b :=
    (hg.pow 2).intervalIntegrable _ _
  rw [show (fun x : ℝ ↦ (f x + g x) ^ 2) =
      fun x ↦ f x ^ 2 + 2 * (f x * g x) + g x ^ 2 by
    funext x
    ring,
    intervalIntegral.integral_add (hff.add hfg) hgg,
    intervalIntegral.integral_add hff hfg,
    intervalIntegral.integral_const_mul]
  ring

private theorem endpointStripEvenMass_polarization_eq
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (fourCellOddEndpointStripEvenMass (u + v) -
        fourCellOddEndpointStripEvenMass u -
        fourCellOddEndpointStripEvenMass v) / 2 =
      fourCellOddEndpointStripEvenMassBilinear u v := by
  let U := fourCellOddEndpointStripEven u
  let V := fourCellOddEndpointStripEven v
  have hU : Continuous U := by
    dsimp only [U]
    exact continuous_fourCellOddEndpointStripEven u hu
  have hV : Continuous V := by
    dsimp only [V]
    exact continuous_fourCellOddEndpointStripEven v hv
  have hadd : fourCellOddEndpointStripEven (u + v) = U + V := by
    funext z
    dsimp only [U, V]
    unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
    simp only [Pi.add_apply]
    ring
  have hmass := intervalMass_polarization_eq U V hU hV (-1) 1
  unfold fourCellOddEndpointStripEvenMass
    fourCellOddEndpointStripEvenMassBilinear
  rw [hadd]
  dsimp only [U, V] at hmass ⊢
  linear_combination (1 / 5 : ℝ) * hmass

private theorem endpointStripOddMass_polarization_eq
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (fourCellOddEndpointStripOddMass (u + v) -
        fourCellOddEndpointStripOddMass u -
        fourCellOddEndpointStripOddMass v) / 2 =
      fourCellOddEndpointStripOddMassBilinear u v := by
  let U := fourCellOddEndpointStripOdd u
  let V := fourCellOddEndpointStripOdd v
  have hU : Continuous U := by
    dsimp only [U]
    exact continuous_fourCellOddEndpointStripOdd u hu
  have hV : Continuous V := by
    dsimp only [V]
    exact continuous_fourCellOddEndpointStripOdd v hv
  have hadd : fourCellOddEndpointStripOdd (u + v) = U + V := by
    funext z
    dsimp only [U, V]
    unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    simp only [Pi.add_apply]
    ring
  have hmass := intervalMass_polarization_eq U V hU hV (-1) 1
  unfold fourCellOddEndpointStripOddMass
    fourCellOddEndpointStripOddMassBilinear
  rw [hadd]
  dsimp only [U, V] at hmass ⊢
  linear_combination (1 / 5 : ℝ) * hmass

private theorem endpointPotential_polarization_eq
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    ((∫ x : ℝ in 0..1,
          yoshidaEndpointPotential x * (u + v) x ^ 2) -
        (∫ x : ℝ in 0..1,
          yoshidaEndpointPotential x * u x ^ 2) -
        (∫ x : ℝ in 0..1,
          yoshidaEndpointPotential x * v x ^ 2)) / 2 =
      ∫ x : ℝ in 0..1,
        yoshidaEndpointPotential x * u x * v x := by
  have hsub : uIcc (0 : ℝ) 1 ⊆ uIcc (-1 : ℝ) 1 := by
    intro x hx
    norm_num at hx ⊢
    constructor <;> linarith
  have huu : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * u x ^ 2)
      volume 0 1 :=
    (intervalIntegrable_endpointPotential_mul_sq u hu).mono_set hsub
  have huv : IntervalIntegrable
      (fun x : ℝ ↦ 2 *
        (yoshidaEndpointPotential x * u x * v x)) volume 0 1 := by
    simpa only [mul_assoc] using
      ((intervalIntegrable_endpointPotential_mul
        (fun x ↦ u x * v x) (hu.mul hv)).mono_set hsub).const_mul 2
  have hvv : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * v x ^ 2)
      volume 0 1 :=
    (intervalIntegrable_endpointPotential_mul_sq v hv).mono_set hsub
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * (u + v) x ^ 2) =
      fun x ↦ yoshidaEndpointPotential x * u x ^ 2 +
        2 * (yoshidaEndpointPotential x * u x * v x) +
        yoshidaEndpointPotential x * v x ^ 2 by
    funext x
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add (huu.add huv) hvv,
    intervalIntegral.integral_add huu huv,
    intervalIntegral.integral_const_mul]
  ring

/-- The abstract prime/potential polarization used in the decomposition is
the existing explicit bilinear form, so its structural Cauchy theorem applies
without any new finite certificate. -/
theorem fourCellOddP51PrimePotentialPolarization_eq_bilinear
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellOddP51PrimePotentialPolarization u v =
      fourCellOddRetainedPrimePotentialBilinear u v := by
  have heven := endpointStripEvenMass_polarization_eq u v hu hv
  have hodd := endpointStripOddMass_polarization_eq u v hu hv
  have hpotential := endpointPotential_polarization_eq u v hu hv
  unfold fourCellOddP51PrimePotentialPolarization
    fourCellOddRetainedPrimePotentialQuadratic
    fourCellOddRetainedPrimePotentialBilinear
  linear_combination
    (Real.sqrt 2 * Real.log 2) * heven +
    (2 - Real.sqrt 2 * Real.log 2) * hodd +
    (93 / 50 : ℝ) * hpotential

private theorem retainedSurplusPolarization_eq_raw_prime_mass
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellOddP51RetainedSurplusPolarization u v =
      (19 / 20 : ℝ) *
          fourCellOddRawStripCancellationPolarization u v +
        fourCellOddP51PrimePotentialPolarization u v -
        fourCellOddLocalScalarMassCoefficient *
          (∫ x : ℝ in 0..1, u x * v x) := by
  have hmass := positiveHalfMass_polarization_eq u v hu hv
  unfold fourCellOddP51RetainedSurplusPolarization
    fourCellOddP51PrimePotentialPolarization
    fourCellOddNineteenTwentiethsRetainedQuadratic
    fourCellOddRawStripCancellationPolarization
  linear_combination
    -fourCellOddLocalScalarMassCoefficient * hmass

private theorem scaled_tail_moments
    (t : ℝ) (r : ℝ → ℝ)
    (htail : FourCellOddP53PlusMomentConditions r) :
    ∀ i : FourCellOddP51RetainedIndex,
      (∫ x : ℝ in 0..1,
        fourCellOddFiniteRetainedBasis i x * (t * r x)) = 0 := by
  intro i
  rw [show (fun x : ℝ ↦
      fourCellOddFiniteRetainedBasis i x * (t * r x)) =
      fun x ↦ t * (fourCellOddFiniteRetainedBasis i x * r x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul, htail.2 i]
  ring

/-- The global raw-log and scalar-mass rows disappear exactly.  The surviving
mixed term is supported solely by the adverse endpoint-strip raw channel and
the positive prime/potential channel. -/
theorem retainedSurplusPolarization_retained_scaled_P53Plus_eq_localMixed
    (a : FourCellOddP51RetainedIndex → ℝ) (t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    fourCellOddP51RetainedSurplusPolarization
        (fourCellOddP51RetainedProfile a) (fun x ↦ t * r x) =
      fourCellOddP51HighTailLocalMixed
        (fourCellOddP51RetainedProfile a) (fun x ↦ t * r x) := by
  let u := fourCellOddP51RetainedProfile a
  let v : ℝ → ℝ := fun x ↦ t * r x
  have hu : ContDiff ℝ 1 u := by
    dsimp only [u, fourCellOddP51RetainedProfile]
    exact contDiff_fourCellOddFiniteRetainedProfile 24 a
  have huodd : Function.Odd u := by
    dsimp only [u, fourCellOddP51RetainedProfile]
    exact odd_fourCellOddFiniteRetainedProfile 24 a
  have hv : ContDiff ℝ 1 v := by
    dsimp only [v]
    exact contDiff_const.mul hr
  have hvodd : Function.Odd v := by
    dsimp only [v]
    exact odd_const_mul hodd t
  have hvmom : ∀ i : FourCellOddP51RetainedIndex,
      (∫ x : ℝ in 0..1,
        fourCellOddFiniteRetainedBasis i x * v x) = 0 := by
    simpa only [v] using scaled_tail_moments t r htail
  have hrawGlobal : centeredRawLogBilinear u v = 0 := by
    dsimp only [u, v, fourCellOddP51RetainedProfile]
    exact centeredRawLogBilinear_finiteRetainedProfile_tail_eq_zero
      24 a (fun x ↦ t * r x) hv hvodd hvmom
  have hraw :=
    fourCellOddRawStripCancellationPolarization_eq_centered_sub_strip
      u v hu hv huodd hvodd
  rw [hrawGlobal] at hraw
  have hmass : (∫ x : ℝ in 0..1, u x * v x) = 0 := by
    dsimp only [u, v, fourCellOddP51RetainedProfile]
    exact integral_zero_one_fourCellOddFiniteRetainedProfile_mul_tail_eq_zero
      24 a (fun x ↦ t * r x) hv.continuous hvmom
  have hsplit := retainedSurplusPolarization_eq_raw_prime_mass
    u v hu.continuous hv.continuous
  have hprime := fourCellOddP51PrimePotentialPolarization_eq_bilinear
    u v hu.continuous hv.continuous
  dsimp only [u, v] at hsplit ⊢
  rw [hsplit, hraw, hmass, hprime]
  unfold fourCellOddP51HighTailLocalMixed
  ring

/-- Exact diagonal-plus-local-mixed decomposition of the outstanding
one-eighth surplus.  In particular, there is no hidden global raw mixed row
and no hidden scalar mass mixed row. -/
theorem fourCellOddP51OneEighthRawStripSurplus_eq_low_add_localMixed_add_tail
    (a : FourCellOddP51RetainedIndex → ℝ) (t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    fourCellOddP51OneEighthRawStripSurplus a t r =
      fourCellOddNineteenTwentiethsRetainedQuadratic
          (fourCellOddP51RetainedProfile a) +
        2 * fourCellOddP51HighTailLocalMixed
          (fourCellOddP51RetainedProfile a) (fun x ↦ t * r x) +
        fourCellOddP51OneEighthTailDiagonal (fun x ↦ t * r x) := by
  let u := fourCellOddP51RetainedProfile a
  let v : ℝ → ℝ := fun x ↦ t * r x
  have hpolar :=
    retainedSurplusPolarization_retained_scaled_P53Plus_eq_localMixed
      a t r hr hodd htail
  have hrawScale := centeredRawLogEnergy_const_mul t r
  have hprofile : fourCellOddP51HighTailMiddleProfile a t r = u + v := by
    rfl
  rw [←
    fourCellOddNineteenTwentiethsRetainedQuadratic_sub_scaledRaw_eq_surplus
      a t r]
  rw [hprofile]
  have hadd :
      fourCellOddNineteenTwentiethsRetainedQuadratic (u + v) =
        fourCellOddNineteenTwentiethsRetainedQuadratic u +
          2 * fourCellOddP51RetainedSurplusPolarization u v +
          fourCellOddNineteenTwentiethsRetainedQuadratic v := by
    unfold fourCellOddP51RetainedSurplusPolarization
    ring
  rw [hadd]
  dsimp only [u, v] at hpolar ⊢
  unfold fourCellOddP51OneEighthTailDiagonal
  rw [hpolar, hrawScale]
  ring

/-- The retained low diagonal is already nonnegative; the Schur reduction
does not leave a finite-mode sign premise. -/
theorem fourCellOddP51RetainedLowDiagonal_nonneg
    (a : FourCellOddP51RetainedIndex → ℝ) :
    0 ≤ fourCellOddNineteenTwentiethsRetainedQuadratic
      (fourCellOddP51RetainedProfile a) := by
  let u := fourCellOddP51RetainedProfile a
  have hu : ContDiff ℝ 1 u := by
    dsimp only [u, fourCellOddP51RetainedProfile]
    exact contDiff_fourCellOddFiniteRetainedProfile 24 a
  have huodd : Function.Odd u := by
    dsimp only [u, fourCellOddP51RetainedProfile]
    exact odd_fourCellOddFiniteRetainedProfile 24 a
  have hu1 : centeredOddP1Coefficient u = 0 := by
    dsimp only [u, fourCellOddP51RetainedProfile]
    exact centeredOddP1Coefficient_fourCellOddFiniteRetainedProfile_eq_zero
      24 a
  have hcoercive :=
    coercivityConstant_mul_positiveHalfMass_le_retainedQuadratic_of_P1
      u hu huodd hu1
  have hmass : 0 ≤ ∫ x : ℝ in 0..1, u x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (u x))
  have hbase : 0 ≤
      fourCellOddNineteenTwentiethsCoercivityConstant *
        (∫ x : ℝ in 0..1, u x ^ 2) :=
    mul_nonneg fourCellOddNineteenTwentiethsCoercivityConstant_pos.le hmass
  dsimp only [u] at hcoercive ⊢
  exact hbase.trans hcoercive

/-- Exact Schur handoff.  The former single opaque surplus is reduced to a
tail diagonal and one determinant inequality for the explicitly local mixed
row. -/
theorem fourCellOddP51OneEighthRawStripSurplus_nonneg_of_localSchur
    (a : FourCellOddP51RetainedIndex → ℝ) (t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r)
    (htailDiag : 0 ≤
      fourCellOddP51OneEighthTailDiagonal (fun x ↦ t * r x))
    (hmixed :
      fourCellOddP51HighTailLocalMixed
          (fourCellOddP51RetainedProfile a) (fun x ↦ t * r x) ^ 2 ≤
        fourCellOddNineteenTwentiethsRetainedQuadratic
            (fourCellOddP51RetainedProfile a) *
          fourCellOddP51OneEighthTailDiagonal (fun x ↦ t * r x)) :
    0 ≤ fourCellOddP51OneEighthRawStripSurplus a t r := by
  let A := fourCellOddNineteenTwentiethsRetainedQuadratic
    (fourCellOddP51RetainedProfile a)
  let B := fourCellOddP51OneEighthTailDiagonal (fun x ↦ t * r x)
  let C := fourCellOddP51HighTailLocalMixed
    (fourCellOddP51RetainedProfile a) (fun x ↦ t * r x)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact fourCellOddP51RetainedLowDiagonal_nonneg a
  have hquad :=
    (YoshidaFactorTwoEndpointBilinear.real_quadratic_pencil_nonneg_iff A B C).2
      ⟨hA, htailDiag, hmixed⟩ 1 1
  have hsplit :=
    fourCellOddP51OneEighthRawStripSurplus_eq_low_add_localMixed_add_tail
      a t r hr hodd htail
  dsimp only [A, B, C] at hquad
  rw [hsplit]
  norm_num at hquad ⊢
  exact hquad

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailRawStripSchurStructural
