import ArithmeticHodge.Analysis.YoshidaEvenCorrectionReality
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailPerturbationRowsStructural

noncomputable section

open ArithmeticHodge.Analysis
open FormSpace
open YoshidaCoercivityNumerics
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaEvenCorrectionReality
open YoshidaEvenHomogeneousCoercivity
open YoshidaEvenTailLowFunctional
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
open YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseEndpointAdaptedDecomposition
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPhaseEndpointTailBilinearContinuityStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseTailRealification
open YoshidaOddHomogeneousCoercivity
open YoshidaPointwiseParityCore
open YoshidaWeightedTailBounds

/-!
# Fourier rows for the canonical even low--tail perturbation

The previous canonical low--tail bound treated the symmetric perturbation by
its uniform operator radius and then rounded the resulting constant.  This
file exposes the actual Fourier row first.  In particular, the finite cosine
partial sums are expanded against the genuine high modes, not against an
abstract bounded functional.  The final estimate below also retains the exact
coercive constants instead of rounding them to `3 / yoshidaA`.
-/

/-- The genuine frequency-`200 + k` vector in the cutoff-`199` even tail. -/
def canonicalEvenHighTailMode (k : ℕ) : YoshidaEvenOneNinetyNineTail :=
  ⟨evenHighModePeriodicCore k, evenHighModePeriodicCore_mem_tail k⟩

@[simp] private theorem evenTail_smul_apply
    (c : ℂ) (f : YoshidaEvenOneNinetyNineTail) (x : ℝ) :
    (((c • f : YoshidaEvenOneNinetyNineTail) :
        YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) x =
      c * ((((f : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA)) x) := by
  rfl

@[simp] private theorem evenTail_real_smul_apply
    (r : ℝ) (f : YoshidaEvenOneNinetyNineTail) (x : ℝ) :
    (((r • f : YoshidaEvenOneNinetyNineTail) :
        YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) x =
      r • ((((f : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA)) x) := by
  rfl

@[simp] private theorem canonicalEvenHighTailMode_apply
    (k : ℕ) (x : ℝ) :
    ((((canonicalEvenHighTailMode k : YoshidaEvenOneNinetyNineTail) :
        YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA)) x =
      yoshidaClippedEvenMode yoshidaA (200 + k) x := by
  rfl

/-- The `k`-th entry of the symmetric-perturbation Fourier row belonging to
the retained canonical even coordinate `i`. -/
def canonicalEvenLowEvenTailSymmetricPerturbationRow
    (i : YoshidaEvenIndex) (k : ℕ) : ℝ :=
  factorTwoCenteredSymmetricPerturbationBilinear
    (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
    (boundaryCanonicalEvenTailProfile (canonicalEvenHighTailMode k))

private theorem canonicalEvenTailPointwise_add
    (f g : YoshidaEvenOneNinetyNineTail) :
    canonicalEvenTailPointwise (f + g) =
      canonicalEvenTailPointwise f + canonicalEvenTailPointwise g := by
  apply Subtype.ext
  rfl

private theorem canonicalEvenTailPointwise_smul_real
    (r : ℝ) (f : YoshidaEvenOneNinetyNineTail) :
    canonicalEvenTailPointwise ((r : ℂ) • f) =
      (r : ℂ) • canonicalEvenTailPointwise f := by
  apply Subtype.ext
  rfl

@[simp] theorem boundaryCanonicalEvenTailProfile_zero :
    boundaryCanonicalEvenTailProfile
      (0 : YoshidaEvenOneNinetyNineTail) = 0 := by
  unfold boundaryCanonicalEvenTailProfile
  rw [show canonicalEvenTailPointwise
      (0 : YoshidaEvenOneNinetyNineTail) = 0 by
    apply Subtype.ext
    rfl]
  exact boundaryContinuousEvenProfile_zero

theorem boundaryCanonicalEvenTailProfile_add
    (f g : YoshidaEvenOneNinetyNineTail) :
    boundaryCanonicalEvenTailProfile (f + g) =
      boundaryCanonicalEvenTailProfile f +
        boundaryCanonicalEvenTailProfile g := by
  unfold boundaryCanonicalEvenTailProfile
  rw [canonicalEvenTailPointwise_add,
    boundaryContinuousEvenProfile_add]

theorem boundaryCanonicalEvenTailProfile_smul_real
    (r : ℝ) (f : YoshidaEvenOneNinetyNineTail) :
    boundaryCanonicalEvenTailProfile ((r : ℂ) • f) =
      r • boundaryCanonicalEvenTailProfile f := by
  unfold boundaryCanonicalEvenTailProfile
  rw [canonicalEvenTailPointwise_smul_real,
    boundaryContinuousEvenProfile_smul_real]

private theorem boundaryCanonicalEvenTailProfile_sum_smul_real
    {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → YoshidaEvenOneNinetyNineTail) :
    boundaryCanonicalEvenTailProfile
        (∑ k ∈ s, ((c k : ℝ) : ℂ) • f k) =
      ∑ k ∈ s, c k • boundaryCanonicalEvenTailProfile (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk,
        boundaryCanonicalEvenTailProfile_add,
        boundaryCanonicalEvenTailProfile_smul_real, ih]

/-- Realifying the genuine complex Fourier partial sum simply replaces every
cosine coefficient by its real part. -/
theorem realified_evenTailCosinePartialSumTail_eq_sum
    (f : YoshidaEvenOneNinetyNineTail) (N : ℕ) :
    realifiedEvenOneNinetyNineTail (evenTailCosinePartialSumTail f N) =
      ∑ k ∈ Finset.range N,
        ((((evenTailCosineCoefficient f k).re : ℝ) : ℂ) •
          canonicalEvenHighTailMode k) := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change
    evenOneNinetyNineTailToClippedSmooth
        (realifiedEvenOneNinetyNineTail
          (evenTailCosinePartialSumTail f N)) x =
      evenOneNinetyNineTailToClippedSmooth
        (∑ k ∈ Finset.range N,
          (((evenTailCosineCoefficient f k).re : ℂ) •
            canonicalEvenHighTailMode k)) x
  rw [realifiedEvenOneNinetyNineTail_apply]
  rw [show evenOneNinetyNineTailToClippedSmooth
      (evenTailCosinePartialSumTail f N) =
        evenTailCosinePartialSum f N by
    exact evenTailCosinePartialSumPeriodicCore_toSmooth f N]
  simp only [map_sum, map_smul]
  apply Complex.ext
  · simp [evenTailCosinePartialSum,
      Pi.smul_apply, smul_eq_mul, ofReal_re, ofReal_im,
      Complex.mul_re, evenMode_im_zero]
    apply Finset.sum_congr rfl
    intro k _hk
    change (evenTailCosineCoefficient f k).re *
        (yoshidaClippedEvenMode yoshidaA (200 + k) x).re =
      (((evenTailCosineCoefficient f k).re : ℂ) *
        yoshidaClippedEvenMode yoshidaA (200 + k) x).re
    simp only [Complex.mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  · simp [evenTailCosinePartialSum,
      Pi.smul_apply, smul_eq_mul, ofReal_re, ofReal_im,
      Complex.mul_im, evenMode_im_zero]
    symm
    apply Finset.sum_eq_zero
    intro k _hk
    change (((evenTailCosineCoefficient f k).re : ℂ) *
        yoshidaClippedEvenMode yoshidaA (200 + k) x).im = 0
    simp only [Complex.mul_im, ofReal_re, ofReal_im, zero_mul,
      evenMode_im_zero, mul_zero, add_zero]

/-- Exact profile expansion of the real Fourier partial sum. -/
theorem boundaryCanonicalEvenTailProfile_realified_partialSum_eq_sum
    (f : YoshidaEvenOneNinetyNineTail) (N : ℕ) :
    boundaryCanonicalEvenTailProfile
        (realifiedEvenOneNinetyNineTail
          (evenTailCosinePartialSumTail f N)) =
      ∑ k ∈ Finset.range N,
        (evenTailCosineCoefficient f k).re •
          boundaryCanonicalEvenTailProfile (canonicalEvenHighTailMode k) := by
  rw [realified_evenTailCosinePartialSumTail_eq_sum]
  exact boundaryCanonicalEvenTailProfile_sum_smul_real
    (Finset.range N) (fun k ↦ (evenTailCosineCoefficient f k).re)
      canonicalEvenHighTailMode

private theorem symmetricPerturbationBilinear_comm
    (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear u v =
      factorTwoCenteredSymmetricPerturbationBilinear v u := by
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_comm u v]

private theorem symmetricPerturbationBilinear_add_right
    (u v w : ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    factorTwoCenteredSymmetricPerturbationBilinear u (v + w) =
      factorTwoCenteredSymmetricPerturbationBilinear u v +
        factorTwoCenteredSymmetricPerturbationBilinear u w := by
  rw [symmetricPerturbationBilinear_comm,
    factorTwoCenteredSymmetricPerturbationBilinear_add_left v w u hv hw hu,
    symmetricPerturbationBilinear_comm v u,
    symmetricPerturbationBilinear_comm w u]

private theorem symmetricPerturbationBilinear_smul_right
    (r : ℝ) (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear u (r • v) =
      r * factorTwoCenteredSymmetricPerturbationBilinear u v := by
  rw [symmetricPerturbationBilinear_comm,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_left,
    symmetricPerturbationBilinear_comm v u]

@[simp] private theorem symmetricPerturbationBilinear_zero_right
    (u : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear u 0 = 0 := by
  have h := symmetricPerturbationBilinear_smul_right 0 u u
  simpa only [zero_smul, zero_mul] using h

private theorem continuous_finset_smul_sum
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → ℝ → ℝ)
    (hu : ∀ k, Continuous (u k)) :
    Continuous (∑ k ∈ s, c k • u k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℝ)))
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact ((hu k).const_smul (c k)).add ih

private theorem symmetricPerturbationBilinear_sum_right
    {ι : Type*} (s : Finset ι) (u : ℝ → ℝ)
    (c : ι → ℝ) (v : ι → ℝ → ℝ)
    (hu : Continuous u) (hv : ∀ k, Continuous (v k)) :
    factorTwoCenteredSymmetricPerturbationBilinear u
        (∑ k ∈ s, c k • v k) =
      ∑ k ∈ s,
        c k * factorTwoCenteredSymmetricPerturbationBilinear u (v k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, symmetricPerturbationBilinear_zero_right]
  | @insert k s hk ih =>
      have hs : Continuous (∑ j ∈ s, c j • v j) :=
        continuous_finset_smul_sum s c v hv
      rw [Finset.sum_insert hk, Finset.sum_insert hk,
        symmetricPerturbationBilinear_add_right u (c k • v k)
          (∑ j ∈ s, c j • v j) hu ((hv k).const_smul (c k)) hs,
        symmetricPerturbationBilinear_smul_right, ih]

/-- Exact finite Fourier expansion of a canonical even perturbation row.
This is the missing algebraic/analytic interface needed before Parseval can
replace the uniform operator-radius estimate by a row-square budget. -/
theorem canonicalEvenLowEvenTailSymmetricPerturbation_partialSum_expansion
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex) (N : ℕ) :
    factorTwoCenteredSymmetricPerturbationBilinear
        (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
        (boundaryCanonicalEvenTailProfile
          (realifiedEvenOneNinetyNineTail
            (evenTailCosinePartialSumTail f N))) =
      ∑ k ∈ Finset.range N,
        (evenTailCosineCoefficient f k).re *
          canonicalEvenLowEvenTailSymmetricPerturbationRow i k := by
  rw [boundaryCanonicalEvenTailProfile_realified_partialSum_eq_sum]
  exact symmetricPerturbationBilinear_sum_right
    (Finset.range N)
    (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
    (fun k ↦ (evenTailCosineCoefficient f k).re)
    (fun k ↦ boundaryCanonicalEvenTailProfile (canonicalEvenHighTailMode k))
    (continuous_boundaryContinuousEvenProfile
      (canonicalEvenLowModePointwise i))
    (fun k ↦ continuous_boundaryCanonicalEvenTailProfile
      (canonicalEvenHighTailMode k))

/-- The clean form norm controls the boundary-continuous even-tail `L²`
energy with the exact coercivity constant. -/
theorem boundaryCanonicalEvenTailProfile_energy_le_formNorm_sq
    (e : YoshidaEvenOneNinetyNineTail)
    (hreal : ∀ t : ℝ,
      (evenOneNinetyNineTailToClippedSmooth e t).im = 0) :
    (∫ t : ℝ in -1..1,
      boundaryCanonicalEvenTailProfile e t ^ 2) ≤
      (25 / (102 * yoshidaA) : ℝ) *
        ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2 := by
  have hcoercive := evenTail_boundaryContinuous_clean_coercive
    (e : YoshidaClippedPeriodicCore yoshidaA) e.property hreal
  have hnorm := evenRealTailFormSpace_norm_sq_eq_clean e hreal
  change (102 / 25 : ℝ) *
      (∫ t : ℝ in -1..1,
        boundaryCanonicalEvenTailProfile e t ^ 2) ≤
    yoshidaEndpointOddCleanQuadratic
      (boundaryCanonicalEvenTailProfile e) at hcoercive
  have hscaled := mul_le_mul_of_nonneg_left hcoercive yoshidaA_pos.le
  have hraw :
      (102 / 25 : ℝ) * yoshidaA *
          (∫ t : ℝ in -1..1,
            boundaryCanonicalEvenTailProfile e t ^ 2) ≤
        ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2 := by
    rw [hnorm]
    nlinarith
  calc
    (∫ t : ℝ in -1..1,
        boundaryCanonicalEvenTailProfile e t ^ 2) =
        (25 / (102 * yoshidaA) : ℝ) *
          ((102 / 25 : ℝ) * yoshidaA *
            (∫ t : ℝ in -1..1,
              boundaryCanonicalEvenTailProfile e t ^ 2)) := by
      field_simp [yoshidaA_pos.ne']
    _ ≤ (25 / (102 * yoshidaA) : ℝ) *
        ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hraw
        (div_nonneg (by norm_num)
          (mul_nonneg (by norm_num) yoshidaA_pos.le))

/-- A genuinely row-level symmetric-perturbation estimate.  It retains the
exact product of the radius `9`, the normalized low-mode energy `1/A`, and
the even-tail coercive energy factor `25/(102 A)`; the former implementation
rounded this coefficient up to `9 / A²`. -/
theorem canonicalEvenLowEvenTailSymmetricPerturbation_sq_le_formNorm_sq
    (i : YoshidaEvenIndex) (e : YoshidaEvenOneNinetyNineTail)
    (hreal : ∀ t : ℝ,
      (evenOneNinetyNineTailToClippedSmooth e t).im = 0) :
    factorTwoCenteredSymmetricPerturbationBilinear
        (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
        (boundaryCanonicalEvenTailProfile e) ^ 2 ≤
      (225 / (102 * yoshidaA ^ 2) : ℝ) *
        ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2 := by
  have hrow :=
    factorTwoCenteredSymmetricPerturbationBilinear_sq_le_even_energy_mul
      (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
      (boundaryCanonicalEvenTailProfile e)
      (continuous_boundaryContinuousEvenProfile
        (canonicalEvenLowModePointwise i))
      (continuous_boundaryCanonicalEvenTailProfile e)
      (boundaryContinuousEvenProfile_even
        (canonicalEvenLowModePointwise i))
      (boundaryContinuousEvenProfile_even (canonicalEvenTailPointwise e))
  rw [canonicalEvenLowBasis_energy_eq] at hrow
  have henergy :=
    boundaryCanonicalEvenTailProfile_energy_le_formNorm_sq e hreal
  have hnonneg : 0 ≤ (9 : ℝ) * (1 / yoshidaA) :=
    mul_nonneg (by norm_num) (div_nonneg (by norm_num) yoshidaA_pos.le)
  calc
    factorTwoCenteredSymmetricPerturbationBilinear
        (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
        (boundaryCanonicalEvenTailProfile e) ^ 2 ≤
      9 * (1 / yoshidaA) *
        (∫ t : ℝ in -1..1,
          boundaryCanonicalEvenTailProfile e t ^ 2) := hrow
    _ ≤ 9 * (1 / yoshidaA) *
        ((25 / (102 * yoshidaA) : ℝ) *
          ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left henergy hnonneg
    _ = (225 / (102 * yoshidaA ^ 2) : ℝ) *
        ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2 := by
      field_simp [yoshidaA_pos.ne']
      ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailPerturbationRowsStructural
