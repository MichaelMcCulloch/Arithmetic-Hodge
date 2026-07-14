import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenSchur

set_option autoImplicit false

open Filter MeasureTheory Real Set Topology
open scoped BigOperators Interval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenSchurClosure

noncomputable section

open EndpointParityCarleman
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseAlternatingCoercivity
open YoshidaFactorTwoPhaseEvenSchur
open YoshidaFactorTwoPhaseEvenSymmetricBound
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseRankLimit
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaFactorTwoPhaseTailCoercivity
open YoshidaRenormalizedGeometricKernel

/-!
# Infinite Schur closure of the even factor-two rank tail

The exact finite endpoint kernel is bounded by the parity Carleman kernel
plus the constant row `1 / 4`.  The parity row costs `pi` on the endpoint
half interval, while the constant row costs `1 / 4`; even reflection then
halves both constants in centered-energy normalization.
-/

/-- The finite endpoint-kernel density is integrable on the positive unit
square. -/
private theorem integrable_evenRankEndpointPartialDensity
    (w : ℝ → ℝ) (hw : Continuous w) (N : ℕ) :
    Integrable
      (fun z : ℝ × ℝ ↦
        evenRankEndpointPartialKernel N z.1 z.2 *
          w (1 - z.1) * w (1 - z.2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))) := by
  let F : ℝ × ℝ → ℝ := fun z ↦
    evenRankEndpointPartialKernel N z.1 z.2 *
      w (1 - z.1) * w (1 - z.2)
  have hF : Continuous F := by
    dsimp only [F, evenRankEndpointPartialKernel]
    fun_prop
  have hcompact : IntegrableOn F
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.prod_restrict]
  exact hcompact.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- The harmless constant-row Schur remainder is integrable. -/
private theorem integrable_evenRankConstantMajorant
    (w : ℝ → ℝ) (hw : Continuous w) :
    Integrable
      (fun z : ℝ × ℝ ↦
        (1 / 8 : ℝ) *
          (w (1 - z.1) ^ 2 + w (1 - z.2) ^ 2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))) := by
  let F : ℝ × ℝ → ℝ := fun z ↦
    (1 / 8 : ℝ) *
      (w (1 - z.1) ^ 2 + w (1 - z.2) ^ 2)
  have hF : Continuous F := by
    dsimp only [F]
    fun_prop
  have hcompact : IntegrableOn F
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.prod_restrict]
  exact hcompact.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- Exact integral of the constant-row square majorant. -/
private theorem integral_evenRankConstantMajorant
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ z : ℝ × ℝ,
        (1 / 8 : ℝ) *
          (w (1 - z.1) ^ 2 + w (1 - z.2) ^ 2)
      ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (volume.restrict (Ioc (0 : ℝ) 1)))) =
      (1 / 4 : ℝ) *
        (∫ p : ℝ in 0..1, w (1 - p) ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let f : ℝ → ℝ := fun p ↦ w (1 - p) ^ 2
  have hf : Integrable f μ := by
    have hcont : Continuous f := by
      dsimp only [f]
      fun_prop
    have hcompact : IntegrableOn f (Icc (0 : ℝ) 1) :=
      hcont.continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hμ : μ.real Set.univ = 1 := by
    dsimp only [μ]
    simp
  have hfirst : Integrable (fun z : ℝ × ℝ ↦ f z.1) (μ.prod μ) :=
    hf.comp_fst μ
  have hsecond : Integrable (fun z : ℝ × ℝ ↦ f z.2) (μ.prod μ) :=
    hf.comp_snd μ
  change (∫ z : ℝ × ℝ,
      (1 / 8 : ℝ) * (f z.1 + f z.2) ∂μ.prod μ) = _
  rw [MeasureTheory.integral_const_mul, integral_add hfirst hsecond]
  rw [integral_fun_fst, integral_fun_snd]
  simp only [smul_eq_mul, hμ, one_mul]
  change (1 / 8 : ℝ) *
      ((∫ p : ℝ, f p ∂μ) + ∫ p : ℝ, f p ∂μ) = _
  have hfint : (∫ p : ℝ, f p ∂μ) =
      ∫ p : ℝ in 0..1, w (1 - p) ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
  rw [hfint]
  ring

/-- Every finite decaying-rank square sum costs at most
`(pi / 2 + 1 / 8)` centered energies. -/
theorem evenRankPartialSquares_le_schur_energy
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w)
    (N : ℕ) :
    yoshidaEndpointA *
        (∑ m ∈ Finset.range N,
          Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            centeredCoshMoment w
              (yoshidaEndpointA * oddRate (m + 1)) ^ 2) ≤
      (Real.pi / 2 + 1 / 8 : ℝ) *
        (∫ x : ℝ in -1..1, w x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let f : ℝ → ℝ := fun p ↦ w (1 - p)
  let D : ℝ × ℝ → ℝ := fun z ↦
    evenRankEndpointPartialKernel N z.1 z.2 * f z.1 * f z.2
  let M : ℝ × ℝ → ℝ := fun z ↦
    parityUnitAbsBilinearDensity f f z +
      (1 / 8 : ℝ) * (f z.1 ^ 2 + f z.2 ^ 2)
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hD : Integrable D (μ.prod μ) := by
    simpa only [D, f, μ] using
      integrable_evenRankEndpointPartialDensity w hw N
  have hunit : Integrable (parityUnitAbsBilinearDensity f f)
      (μ.prod μ) := by
    simpa only [μ] using integrable_parityUnitAbsBilinearDensity f f hf hf
  have hconstant : Integrable
      (fun z : ℝ × ℝ ↦
        (1 / 8 : ℝ) * (f z.1 ^ 2 + f z.2 ^ 2))
      (μ.prod μ) := by
    simpa only [f, μ] using integrable_evenRankConstantMajorant w hw
  have hM : Integrable M (μ.prod μ) := by
    dsimp only [M]
    exact hunit.add hconstant
  have hpq : ∀ᵐ z ∂μ.prod μ,
      z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hpoint : ∀ᵐ z ∂μ.prod μ, D z ≤ M z := by
    filter_upwards [hpq] with z hz
    have hkernel := evenRankEndpointPartialKernel_le_parityUnit_add_quarter
      N hz.1.1 hz.1.2 hz.2.1 hz.2.2
    have hkernel0 : 0 ≤ evenRankEndpointPartialKernel N z.1 z.2 := by
      unfold evenRankEndpointPartialKernel
      exact Finset.sum_nonneg fun m _hm ↦
        mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) yoshidaEndpointA_pos.le)
              (Real.exp_pos _).le)
            (Real.cosh_pos _).le)
          (Real.cosh_pos _).le
    have hprod : f z.1 * f z.2 ≤ |f z.1 * f z.2| := le_abs_self _
    have hfirst :
        evenRankEndpointPartialKernel N z.1 z.2 *
              (f z.1 * f z.2) ≤
          evenRankEndpointPartialKernel N z.1 z.2 *
              |f z.1 * f z.2| :=
      mul_le_mul_of_nonneg_left hprod hkernel0
    have hsecond :
        evenRankEndpointPartialKernel N z.1 z.2 *
              |f z.1 * f z.2| ≤
          (parityUnitCarlemanKernel z.1 z.2 + (1 / 4 : ℝ)) *
              |f z.1 * f z.2| :=
      mul_le_mul_of_nonneg_right hkernel (abs_nonneg _)
    have hyoung :
        (1 / 4 : ℝ) * |f z.1 * f z.2| ≤
          (1 / 8 : ℝ) * (f z.1 ^ 2 + f z.2 ^ 2) := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|f z.1| - |f z.2|),
        sq_abs (f z.1), sq_abs (f z.2)]
    dsimp only [D, M, parityUnitAbsBilinearDensity]
    rw [show evenRankEndpointPartialKernel N z.1 z.2 * f z.1 * f z.2 =
        evenRankEndpointPartialKernel N z.1 z.2 * (f z.1 * f z.2) by ring]
    calc
      _ ≤ evenRankEndpointPartialKernel N z.1 z.2 *
          |f z.1 * f z.2| := hfirst
      _ ≤ (parityUnitCarlemanKernel z.1 z.2 + (1 / 4 : ℝ)) *
          |f z.1 * f z.2| := hsecond
      _ = |f z.1 * f z.2| * parityUnitCarlemanKernel z.1 z.2 +
          (1 / 4 : ℝ) * |f z.1 * f z.2| := by ring
      _ ≤ |f z.1 * f z.2| * parityUnitCarlemanKernel z.1 z.2 +
          (1 / 8 : ℝ) * (f z.1 ^ 2 + f z.2 ^ 2) :=
        add_le_add le_rfl hyoung
  have hmono : (∫ z : ℝ × ℝ, D z ∂μ.prod μ) ≤
      ∫ z : ℝ × ℝ, M z ∂μ.prod μ :=
    integral_mono_ae hD hM hpoint
  have hunitBound := integral_parityUnitAbsBilinearDensity_le f f hf hf
  have hconstantIntegral := integral_evenRankConstantMajorant w hw
  have hconstantEq :
      (∫ z : ℝ × ℝ,
          (1 / 8 : ℝ) * (f z.1 ^ 2 + f z.2 ^ 2) ∂μ.prod μ) =
        (1 / 4 : ℝ) *
          (∫ p : ℝ in 0..1, w (1 - p) ^ 2) := by
    simpa only [f, μ] using hconstantIntegral
  have hhalf := endpoint_half_energy_of_even_or_odd w hw (Or.inl heven)
  have hexact := evenRankPartialSquares_eq_endpointKernel w hw heven N
  change yoshidaEndpointA * _ = ∫ z : ℝ × ℝ, D z ∂μ.prod μ at hexact
  rw [hexact]
  calc
    (∫ z : ℝ × ℝ, D z ∂μ.prod μ) ≤
        ∫ z : ℝ × ℝ, M z ∂μ.prod μ := hmono
    _ = (∫ z : ℝ × ℝ, parityUnitAbsBilinearDensity f f z ∂μ.prod μ) +
        ∫ z : ℝ × ℝ,
          (1 / 8 : ℝ) * (f z.1 ^ 2 + f z.2 ^ 2) ∂μ.prod μ := by
      dsimp only [M]
      rw [integral_add hunit hconstant]
    _ ≤ (Real.pi / 2) *
          ((∫ p : ℝ in 0..1, f p ^ 2) +
            (∫ q : ℝ in 0..1, f q ^ 2)) +
        (1 / 4 : ℝ) *
          (∫ p : ℝ in 0..1, w (1 - p) ^ 2) := by
      rw [hconstantEq]
      simpa only [μ, f] using add_le_add hunitBound le_rfl
    _ = (Real.pi / 2 + 1 / 8 : ℝ) *
        (∫ x : ℝ in -1..1, w x ^ 2) := by
      dsimp only [f]
      rw [hhalf]
      ring

/-- The complete decaying-rank loss obeys the same Schur estimate.  This is
the structural finite-to-infinite passage: the finite bound is closed under
the genuine `HasSum` limit, with no rank cutoff retained in the statement. -/
theorem factorTwoEvenDecayingRankTail_le_schur_energy
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    factorTwoEvenDecayingRankTail w ≤
      (Real.pi / 2 + 1 / 8 : ℝ) *
        (∫ x : ℝ in -1..1, w x ^ 2) := by
  let q : ℕ → ℝ := fun m ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment w
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  let B : ℝ := (Real.pi / 2 + 1 / 8 : ℝ) *
    (∫ x : ℝ in -1..1, w x ^ 2)
  have hsum := hasSum_factorTwoCenteredArch_evenRankSquares w hw heven
  have htend : Tendsto
      (fun N : ℕ ↦ yoshidaEndpointA *
        ∑ m ∈ Finset.range N, q m) atTop
      (nhds (yoshidaEndpointA * ∑' m : ℕ, q m)) := by
    exact hsum.summable.hasSum.tendsto_sum_nat.const_mul yoshidaEndpointA
  have hfinite (N : ℕ) :
      yoshidaEndpointA * (∑ m ∈ Finset.range N, q m) ≤ B := by
    simpa only [q, B] using evenRankPartialSquares_le_schur_energy
      w hw heven N
  have hlimit : yoshidaEndpointA * (∑' m : ℕ, q m) ≤ B :=
    le_of_tendsto' htend hfinite
  simpa only [factorTwoEvenDecayingRankTail, q, B] using hlimit

/-- The Schur tail loss plus the sharp retained-prime mass bound fits
strictly inside three centered energies. -/
theorem evenSchurTail_add_prime_coefficient_lt_three :
    (Real.pi / 2 + 1 / 8 : ℝ) +
        (Real.log 2 / Real.sqrt 2 +
          (Real.log 3 / Real.sqrt 3) / 2) < 3 := by
  have hpi : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
  have htwo : Real.log 2 / Real.sqrt 2 < (1 / 2 : ℝ) :=
    factorTwoDyadicWeight_lt_half
  have hthree : Real.log 3 / Real.sqrt 3 < 1 :=
    factorTwoPrimeThreeWeight_lt_one
  nlinarith

/-- Unconditional directional lower bound for the even symmetric channel.
The complete infinite Schur kernel controls the negative rank tail, and the
existing sharp mass interval controls both retained primes jointly. -/
theorem neg_three_energy_le_even_symmetricPerturbation
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    -(3 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      factorTwoCenteredSymmetricPerturbation w := by
  let E : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let C : ℝ := centeredCoshMoment w (yoshidaEndpointA / 2) ^ 2
  let T : ℝ := ∑' m : ℕ,
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment w
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  let K : ℝ := Real.pi / 2 + 1 / 8
  let R : ℝ := Real.log 2 / Real.sqrt 2 +
    (Real.log 3 / Real.sqrt 3) / 2
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (w x))
  have htail := factorTwoEvenDecayingRankTail_le_schur_energy
    w hw heven
  change yoshidaEndpointA * T ≤ K * E at htail
  have hhead : 0 ≤
      yoshidaEndpointA * Real.exp yoshidaEndpointA * C := by
    exact mul_nonneg
      (mul_nonneg yoshidaEndpointA_pos.le
        (Real.exp_pos yoshidaEndpointA).le)
      (sq_nonneg _)
  have harchEq := factorTwoCenteredArchBlock_eq_evenRankSquares
    w hw heven
  change factorTwoCenteredArchBlock w =
    yoshidaEndpointA * (Real.exp yoshidaEndpointA * C - T) at harchEq
  have harch : -K * E ≤ factorTwoCenteredArchBlock w := by
    rw [harchEq]
    nlinarith
  have hprime := (primeBlock_mass_bounds w hw).2
  change factorTwoCenteredPrimeBlock w ≤ R * E at hprime
  have hcoeff := evenSchurTail_add_prime_coefficient_lt_three
  change K + R < 3 at hcoeff
  rw [symmetricPerturbation_eq_arch_sub_primeBlock]
  change -(3 : ℝ) * E ≤
    factorTwoCenteredArchBlock w - factorTwoCenteredPrimeBlock w
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenSchurClosure
