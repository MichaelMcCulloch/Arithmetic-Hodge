import ArithmeticHodge.Analysis.YoshidaEvenHomogeneousCoercivity
import ArithmeticHodge.Analysis.YoshidaEvenDigammaImagRemainder
import ArithmeticHodge.Analysis.YoshidaEvenPairingEquation
import ArithmeticHodge.Analysis.HermitianFormRieszCorrection

set_option autoImplicit false

noncomputable section

open Complex Filter MeasureTheory Real Set Topology
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace ArithmeticHodge.Analysis.YoshidaEvenTailLowFunctional

open ArithmeticHodge.Analysis
open FormSpace
open YoshidaClippedCircleBridge
open YoshidaClippedCircleFaithful
open YoshidaCoercivityNumerics
open YoshidaEvenCouplingReduction
open YoshidaEvenDigammaImagRemainder
open YoshidaEvenHomogeneousCoercivity
open YoshidaEvenIntervalCertificate
open YoshidaEvenPairingBridge
open YoshidaEvenPairingEquation
open YoshidaEvenTailReduction
open YoshidaOddHomogeneousCoercivity
open YoshidaOddSpectralMassBridge
open YoshidaOddTailPaired
open YoshidaSectionSixAnalytic
open YoshidaWeightedTailBounds

/-!
# The canonical even-tail/low-mode functional

This file closes the actual canonical `200`-mode/even-tail coupling budget
and develops the corresponding production Riesz corrections.
-/

/-- The unconditional source coupling budget for every canonical even low
mode, obtained from the proved sharp digamma remainder and the proved exact
equation-(6.25) pairing identity. -/
theorem evenLowTailCouplingEnergy_le (i : YoshidaEvenIndex) :
    evenLowTailCouplingEnergy yoshidaA yoshidaA_pos i ≤
      (51 / 25000 : ℝ) := by
  apply evenLowTailCouplingEnergy_le_of_decay yoshidaA_pos i
  exact even_low_high_pairing_sq_decay_of_bridges
    actualEvenPairingEquation6_25 sharpDigammaImagRemainder5_11 i

/-- The Lebesgue-normalized cosine coefficient of an actual canonical even-tail
vector at frequency `200 + k`.  The factor `sqrt (4a)` converts the
probability-Haar Fourier coefficient into the coefficient of Yoshida's
Lebesgue-normalized cosine mode. -/
def evenTailCosineCoefficient (f : YoshidaEvenOneNinetyNineTail) (k : ℕ) : ℂ :=
  (((Real.sqrt (4 * yoshidaA) : ℝ) : ℂ)) *
    centeredFourierCoeff yoshidaA_pos
      ((evenOneNinetyNineTailToClippedSmooth f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ)
      ((200 + k : ℕ) : ℤ)

/-- Parseval with the exact cosine-mode normalization: the positive-frequency
even coefficients carry all of the interval energy after multiplication by
`4a`. -/
theorem hasSum_sq_evenTailCosineCoefficient (f : YoshidaEvenOneNinetyNineTail) :
    HasSum (fun k : ℕ ↦ ‖evenTailCosineCoefficient f k‖ ^ 2)
      (clippedIntervalEnergy (evenOneNinetyNineTailToClippedSmooth f)) := by
  have h := hasSum_sq_centeredFourierCoeff_evenTail_positive
    yoshidaA_pos 199
    (f : YoshidaClippedPeriodicCore yoshidaA) f.property
  have hs := h.mul_left (4 * yoshidaA)
  convert hs using 1
  · funext k
    simp only [evenTailCosineCoefficient, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) yoshidaA_pos.le)]
    simp only [evenOneNinetyNineTailToClippedSmooth_apply]
  · unfold clippedIntervalEnergy
    simp only [evenOneNinetyNineTailToClippedSmooth_apply]
    field_simp [yoshidaA_pos.ne']

private theorem normalizedCosineCoefficient_smul_circleMode
    (c : ℂ) (n : ℕ) :
    letI : Fact (0 < 2 * yoshidaA) :=
      ⟨mul_pos (by norm_num) yoshidaA_pos⟩
    ((((Real.sqrt (4 * yoshidaA) : ℝ) : ℂ)) * c) •
        yoshidaEvenMode (T := 2 * yoshidaA) n =
      c • fourierLp (T := 2 * yoshidaA) 2 (n : ℤ) +
        c • fourierLp (T := 2 * yoshidaA) 2 (-(n : ℤ)) := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  have hsqrt : Real.sqrt (4 * yoshidaA) =
      Real.sqrt 2 * Real.sqrt (2 * yoshidaA) := by
    rw [show 4 * yoshidaA = 2 * (2 * yoshidaA) by ring,
      Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrtT : Real.sqrt (2 * yoshidaA) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (by norm_num) yoshidaA_pos)).ne'
  have hsqrta : Real.sqrt yoshidaA ≠ 0 :=
    (Real.sqrt_pos.2 yoshidaA_pos).ne'
  rw [yoshidaEvenMode, hsqrt]
  unfold lebesgueNormalizedExponential
  simp only [smul_add, smul_smul]
  apply congrArg₂ (fun x y ↦ x + y)
  · congr 1
    push_cast
    field_simp [hsqrtTwo, hsqrtT, hsqrta]
  · congr 1
    push_cast
    field_simp [hsqrtTwo, hsqrtT, hsqrta]

/-- The explicit cosine series used below is not a surrogate: after applying
the faithful circle coordinate it converges in `L²` to the given algebraic
tail vector. -/
theorem hasSum_evenTailCosineSeries_circle (f : YoshidaEvenOneNinetyNineTail) :
    letI : Fact (0 < 2 * yoshidaA) :=
      ⟨mul_pos (by norm_num) yoshidaA_pos⟩
    HasSum
      (fun k : ℕ ↦ evenTailCosineCoefficient f k •
        yoshidaEvenMode (T := 2 * yoshidaA) (200 + k))
      (yoshidaClippedCircleL2 yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f)) := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  let F := yoshidaClippedCircleL2 yoshidaA_pos
    (evenOneNinetyNineTailToClippedSmooth f)
  let c : ℤ → ℂ := fun n ↦ centeredFourierCoeff yoshidaA_pos
    ((evenOneNinetyNineTailToClippedSmooth f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) n
  have htail : F ∈ evenFourierTailSubmodule (T := 2 * yoshidaA) 199 :=
    (mem_yoshidaPeriodicCoreEvenTailSubmodule_iff yoshidaA_pos 199
      (f : YoshidaClippedPeriodicCore yoshidaA)).mp f.property
  have heven : F ∈ evenL2Submodule (T := 2 * yoshidaA) := htail.1
  have hzero : F ∈ fourierTailSubmodule (T := 2 * yoshidaA) 199 := htail.2
  have hcneg (n : ℤ) : c (-n) = c n := by
    dsimp only [c, F]
    rw [← fourierCoeff_yoshidaClippedCircleL2 yoshidaA_pos
      (evenOneNinetyNineTailToClippedSmooth f) (-n)]
    rw [← fourierCoeff_yoshidaClippedCircleL2 yoshidaA_pos
      (evenOneNinetyNineTailToClippedSmooth f) n]
    exact fourierCoeff_even_of_mem heven n
  have hc_of_nat_le (n : ℕ) (hn : n ≤ 199) : c (n : ℤ) = 0 := by
    dsimp only [c, F]
    rw [← fourierCoeff_yoshidaClippedCircleL2 yoshidaA_pos
      (evenOneNinetyNineTailToClippedSmooth f) (n : ℤ)]
    exact (mem_fourierTailSubmodule_iff 199 F).mp hzero (n : ℤ) (by
      simp only [Finset.mem_Icc]
      constructor <;> omega)
  have hc0 : c 0 = 0 := by
    simpa using hc_of_nat_le 0 (by omega)
  have hall : HasSum
      (fun n : ℤ ↦ c n • fourierLp (T := 2 * yoshidaA) 2 n) F := by
    simpa only [c, F] using
      hasSum_yoshidaClippedCircleL2_fourier yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f)
  let p : ℕ → CircleL2 (T := 2 * yoshidaA) := fun n ↦
    c (n : ℤ) • fourierLp 2 (n : ℤ) +
      c (-(n : ℤ)) • fourierLp 2 (-(n : ℤ))
  have hpaired : HasSum p F := by
    have hraw := hall.nat_add_neg
    rw [hc0] at hraw
    simp only [zero_smul, add_zero] at hraw
    refine hraw.congr_fun ?_
    intro n
    rfl
  have hhead : ∑ n ∈ Finset.range 200, p n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnle : n ≤ 199 := by
      have := Finset.mem_range.mp hn
      omega
    dsimp only [p]
    rw [hc_of_nat_le n hnle, hcneg, hc_of_nat_le n hnle]
    simp
  have hshift : HasSum (fun k : ℕ ↦ p (k + 200)) F := by
    apply (hasSum_nat_add_iff (f := p) 200).mpr
    rw [hhead, add_zero]
    exact hpaired
  refine hshift.congr_fun ?_
  intro k
  dsimp only [p]
  rw [show k + 200 = 200 + k by omega]
  change
    ((((Real.sqrt (4 * yoshidaA) : ℝ) : ℂ)) *
        c ((200 + k : ℕ) : ℤ)) •
        yoshidaEvenMode (T := 2 * yoshidaA) (200 + k) =
      c ((200 + k : ℕ) : ℤ) • fourierLp 2 ((200 + k : ℕ) : ℤ) +
        c (-((200 + k : ℕ) : ℤ)) • fourierLp 2 (-((200 + k : ℕ) : ℤ))
  rw [hcneg]
  exact normalizedCosineCoefficient_smul_circleMode
    (c ((200 + k : ℕ) : ℤ)) (200 + k)

/-- The certified actual high-mode/low-mode entry, written at the production
half-length used by the even-tail coercivity theorem. -/
def evenTailLowCoupling (i : YoshidaEvenIndex) (k : ℕ) : ℂ :=
  yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
    (yoshidaClippedEvenMode yoshidaA (200 + k))
    (yoshidaClippedEvenLowMode yoshidaA i)

/-- The exact analytic statement missing from the current library: the
actual clipped form pairing is the sum of its normalized high cosine-mode
pairings.  This is deliberately a `HasSum`, not a boundedness assumption or
a renamed target inequality. -/
def EvenTailLowFourierInterchange
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex) : Prop :=
  HasSum
    (fun k : ℕ ↦
      star (evenTailCosineCoefficient f k) * evenTailLowCoupling i k)
    (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
      (evenOneNinetyNineTailToClippedSmooth f)
      (yoshidaClippedEvenLowMode yoshidaA i))

/-- The actual finite cosine partial sum in the clipped smooth carrier. -/
def evenTailCosinePartialSum
    (f : YoshidaEvenOneNinetyNineTail) (N : ℕ) : YoshidaClippedSmooth yoshidaA :=
  ∑ k ∈ Finset.range N,
    evenTailCosineCoefficient f k •
      yoshidaClippedEvenMode yoshidaA (200 + k)

/-- The `k`-th high cosine mode as an element of the periodic source core. -/
def evenHighModePeriodicCore (k : ℕ) :
    YoshidaClippedPeriodicCore yoshidaA :=
  ⟨yoshidaClippedEvenMode yoshidaA (200 + k),
    yoshidaClippedEvenMode_mem_periodicCore yoshidaA_pos (200 + k)⟩

theorem evenHighModePeriodicCore_mem_tail (k : ℕ) :
    evenHighModePeriodicCore k ∈
      yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199 := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  rw [mem_yoshidaPeriodicCoreEvenTailSubmodule_iff]
  change yoshidaClippedCircleL2 yoshidaA_pos
      (yoshidaClippedEvenMode yoshidaA (200 + k)) ∈
    evenFourierTailSubmodule (T := 2 * yoshidaA) 199
  rw [yoshidaClippedCircleL2_evenMode]
  constructor
  · exact yoshidaEvenMode_mem_even (200 + k)
  · change yoshidaEvenMode (T := 2 * yoshidaA) (200 + k) ∈
      fourierTailSubmodule (T := 2 * yoshidaA) 199
    rw [mem_fourierTailSubmodule_iff]
    intro m hm
    simp only [Finset.mem_Icc] at hm
    rw [fourierCoeff_yoshidaEvenMode]
    split_ifs <;> simp_all <;> omega

/-- The finite partial sum packaged in the periodic source core. -/
def evenTailCosinePartialSumPeriodicCore
    (f : YoshidaEvenOneNinetyNineTail) (N : ℕ) :
    YoshidaClippedPeriodicCore yoshidaA :=
  ∑ k ∈ Finset.range N,
    evenTailCosineCoefficient f k • evenHighModePeriodicCore k

@[simp] theorem evenTailCosinePartialSumPeriodicCore_toSmooth
    (f : YoshidaEvenOneNinetyNineTail) (N : ℕ) :
    ((evenTailCosinePartialSumPeriodicCore f N :
        YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) = evenTailCosinePartialSum f N := by
  simp [evenTailCosinePartialSumPeriodicCore, evenTailCosinePartialSum,
    evenHighModePeriodicCore]

theorem evenTailCosinePartialSumPeriodicCore_mem_tail
    (f : YoshidaEvenOneNinetyNineTail) (N : ℕ) :
    evenTailCosinePartialSumPeriodicCore f N ∈
      yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199 := by
  apply Submodule.sum_mem
  intro k _
  exact (yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199).smul_mem
    (evenTailCosineCoefficient f k) (evenHighModePeriodicCore_mem_tail k)

def evenTailCosinePartialSumTail
    (f : YoshidaEvenOneNinetyNineTail) (N : ℕ) : YoshidaEvenOneNinetyNineTail :=
  ⟨evenTailCosinePartialSumPeriodicCore f N,
    evenTailCosinePartialSumPeriodicCore_mem_tail f N⟩

/-- The periodic even-tail remainder whose spectral mass is controlled by the
new Plancherel bridge. -/
def evenTailCosineRemainderPeriodicCore
    (f : YoshidaEvenOneNinetyNineTail) (N : ℕ) :
    YoshidaClippedPeriodicCore yoshidaA :=
  evenTailCosinePartialSumPeriodicCore f N -
    (f : YoshidaClippedPeriodicCore yoshidaA)

theorem evenTailCosineRemainderPeriodicCore_mem_tail
    (f : YoshidaEvenOneNinetyNineTail) (N : ℕ) :
    evenTailCosineRemainderPeriodicCore f N ∈
      yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199 := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  have hp : yoshidaClippedCircleL2 yoshidaA_pos
      ((evenTailCosinePartialSumPeriodicCore f N :
        YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) ∈
      evenFourierTailSubmodule (T := 2 * yoshidaA) 199 :=
    (mem_yoshidaPeriodicCoreEvenTailSubmodule_iff yoshidaA_pos 199
      (evenTailCosinePartialSumPeriodicCore f N)).mp
        (evenTailCosinePartialSumPeriodicCore_mem_tail f N)
  have hf : yoshidaClippedCircleL2 yoshidaA_pos
      ((f : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) ∈
      evenFourierTailSubmodule (T := 2 * yoshidaA) 199 :=
    (mem_yoshidaPeriodicCoreEvenTailSubmodule_iff yoshidaA_pos 199
      (f : YoshidaClippedPeriodicCore yoshidaA)).mp f.property
  rw [mem_yoshidaPeriodicCoreEvenTailSubmodule_iff]
  unfold evenTailCosineRemainderPeriodicCore
  change yoshidaClippedCircleL2Linear yoshidaA_pos
      (((evenTailCosinePartialSumPeriodicCore f N -
        (f : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA)) ∈ _
  rw [show
      (((evenTailCosinePartialSumPeriodicCore f N -
        (f : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA)) =
      ((evenTailCosinePartialSumPeriodicCore f N :
          YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) -
      ((f : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) by
        exact Submodule.coe_sub
          (yoshidaClippedPeriodicCoreSubmodule yoshidaA)
          (evenTailCosinePartialSumPeriodicCore f N)
          (f : YoshidaClippedPeriodicCore yoshidaA), map_sub]
  exact (evenFourierTailSubmodule (T := 2 * yoshidaA) 199).sub_mem hp hf

@[simp] theorem evenTailCosineRemainderPeriodicCore_toSmooth
    (f : YoshidaEvenOneNinetyNineTail) (N : ℕ) :
    ((evenTailCosineRemainderPeriodicCore f N :
        YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) =
      evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f := by
  simp [evenTailCosineRemainderPeriodicCore]

theorem evenTailCosinePartialSum_circle
    (f : YoshidaEvenOneNinetyNineTail) (N : ℕ) :
    letI : Fact (0 < 2 * yoshidaA) :=
      ⟨mul_pos (by norm_num) yoshidaA_pos⟩
    yoshidaClippedCircleL2 yoshidaA_pos
        (evenTailCosinePartialSum f N) =
      ∑ k ∈ Finset.range N,
        evenTailCosineCoefficient f k •
          yoshidaEvenMode (T := 2 * yoshidaA) (200 + k) := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  change yoshidaClippedCircleL2Linear yoshidaA_pos
      (evenTailCosinePartialSum f N) = _
  simp only [evenTailCosinePartialSum, map_sum, map_smul,
    yoshidaClippedCircleL2Linear_apply,
    yoshidaClippedCircleL2_evenMode]

/-- These are genuine Fourier partial sums of the tail: their faithful
circle coordinates converge in `L²` to the original vector. -/
theorem evenTailCosinePartialSum_circle_tendsto
    (f : YoshidaEvenOneNinetyNineTail) :
    letI : Fact (0 < 2 * yoshidaA) :=
      ⟨mul_pos (by norm_num) yoshidaA_pos⟩
    Tendsto
      (fun N : ℕ ↦ yoshidaClippedCircleL2 yoshidaA_pos
        (evenTailCosinePartialSum f N))
      atTop
      (𝓝 (yoshidaClippedCircleL2 yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f))) := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  have h := (hasSum_evenTailCosineSeries_circle f).tendsto_sum_nat
  simpa only [evenTailCosinePartialSum_circle] using h

/-- Convergence in norm, recorded explicitly so the remaining analytic
obligation cannot conceal a missing Fourier-convergence step. -/
theorem evenTailCosinePartialSum_circle_remainder_tendsto_zero
    (f : YoshidaEvenOneNinetyNineTail) :
    letI : Fact (0 < 2 * yoshidaA) :=
      ⟨mul_pos (by norm_num) yoshidaA_pos⟩
    Tendsto
      (fun N : ℕ ↦
        ‖yoshidaClippedCircleL2 yoshidaA_pos
            (evenOneNinetyNineTailToClippedSmooth f) -
          yoshidaClippedCircleL2 yoshidaA_pos
            (evenTailCosinePartialSum f N)‖)
      atTop (𝓝 0) := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  have hconst : Tendsto
      (fun _ : ℕ ↦ yoshidaClippedCircleL2 yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f)) atTop
      (𝓝 (yoshidaClippedCircleL2 yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f))) := tendsto_const_nhds
  have hsub := hconst.sub (evenTailCosinePartialSum_circle_tendsto f)
  simpa using tendsto_norm.comp hsub

/-- Cauchy--Schwarz for any centered Laplace sample on a clipped interval.
This is the bounded `L²` input used to discharge both polar terms below. -/
private theorem normSq_centeredLaplace_le_weight_mul_energy
    {a : ℝ} (ha : 0 < a) (z : ℂ) (f : YoshidaClippedSmooth a) :
    Complex.normSq (yoshidaCenteredLaplaceLinear a ha z f) ≤
      (∫ x : ℝ in -a..a,
        ‖Complex.exp (-(z * (x : ℂ)))‖ ^ 2) *
      (∫ x : ℝ in -a..a, ‖f x‖ ^ 2) := by
  let I : Set ℝ := Set.Ioc (-a) a
  let μ : Measure ℝ := volume.restrict I
  let w : ℝ → ℂ := fun x ↦ Complex.exp (-(z * (x : ℂ)))
  have hwMeas : AEStronglyMeasurable w μ := by
    exact (by fun_prop : Continuous w).aestronglyMeasurable.restrict
  have hw : MemLp w 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hwMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖w x‖ ^ 2)
        (Set.Icc (-a) a) :=
      (by fun_prop : Continuous (fun x : ℝ ↦ ‖w x‖ ^ 2))
        |>.continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hf : MemLp (fun x : ℝ ↦ f x) 2 μ := by
    simpa only [μ, I] using yoshidaClippedSmooth_memLp_two f
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := 2) (q := 2) (f := w) (g := fun x : ℝ ↦ f x) (μ := μ)
    Real.HolderConjugate.two_two (by simpa using hw) (by simpa using hf)
  have hA0 : 0 ≤ ∫ x : ℝ, ‖w x‖ ^ 2 ∂μ :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hB0 : 0 ≤ ∫ x : ℝ, ‖f x‖ ^ 2 ∂μ :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hholder' :
      (∫ x : ℝ, ‖w x‖ * ‖f x‖ ∂μ) ≤
        Real.sqrt (∫ x : ℝ, ‖w x‖ ^ 2 ∂μ) *
          Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    simpa only [Real.rpow_two] using hholder
  have hnorm :
      ‖∫ x : ℝ in -a..a, w x * f x‖ ≤
        ∫ x : ℝ, ‖w x‖ * ‖f x‖ ∂μ := by
    calc
      ‖∫ x : ℝ in -a..a, w x * f x‖ ≤
          ∫ x : ℝ in -a..a, ‖w x * f x‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ = ∫ x : ℝ in -a..a, ‖w x‖ * ‖f x‖ := by
        apply intervalIntegral.integral_congr
        intro x _
        exact norm_mul _ _
      _ = ∫ x : ℝ, ‖w x‖ * ‖f x‖ ∂μ := by
        rw [intervalIntegral.integral_of_le (by linarith)]
  have hbound := hnorm.trans hholder'
  have hsq :
      ‖∫ x : ℝ in -a..a, w x * f x‖ ^ 2 ≤
        (∫ x : ℝ, ‖w x‖ ^ 2 ∂μ) *
          (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) := by
    calc
      ‖∫ x : ℝ in -a..a, w x * f x‖ ^ 2 ≤
          (Real.sqrt (∫ x : ℝ, ‖w x‖ ^ 2 ∂μ) *
            Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hbound
      _ = (∫ x : ℝ, ‖w x‖ ^ 2 ∂μ) *
          (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) := by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  rw [yoshidaCenteredLaplaceLinear_apply,
    Complex.normSq_eq_norm_sq]
  change ‖∫ x : ℝ in -a..a, w x * f x‖ ^ 2 ≤ _
  simpa only [μ, I, w,
    intervalIntegral.integral_of_le (by linarith : -a ≤ a)] using hsq

theorem evenTailCosinePartialSum_energy_remainder_tendsto_zero
    (f : YoshidaEvenOneNinetyNineTail) :
    Tendsto
      (fun N : ℕ ↦ clippedIntervalEnergy
        (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f))
      atTop (𝓝 0) := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  have hnorm : Tendsto
      (fun N : ℕ ↦
        ‖yoshidaClippedCircleL2 yoshidaA_pos
            (evenTailCosinePartialSum f N) -
          yoshidaClippedCircleL2 yoshidaA_pos
            (evenOneNinetyNineTailToClippedSmooth f)‖)
      atTop (𝓝 0) := by
    simpa only [norm_sub_rev] using
      evenTailCosinePartialSum_circle_remainder_tendsto_zero f
  have hscaled :=
    (tendsto_const_nhds.mul (hnorm.pow 2) :
      Tendsto
        (fun N : ℕ ↦ (2 * yoshidaA) *
          ‖yoshidaClippedCircleL2 yoshidaA_pos
              (evenTailCosinePartialSum f N) -
            yoshidaClippedCircleL2 yoshidaA_pos
              (evenOneNinetyNineTailToClippedSmooth f)‖ ^ 2)
        atTop (𝓝 ((2 * yoshidaA) * 0 ^ 2)))
  convert hscaled using 1
  · funext N
    unfold clippedIntervalEnergy
    rw [← lebesgueNormSq_yoshidaClippedCircleL2 yoshidaA_pos
      (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f)]
    unfold lebesgueNormSq
    change (2 * yoshidaA) *
      ‖yoshidaClippedCircleL2Linear yoshidaA_pos
        (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f)‖ ^ 2 = _
    rw [map_sub]
    rfl
  · norm_num

/-- Every fixed centered Laplace sample is continuous along the explicit
Fourier partial sums.  In particular this discharges both polar samples of
the production form without assuming boundedness of the full form. -/
theorem centeredLaplace_evenTailCosinePartialSum_tendsto
    (f : YoshidaEvenOneNinetyNineTail) (z : ℂ) :
    Tendsto
      (fun N : ℕ ↦ yoshidaCenteredLaplaceLinear yoshidaA yoshidaA_pos z
        (evenTailCosinePartialSum f N))
      atTop
      (𝓝 (yoshidaCenteredLaplaceLinear yoshidaA yoshidaA_pos z
        (evenOneNinetyNineTailToClippedSmooth f))) := by
  let W : ℝ := ∫ x : ℝ in -yoshidaA..yoshidaA,
    ‖Complex.exp (-(z * (x : ℂ)))‖ ^ 2
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact intervalIntegral.integral_nonneg
      (by linarith [yoshidaA_pos]) (fun _ _ ↦ sq_nonneg _)
  have hsqBound (N : ℕ) :
      Complex.normSq
          (yoshidaCenteredLaplaceLinear yoshidaA yoshidaA_pos z
            (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f)) ≤
        W * clippedIntervalEnergy
          (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f) := by
    simpa only [W, clippedIntervalEnergy] using
      normSq_centeredLaplace_le_weight_mul_energy yoshidaA_pos z
        (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f)
  have hrhs : Tendsto
      (fun N : ℕ ↦ W * clippedIntervalEnergy
        (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f))
      atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul
      (evenTailCosinePartialSum_energy_remainder_tendsto_zero f) using 1
    norm_num
  have hnormSq : Tendsto
      (fun N : ℕ ↦ Complex.normSq
        (yoshidaCenteredLaplaceLinear yoshidaA yoshidaA_pos z
          (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f)))
      atTop (𝓝 0) :=
    squeeze_zero (fun N ↦ Complex.normSq_nonneg _) hsqBound hrhs
  have hnorm : Tendsto
      (fun N : ℕ ↦
        ‖yoshidaCenteredLaplaceLinear yoshidaA yoshidaA_pos z
          (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f)‖)
      atTop (𝓝 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hnormSq
    simpa only [Function.comp_def, Complex.normSq_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  have hdiff : Tendsto
      (fun N : ℕ ↦
        yoshidaCenteredLaplaceLinear yoshidaA yoshidaA_pos z
          (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f))
      atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hnorm
  apply tendsto_sub_nhds_zero_iff.mp
  simpa only [map_sub] using hdiff

theorem positivePolar_evenTailCosinePartialSum_tendsto
    (f : YoshidaEvenOneNinetyNineTail) :
    Tendsto
      (fun N : ℕ ↦ yoshidaPositivePolarLinear yoshidaA yoshidaA_pos
        (evenTailCosinePartialSum f N))
      atTop
      (𝓝 (yoshidaPositivePolarLinear yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f))) := by
  simpa only [yoshidaPositivePolarLinear] using
    centeredLaplace_evenTailCosinePartialSum_tendsto f (1 / 2 : ℂ)

theorem negativePolar_evenTailCosinePartialSum_tendsto
    (f : YoshidaEvenOneNinetyNineTail) :
    Tendsto
      (fun N : ℕ ↦ yoshidaNegativePolarLinear yoshidaA yoshidaA_pos
        (evenTailCosinePartialSum f N))
      atTop
      (𝓝 (yoshidaNegativePolarLinear yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f))) := by
  simpa only [yoshidaNegativePolarLinear] using
    centeredLaplace_evenTailCosinePartialSum_tendsto f (-1 / 2 : ℂ)

private theorem continuous_criticalSample
    {a : ℝ} (ha : 0 < a) (g : YoshidaClippedSmooth a) :
    Continuous (fun v : ℝ ↦ yoshidaCriticalSampleLinear a ha v g) := by
  have hgint : Integrable (g : ℝ → ℂ) :=
    g.property.1.continuousOn.integrableOn_Icc
      |>.integrable_of_forall_notMem_eq_zero
        (fun x hx ↦ yoshidaClippedSmooth_eq_zero_outside g hx)
  have hfourier : Continuous (FourierTransform.fourier (g : ℝ → ℂ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hgint
  have heq : (fun v : ℝ ↦ yoshidaCriticalSampleLinear a ha v g) =
      fun v : ℝ ↦ FourierTransform.fourier (g : ℝ → ℂ)
        (v / (2 * Real.pi)) := by
    funext v
    exact yoshidaCriticalSample_eq_fourier ha v g
  rw [heq]
  exact hfourier.comp (by fun_prop)

private theorem integrable_max_one_abs_rpow_neg_three_halves :
    Integrable (fun v : ℝ ↦
      (max 1 |v|) ^ (-(3 / 2 : ℝ))) := by
  let r : ℝ := 3 / 2
  have hr : (1 : ℝ) < r := by norm_num [r]
  have hbase : Integrable (fun v : ℝ ↦
      (1 + ‖v‖) ^ (-r)) :=
    integrable_one_add_norm (E := ℝ) (r := r) (by simpa using hr)
  have hmajor := hbase.const_mul (2 ^ r)
  apply hmajor.mono'
  · exact ((continuous_const.max continuous_abs).rpow_const
      (fun v ↦ Or.inl (ne_of_gt
        (lt_of_lt_of_le zero_lt_one (le_max_left 1 |v|)))))
      |>.aestronglyMeasurable
  · filter_upwards with v
    let m : ℝ := max 1 |v|
    have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one (le_max_left 1 |v|)
    have hcompare : 1 + |v| ≤ 2 * m := by
      dsimp [m]
      nlinarith [le_max_left (1 : ℝ) |v|, le_max_right (1 : ℝ) |v|]
    have hneg : -r ≤ 0 := by norm_num [r]
    have hrpow : (2 * m) ^ (-r) ≤ (1 + |v|) ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hcompare hneg
    have heq : m ^ (-r) = 2 ^ r * (2 * m) ^ (-r) := by
      rw [Real.mul_rpow (by positivity) hmpos.le]
      rw [← mul_assoc, ← Real.rpow_add zero_lt_two]
      norm_num
    rw [Real.norm_eq_abs]
    change |m ^ (-r)| ≤ 2 ^ r * (1 + |v|) ^ (-r)
    rw [abs_of_nonneg (Real.rpow_nonneg hmpos.le _), heq]
    exact mul_le_mul_of_nonneg_left hrpow
      (Real.rpow_nonneg (by positivity) _)

/-- The fixed low-mode spectral factor multiplying the variable tail sample
in the critical cross integral. -/
def evenLowCriticalWeight (i : YoshidaEvenIndex) (v : ℝ) : ℂ :=
  MultiplicativeWeil.bombieriLocalCriticalKernel v *
    yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v
      (yoshidaClippedEvenLowMode yoshidaA i)

private theorem evenLowCriticalWeight_norm_sq_le_tail
    {C : ℝ} (hC : 0 ≤ C)
    (hkernel : ∀ v : ℝ,
      ‖MultiplicativeWeil.bombieriLocalCriticalKernel v‖ ≤
        C * (1 + Real.log (max 1 |v|)))
    (i : YoshidaEvenIndex) {v : ℝ}
    (hv : v ∉ Set.Icc (-1 : ℝ) 1) :
    ‖evenLowCriticalWeight i v‖ ^ 2 ≤
      (25 * C ^ 2 *
        yoshidaCriticalDecayConstant yoshidaA
          (yoshidaClippedEvenLowMode yoshidaA i) ^ 2) *
        (max 1 |v|) ^ (-(3 / 2 : ℝ)) := by
  have habs : 1 < |v| := by
    by_contra h
    apply hv
    exact abs_le.mp (le_of_not_gt h)
  have hvne : v ≠ 0 := abs_pos.mp (zero_lt_one.trans habs)
  have hmax : max 1 |v| = |v| := max_eq_right habs.le
  let D : ℝ := yoshidaCriticalDecayConstant yoshidaA
    (yoshidaClippedEvenLowMode yoshidaA i)
  have hD : 0 ≤ D :=
    yoshidaCriticalDecayConstant_nonneg yoshidaA_pos _
  have hs := yoshidaCriticalSample_norm_le_inv_abs
    yoshidaA_pos v hvne (yoshidaClippedEvenLowMode yoshidaA i)
  have hk := hkernel v
  rw [hmax] at hk
  have hlog := Real.log_le_rpow_div (x := |v|) (abs_nonneg v)
    (show 0 < (1 / 4 : ℝ) by norm_num)
  have hrpowOne : 1 ≤ |v| ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow habs.le (by norm_num)
  have hlog' : Real.log |v| ≤ 4 * |v| ^ (1 / 4 : ℝ) := by
    calc
      Real.log |v| ≤ |v| ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) := hlog
      _ = 4 * |v| ^ (1 / 4 : ℝ) := by ring
  have hkernel' :
      ‖MultiplicativeWeil.bombieriLocalCriticalKernel v‖ ≤
        5 * C * |v| ^ (1 / 4 : ℝ) := by
    calc
      ‖MultiplicativeWeil.bombieriLocalCriticalKernel v‖ ≤
          C * (1 + Real.log |v|) := hk
      _ ≤ C * (5 * |v| ^ (1 / 4 : ℝ)) := by
        gcongr
        nlinarith
      _ = 5 * C * |v| ^ (1 / 4 : ℝ) := by ring
  have hweight : ‖evenLowCriticalWeight i v‖ ≤
      (5 * C * |v| ^ (1 / 4 : ℝ)) * (D / |v|) := by
    rw [evenLowCriticalWeight, norm_mul]
    exact mul_le_mul hkernel' hs (norm_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) hC)
        (Real.rpow_nonneg (abs_nonneg v) _))
  have hrhs0 : 0 ≤
      (5 * C * |v| ^ (1 / 4 : ℝ)) * (D / |v|) := by positivity
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hweight 2
  have hrpow :
      (|v| ^ (1 / 4 : ℝ)) ^ 2 / |v| ^ 2 =
        |v| ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg v),
      ← Real.rpow_natCast, ← Real.rpow_sub (abs_pos.mpr hvne)]
    congr 1
    norm_num
  rw [hmax]
  dsimp only [D] at hsq ⊢
  calc
    ‖evenLowCriticalWeight i v‖ ^ 2 ≤
        ((5 * C * |v| ^ (1 / 4 : ℝ)) *
          (yoshidaCriticalDecayConstant yoshidaA
            (yoshidaClippedEvenLowMode yoshidaA i) / |v|)) ^ 2 := hsq
    _ = (25 * C ^ 2 *
        yoshidaCriticalDecayConstant yoshidaA
          (yoshidaClippedEvenLowMode yoshidaA i) ^ 2) *
        ((|v| ^ (1 / 4 : ℝ)) ^ 2 / |v| ^ 2) := by ring
    _ = _ := by rw [hrpow]

theorem integrable_norm_sq_evenLowCriticalWeight (i : YoshidaEvenIndex) :
    Integrable (fun v : ℝ ↦ ‖evenLowCriticalWeight i v‖ ^ 2) := by
  obtain ⟨C, hCpos, hkernel⟩ :=
    exists_bombieriLocalCriticalKernel_log_norm_bound
  let K : ℝ := 25 * C ^ 2 *
    yoshidaCriticalDecayConstant yoshidaA
      (yoshidaClippedEvenLowMode yoshidaA i) ^ 2
  let q : ℝ → ℝ := fun v ↦ (max 1 |v|) ^ (-(3 / 2 : ℝ))
  let S : Set ℝ := Set.Icc (-1 : ℝ) 1
  have hcontinuous : Continuous (fun v : ℝ ↦
      ‖evenLowCriticalWeight i v‖ ^ 2) := by
    exact ((continuous_bombieriLocalCriticalKernel.mul
      (continuous_criticalSample yoshidaA_pos
        (yoshidaClippedEvenLowMode yoshidaA i))).norm.pow 2)
  have hcompact : IntegrableOn
      (fun v : ℝ ↦ ‖evenLowCriticalWeight i v‖ ^ 2) S :=
    hcontinuous.continuousOn.integrableOn_compact isCompact_Icc
  have hq : Integrable q := by
    simpa only [q] using integrable_max_one_abs_rpow_neg_three_halves
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hmajor : Integrable (fun v ↦ K * q v) := hq.const_mul K
  have htail : IntegrableOn
      (fun v : ℝ ↦ ‖evenLowCriticalWeight i v‖ ^ 2) Sᶜ := by
    apply hmajor.integrableOn.mono'
    · exact hcontinuous.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
      rw [Real.norm_of_nonneg (sq_nonneg ‖evenLowCriticalWeight i v‖)]
      simpa only [K, q] using
        evenLowCriticalWeight_norm_sq_le_tail hCpos.le hkernel i hv
  rw [← integrableOn_univ]
  simpa only [S, union_compl_self] using hcompact.union htail

theorem clippedSpectralMass_evenTailCosineRemainder_eq_energy
    (f : YoshidaEvenOneNinetyNineTail) (N : ℕ) :
    clippedSpectralMass yoshidaA yoshidaA_pos
        (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f) =
      clippedIntervalEnergy
        (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f) := by
  simpa only [clippedIntervalEnergy] using
    (clippedSpectralMass_eq_intervalEnergy yoshidaA_pos
      (evenTailCosinePartialSum f N -
        evenOneNinetyNineTailToClippedSmooth f))

theorem integral_normSq_criticalSample_evenTailCosineRemainder
    (f : YoshidaEvenOneNinetyNineTail) (N : ℕ) :
    (∫ v : ℝ, Complex.normSq
      (yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v
        (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f))) =
      (2 * Real.pi) * clippedIntervalEnergy
        (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f) := by
  have h := clippedSpectralMass_evenTailCosineRemainder_eq_energy f N
  unfold clippedSpectralMass at h
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  calc
    (∫ v : ℝ, Complex.normSq
      (yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v
        (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f))) =
      (2 * Real.pi) *
        ((1 / (2 * Real.pi)) *
          ∫ v : ℝ, Complex.normSq
            (yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v
              (evenTailCosinePartialSum f N -
                evenOneNinetyNineTailToClippedSmooth f))) := by
          field_simp
    _ = _ := by rw [h]

/-- Spectral Cauchy--Schwarz against the fixed low-mode kernel factor. -/
theorem norm_sq_integral_criticalCross_le
    (g : YoshidaClippedSmooth yoshidaA) (i : YoshidaEvenIndex) :
    ‖∫ v : ℝ,
      yoshidaClippedCriticalCrossIntegrand yoshidaA yoshidaA_pos g
        (yoshidaClippedEvenLowMode yoshidaA i) v‖ ^ 2 ≤
      (∫ v : ℝ, Complex.normSq
        (yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v g)) *
      (∫ v : ℝ, ‖evenLowCriticalWeight i v‖ ^ 2) := by
  let u : ℝ → ℂ := fun v ↦
    yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v g
  let w : ℝ → ℂ := evenLowCriticalWeight i
  have huMeas : AEStronglyMeasurable u :=
    (continuous_criticalSample yoshidaA_pos g).aestronglyMeasurable
  have hwMeas : AEStronglyMeasurable w := by
    exact (continuous_bombieriLocalCriticalKernel.mul
      (continuous_criticalSample yoshidaA_pos
        (yoshidaClippedEvenLowMode yoshidaA i))).aestronglyMeasurable
  have hu : MemLp u 2 := by
    rw [memLp_two_iff_integrable_sq_norm huMeas]
    simpa only [u, Complex.normSq_eq_norm_sq] using
      integrable_normSq_yoshidaCriticalSample yoshidaA_pos g
  have hw : MemLp w 2 := by
    rw [memLp_two_iff_integrable_sq_norm hwMeas]
    simpa only [w] using integrable_norm_sq_evenLowCriticalWeight i
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := 2) (q := 2) (f := u) (g := w)
    Real.HolderConjugate.two_two (by simpa using hu) (by simpa using hw)
  have hA0 : 0 ≤ ∫ v : ℝ, ‖u v‖ ^ 2 :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hB0 : 0 ≤ ∫ v : ℝ, ‖w v‖ ^ 2 :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hholder' :
      (∫ v : ℝ, ‖u v‖ * ‖w v‖) ≤
        Real.sqrt (∫ v : ℝ, ‖u v‖ ^ 2) *
          Real.sqrt (∫ v : ℝ, ‖w v‖ ^ 2) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    simpa only [Real.rpow_two] using hholder
  have hnorm :
      ‖∫ v : ℝ,
        yoshidaClippedCriticalCrossIntegrand yoshidaA yoshidaA_pos g
          (yoshidaClippedEvenLowMode yoshidaA i) v‖ ≤
        ∫ v : ℝ, ‖u v‖ * ‖w v‖ := by
    calc
      ‖∫ v : ℝ,
        yoshidaClippedCriticalCrossIntegrand yoshidaA yoshidaA_pos g
          (yoshidaClippedEvenLowMode yoshidaA i) v‖ ≤
          ∫ v : ℝ,
            ‖yoshidaClippedCriticalCrossIntegrand yoshidaA yoshidaA_pos g
              (yoshidaClippedEvenLowMode yoshidaA i) v‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ v : ℝ, ‖u v‖ * ‖w v‖ := by
        apply integral_congr_ae
        filter_upwards with v
        simp only [yoshidaClippedCriticalCrossIntegrand,
          evenLowCriticalWeight, u, w, norm_mul, norm_star]
        ring
  have hbound := hnorm.trans hholder'
  calc
    ‖∫ v : ℝ,
      yoshidaClippedCriticalCrossIntegrand yoshidaA yoshidaA_pos g
        (yoshidaClippedEvenLowMode yoshidaA i) v‖ ^ 2 ≤
        (Real.sqrt (∫ v : ℝ, ‖u v‖ ^ 2) *
          Real.sqrt (∫ v : ℝ, ‖w v‖ ^ 2)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hbound
    _ = (∫ v : ℝ, ‖u v‖ ^ 2) *
        (∫ v : ℝ, ‖w v‖ ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    _ = _ := by
      simp only [u, w, Complex.normSq_eq_norm_sq]

theorem integral_criticalCross_evenTailCosineRemainder_tendsto_zero
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex) :
    Tendsto
      (fun N : ℕ ↦ ∫ v : ℝ,
        yoshidaClippedCriticalCrossIntegrand yoshidaA yoshidaA_pos
          (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f)
          (yoshidaClippedEvenLowMode yoshidaA i) v)
      atTop (𝓝 0) := by
  let B : ℝ := ∫ v : ℝ, ‖evenLowCriticalWeight i v‖ ^ 2
  have hB : 0 ≤ B := integral_nonneg fun _ ↦ sq_nonneg _
  have hmass : Tendsto
      (fun N : ℕ ↦ ∫ v : ℝ, Complex.normSq
        (yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v
          (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f)))
      atTop (𝓝 0) := by
    have hscaled : Tendsto
        (fun N : ℕ ↦ (2 * Real.pi) * clippedIntervalEnergy
          (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f))
        atTop (𝓝 0) := by
      convert (tendsto_const_nhds.mul
        (evenTailCosinePartialSum_energy_remainder_tendsto_zero f) :
        Tendsto
          (fun N : ℕ ↦ (2 * Real.pi) * clippedIntervalEnergy
            (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f))
          atTop (𝓝 ((2 * Real.pi) * 0))) using 1
      norm_num
    convert hscaled using 1
    · funext N
      exact integral_normSq_criticalSample_evenTailCosineRemainder f N
  have hrhs : Tendsto
      (fun N : ℕ ↦
        (∫ v : ℝ, Complex.normSq
          (yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v
            (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f))) * B)
      atTop (𝓝 0) := by
    convert hmass.mul_const B using 1
    norm_num
  have hsqBound (N : ℕ) :
      ‖∫ v : ℝ,
        yoshidaClippedCriticalCrossIntegrand yoshidaA yoshidaA_pos
          (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f)
          (yoshidaClippedEvenLowMode yoshidaA i) v‖ ^ 2 ≤
        (∫ v : ℝ, Complex.normSq
          (yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v
            (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f))) * B := by
    simpa only [B] using norm_sq_integral_criticalCross_le
      (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f) i
  have hnormSq : Tendsto
      (fun N : ℕ ↦
        ‖∫ v : ℝ,
          yoshidaClippedCriticalCrossIntegrand yoshidaA yoshidaA_pos
            (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f)
            (yoshidaClippedEvenLowMode yoshidaA i) v‖ ^ 2)
      atTop (𝓝 0) :=
    squeeze_zero (fun N ↦ sq_nonneg _) hsqBound hrhs
  have hnorm : Tendsto
      (fun N : ℕ ↦
        ‖∫ v : ℝ,
          yoshidaClippedCriticalCrossIntegrand yoshidaA yoshidaA_pos
            (evenTailCosinePartialSum f N - evenOneNinetyNineTailToClippedSmooth f)
            (yoshidaClippedEvenLowMode yoshidaA i) v‖)
      atTop (𝓝 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hnormSq
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_zero] using hsqrt
  exact (tendsto_zero_iff_norm_tendsto_zero).2 hnorm

/-- After the polar terms have been discharged, the remaining analytic
interchange is convergence of the digamma-weighted critical cross integral
against one fixed low mode. -/
def EvenTailLowCriticalCrossIntegralContinuity
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex) : Prop :=
  Tendsto
    (fun N : ℕ ↦ ∫ v : ℝ,
      yoshidaClippedCriticalCrossIntegrand yoshidaA yoshidaA_pos
        (evenTailCosinePartialSum f N)
        (yoshidaClippedEvenLowMode yoshidaA i) v)
    atTop
    (𝓝 (∫ v : ℝ,
      yoshidaClippedCriticalCrossIntegrand yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f)
        (yoshidaClippedEvenLowMode yoshidaA i) v))

theorem evenTailLowCriticalCrossIntegralContinuity
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex) :
    EvenTailLowCriticalCrossIntegralContinuity f i := by
  have hrem :=
    integral_criticalCross_evenTailCosineRemainder_tendsto_zero f i
  apply tendsto_sub_nhds_zero_iff.mp
  convert hrem using 1
  funext N
  rw [← integral_sub
    (yoshidaClippedCriticalCrossIntegrand_integrable yoshidaA_pos
      (evenTailCosinePartialSum f N)
      (yoshidaClippedEvenLowMode yoshidaA i))
    (yoshidaClippedCriticalCrossIntegrand_integrable yoshidaA_pos
      (evenOneNinetyNineTailToClippedSmooth f)
      (yoshidaClippedEvenLowMode yoshidaA i))]
  apply integral_congr_ae
  filter_upwards with v
  simp only [yoshidaClippedCriticalCrossIntegrand, map_sub, star_sub]
  ring

/-- Continuity of the full production pairing along the explicit Fourier
partial sums.  The theorem below reduces this to the critical cross integral
alone. -/
def EvenTailLowFormContinuityAlongFourier
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex) : Prop :=
  Tendsto
    (fun N : ℕ ↦
      yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenTailCosinePartialSum f N)
        (yoshidaClippedEvenLowMode yoshidaA i))
    atTop
    (𝓝 (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
      (evenOneNinetyNineTailToClippedSmooth f)
      (yoshidaClippedEvenLowMode yoshidaA i)))

theorem evenTailLowFormContinuityAlongFourier_of_criticalCross
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex)
    (hcritical : EvenTailLowCriticalCrossIntegralContinuity f i) :
    EvenTailLowFormContinuityAlongFourier f i := by
  have hpos := (positivePolar_evenTailCosinePartialSum_tendsto f).star.mul_const
    (yoshidaNegativePolarLinear yoshidaA yoshidaA_pos
      (yoshidaClippedEvenLowMode yoshidaA i))
  have hneg := (negativePolar_evenTailCosinePartialSum_tendsto f).star.mul_const
    (yoshidaPositivePolarLinear yoshidaA yoshidaA_pos
      (yoshidaClippedEvenLowMode yoshidaA i))
  have hcross := hcritical.const_mul
    ((((1 / (2 * Real.pi) : ℝ) : ℂ)))
  have htotal := (hpos.add hneg).add hcross
  simpa only [EvenTailLowFormContinuityAlongFourier,
    yoshidaClippedLocalCriticalForm_apply,
    yoshidaClippedLocalCriticalPairing] using htotal

/-- Conjugate-linearity gives the exact finite identity before any limiting
argument. -/
theorem evenTailLowForm_partialSum
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex) (N : ℕ) :
    yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenTailCosinePartialSum f N)
        (yoshidaClippedEvenLowMode yoshidaA i) =
      ∑ k ∈ Finset.range N,
        star (evenTailCosineCoefficient f k) *
          evenTailLowCoupling i k := by
  unfold evenTailCosinePartialSum
  rw [map_sum]
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [LinearMap.map_smulₛₗ₂]
  rfl

/-- The certified pointwise decay implies genuine summability of the actual
coupling sequence.  This matters because a bare `tsum` would otherwise be
zero by convention in the nonsummable case. -/
theorem summable_sq_evenTailLowCoupling (i : YoshidaEvenIndex) :
    Summable (fun k : ℕ ↦ ‖evenTailLowCoupling i k‖ ^ 2) := by
  let major : ℕ → ℝ := fun k ↦
    (10149 / 25000 : ℝ) / (((200 + k : ℕ) : ℝ) ^ 2)
  have hs : Summable (fun k : ℕ ↦
      1 / (((200 + k : ℕ) : ℝ) ^ 2)) := by
    have h : Summable
        (fun k : ℕ ↦ 1 / |(k : ℝ) + 200| ^ (2 : ℝ)) :=
      (Real.summable_one_div_nat_add_rpow 200 2).mpr (by norm_num)
    convert h using 1
    funext k
    rw [Real.rpow_two, sq_abs]
    push_cast
    ring
  have hmajor : Summable major := by
    convert hs.mul_left (10149 / 25000 : ℝ) using 1
    funext k
    norm_num [major, div_eq_mul_inv]
  apply hmajor.of_nonneg_of_le
  · intro k
    exact sq_nonneg _
  · intro k
    have hdecay := even_low_high_pairing_sq_decay_of_bridges
      actualEvenPairingEquation6_25 sharpDigammaImagRemainder5_11 i k
    calc
      ‖evenTailLowCoupling i k‖ ^ 2 =
          ‖yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (yoshidaClippedEvenLowMode yoshidaA i)
            (yoshidaClippedEvenMode yoshidaA (200 + k))‖ ^ 2 := by
        unfold evenTailLowCoupling
        rw [← yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos]
        simp only [norm_star]
      _ = ‖yoshidaClippedEvenLowModePairingFormula yoshidaA i
            (200 + k)‖ ^ 2 := by
        rw [yoshidaClippedLocalCriticalForm_evenLowMode_tail_eq_formula]
      _ ≤ major k := by
        simpa only [major] using hdecay

theorem hasSum_sq_evenTailLowCoupling (i : YoshidaEvenIndex) :
    HasSum (fun k : ℕ ↦ ‖evenTailLowCoupling i k‖ ^ 2)
      (evenLowTailCouplingEnergy yoshidaA yoshidaA_pos i) := by
  have h := (summable_sq_evenTailLowCoupling i).hasSum
  convert h using 1
  unfold evenLowTailCouplingEnergy
  apply tsum_congr
  intro k
  unfold evenTailLowCoupling
  rw [← yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos]
  simp only [norm_star]

/-- The coupling series is absolutely summable by `ℓ2·ℓ2 ⊆ ℓ1`.
This justifies using ordinary natural partial sums in the final limit. -/
theorem summable_norm_evenTailLowFourierSeries
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex) :
    Summable (fun k : ℕ ↦
      ‖star (evenTailCosineCoefficient f k) * evenTailLowCoupling i k‖) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  have hu : Summable (fun k : ℕ ↦
      ‖star (evenTailCosineCoefficient f k)‖ ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two, norm_star] using
      (hasSum_sq_evenTailCosineCoefficient f).summable
  have hw : Summable (fun k : ℕ ↦
      ‖evenTailLowCoupling i k‖ ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two] using summable_sq_evenTailLowCoupling i
  have hholder :=
    Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq
      (fun k ↦ norm_nonneg (star (evenTailCosineCoefficient f k)))
      (fun k ↦ norm_nonneg (evenTailLowCoupling i k)) hu hw
  simpa only [norm_mul] using hholder.1

theorem evenTailLowFourierInterchange_of_continuity
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex)
    (hcontinuous : EvenTailLowFormContinuityAlongFourier f i) :
    EvenTailLowFourierInterchange f i := by
  apply (hasSum_iff_tendsto_nat_of_summable_norm
    (summable_norm_evenTailLowFourierSeries f i)).2
  simpa only [EvenTailLowFormContinuityAlongFourier,
    evenTailLowForm_partialSum] using hcontinuous

/-- The production form is continuous along the actual cosine partial sums;
the weighted critical cross integral is controlled by Plancherel and the
fixed low-mode spectral weight. -/
theorem evenTailLowFormContinuityAlongFourier
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex) :
    EvenTailLowFormContinuityAlongFourier f i :=
  evenTailLowFormContinuityAlongFourier_of_criticalCross f i
    (evenTailLowCriticalCrossIntegralContinuity f i)

/-- The make-or-break identity: the actual clipped low/tail pairing equals
the infinite normalized cosine-coefficient pairing. -/
theorem evenTailLowFourierInterchange
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex) :
    EvenTailLowFourierInterchange f i :=
  evenTailLowFourierInterchange_of_continuity f i
    (evenTailLowFormContinuityAlongFourier f i)

/-- Infinite Cauchy--Schwarz for the *actual* clipped pairing, conditional
only on the exact Fourier/form interchange. -/
theorem evenTailLowPairing_sq_le_energy_of_interchange
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex)
    (hinterchange : EvenTailLowFourierInterchange f i) :
    ‖yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f)
        (yoshidaClippedEvenLowMode yoshidaA i)‖ ^ 2 ≤
      clippedIntervalEnergy (evenOneNinetyNineTailToClippedSmooth f) *
        evenLowTailCouplingEnergy yoshidaA yoshidaA_pos i := by
  have hu : HasSum
      (fun k : ℕ ↦ ‖star (evenTailCosineCoefficient f k)‖ ^ 2)
      (clippedIntervalEnergy (evenOneNinetyNineTailToClippedSmooth f)) := by
    simpa only [norm_star] using hasSum_sq_evenTailCosineCoefficient f
  have hw := hasSum_sq_evenTailLowCoupling i
  have hcs := normSq_hasSum_mul_le hinterchange hu hw
  simpa only [Complex.normSq_eq_norm_sq, evenTailLowCoupling] using hcs

/-- The committed `51/25000` coupling budget turns the preceding exact
Parseval estimate into a source-energy bound. -/
theorem evenTailLowPairing_sq_le_sourceEnergy_of_interchange
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex)
    (hinterchange : EvenTailLowFourierInterchange f i) :
    ‖yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f)
        (yoshidaClippedEvenLowMode yoshidaA i)‖ ^ 2 ≤
      (51 / 25000 : ℝ) *
        clippedIntervalEnergy (evenOneNinetyNineTailToClippedSmooth f) := by
  have hraw := evenTailLowPairing_sq_le_energy_of_interchange f i hinterchange
  have hE : 0 ≤ clippedIntervalEnergy (evenOneNinetyNineTailToClippedSmooth f) := by
    unfold clippedIntervalEnergy
    exact intervalIntegral.integral_nonneg
      (by linarith [yoshidaA_pos]) (fun _ _ ↦ sq_nonneg _)
  calc
    ‖yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f)
        (yoshidaClippedEvenLowMode yoshidaA i)‖ ^ 2 ≤
      clippedIntervalEnergy (evenOneNinetyNineTailToClippedSmooth f) *
        evenLowTailCouplingEnergy yoshidaA yoshidaA_pos i := hraw
    _ ≤ clippedIntervalEnergy (evenOneNinetyNineTailToClippedSmooth f) *
        (51 / 25000 : ℝ) :=
      mul_le_mul_of_nonneg_left (evenLowTailCouplingEnergy_le i) hE
    _ = (51 / 25000 : ℝ) *
        clippedIntervalEnergy (evenOneNinetyNineTailToClippedSmooth f) := by ring

/-- The precise bound requested by the form completion: `51/25000` divided by
the proved even-tail coercivity constant `102/25` is exactly `1/2000`. -/
theorem evenTailLowFunctional_sq_le_formNorm_of_interchange
    (x : FormSpace evenOneNinetyNineTailPositiveHermitianForm)
    (i : YoshidaEvenIndex)
    (hinterchange : EvenTailLowFourierInterchange x.toV i) :
    ‖yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth x.toV)
        (yoshidaClippedEvenLowMode yoshidaA i)‖ ^ 2 ≤
      (1 / 2000 : ℝ) * ‖x‖ ^ 2 := by
  have hsource :=
    evenTailLowPairing_sq_le_sourceEnergy_of_interchange x.toV i hinterchange
  have hcoercive :
      (102 / 25 : ℝ) *
          clippedIntervalEnergy (evenOneNinetyNineTailToClippedSmooth x.toV) ≤
        ‖x‖ ^ 2 := by
    rw [norm_sq_eq_form_re]
    exact evenOneNinetyNineTailPositiveHermitianForm_coercive x.toV
  calc
    ‖yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth x.toV)
        (yoshidaClippedEvenLowMode yoshidaA i)‖ ^ 2 ≤
      (51 / 25000 : ℝ) *
        clippedIntervalEnergy (evenOneNinetyNineTailToClippedSmooth x.toV) := hsource
    _ = (1 / 2000 : ℝ) *
        ((102 / 25 : ℝ) *
          clippedIntervalEnergy (evenOneNinetyNineTailToClippedSmooth x.toV)) := by ring
    _ ≤ (1 / 2000 : ℝ) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hcoercive (by norm_num)

/-- Once the exact interchange is supplied for every algebraic tail vector,
the generic completion machinery produces the actual low-mode Riesz vector.
No surrogate functional is introduced: its values are the production
clipped critical pairings. -/
noncomputable def evenTailLowRieszCorrection
    (i : YoshidaEvenIndex)
    (hinterchange : ∀ f : YoshidaEvenOneNinetyNineTail,
      EvenTailLowFourierInterchange f i) :
    FormSpace.Completion evenOneNinetyNineTailPositiveHermitianForm :=
  externalLowRieszCorrectionOfSqBound
    (q := evenOneNinetyNineTailPositiveHermitianForm)
    (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos)
    (yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos)
    evenOneNinetyNineTailToClippedSmooth
    (yoshidaClippedEvenLowMode yoshidaA i)
    (S := (1 / 2000 : ℝ)) (by norm_num)
    (fun x ↦ evenTailLowFunctional_sq_le_formNorm_of_interchange
      x i (hinterchange x.toV))

theorem norm_sq_evenTailLowRieszCorrection_le
    (i : YoshidaEvenIndex)
    (hinterchange : ∀ f : YoshidaEvenOneNinetyNineTail,
      EvenTailLowFourierInterchange f i) :
    ‖evenTailLowRieszCorrection i hinterchange‖ ^ 2 ≤
      (1 / 2000 : ℝ) := by
  exact norm_sq_externalLowRieszCorrection_le
    (q := evenOneNinetyNineTailPositiveHermitianForm)
    (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos)
    (yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos)
    evenOneNinetyNineTailToClippedSmooth
    (yoshidaClippedEvenLowMode yoshidaA i)
    (S := (1 / 2000 : ℝ)) (by norm_num)
    (fun x ↦ evenTailLowFunctional_sq_le_formNorm_of_interchange
      x i (hinterchange x.toV))

/-- Premise-free source-energy estimate for the actual production pairing. -/
theorem evenTailLowPairing_sq_le_sourceEnergy
    (f : YoshidaEvenOneNinetyNineTail) (i : YoshidaEvenIndex) :
    ‖yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f)
        (yoshidaClippedEvenLowMode yoshidaA i)‖ ^ 2 ≤
      (51 / 25000 : ℝ) *
        clippedIntervalEnergy (evenOneNinetyNineTailToClippedSmooth f) :=
  evenTailLowPairing_sq_le_sourceEnergy_of_interchange f i
    (evenTailLowFourierInterchange f i)

/-- Final boundedness theorem in exactly the shape required by
`FormSpace.externalLowRieszCorrectionOfSqBound`. -/
theorem evenTailLowFunctional_sq_le_formNorm
    (x : FormSpace evenOneNinetyNineTailPositiveHermitianForm)
    (i : YoshidaEvenIndex) :
    ‖yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth x.toV)
        (yoshidaClippedEvenLowMode yoshidaA i)‖ ^ 2 ≤
      (1 / 2000 : ℝ) * ‖x‖ ^ 2 :=
  evenTailLowFunctional_sq_le_formNorm_of_interchange x i
    (evenTailLowFourierInterchange x.toV i)

/-- The actual low-mode Riesz correction, with no analytic premise. -/
noncomputable def actualEvenTailLowRieszCorrection
    (i : YoshidaEvenIndex) :
    FormSpace.Completion evenOneNinetyNineTailPositiveHermitianForm :=
  externalLowRieszCorrectionOfSqBound
    (q := evenOneNinetyNineTailPositiveHermitianForm)
    (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos)
    (yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos)
    evenOneNinetyNineTailToClippedSmooth
    (yoshidaClippedEvenLowMode yoshidaA i)
    (S := (1 / 2000 : ℝ)) (by norm_num)
    (fun x ↦ evenTailLowFunctional_sq_le_formNorm x i)

theorem norm_sq_actualEvenTailLowRieszCorrection_le
    (i : YoshidaEvenIndex) :
    ‖actualEvenTailLowRieszCorrection i‖ ^ 2 ≤ (1 / 2000 : ℝ) := by
  exact norm_sq_externalLowRieszCorrection_le
    (q := evenOneNinetyNineTailPositiveHermitianForm)
    (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos)
    (yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos)
    evenOneNinetyNineTailToClippedSmooth
    (yoshidaClippedEvenLowMode yoshidaA i)
    (S := (1 / 2000 : ℝ)) (by norm_num)
    (fun x ↦ evenTailLowFunctional_sq_le_formNorm x i)

@[simp] theorem formSpace_inner_actualEvenTailLowRieszCorrection
    (i : YoshidaEvenIndex)
    (x : FormSpace evenOneNinetyNineTailPositiveHermitianForm) :
    ⟪(x : FormSpace.Completion evenOneNinetyNineTailPositiveHermitianForm),
      actualEvenTailLowRieszCorrection i⟫_ℂ =
      yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth x.toV)
        (yoshidaClippedEvenLowMode yoshidaA i) := by
  exact coe_inner_externalLowRieszCorrection
    (q := evenOneNinetyNineTailPositiveHermitianForm)
    (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos)
    (yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos)
    evenOneNinetyNineTailToClippedSmooth
    (yoshidaClippedEvenLowMode yoshidaA i)
    (S := (1 / 2000 : ℝ)) (by norm_num)
    (fun y ↦ evenTailLowFunctional_sq_le_formNorm y i) x

/-- Gram matrix of the two hundred actual low/even-tail Riesz corrections. -/
noncomputable def actualEvenTailCorrectionGram :
    Matrix YoshidaEvenIndex YoshidaEvenIndex ℂ :=
  fun i j ↦
    ⟪actualEvenTailLowRieszCorrection i,
      actualEvenTailLowRieszCorrection j⟫_ℂ

theorem actualEvenTailCorrectionGram_isHermitian :
    actualEvenTailCorrectionGram.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  exact inner_conj_symm _ _

private theorem correction_norm_product_le
    (i j : YoshidaEvenIndex) :
    ‖actualEvenTailLowRieszCorrection i‖ *
        ‖actualEvenTailLowRieszCorrection j‖ ≤ (1 / 2000 : ℝ) := by
  rw [← sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 1 / 2000)]
  calc
    (‖actualEvenTailLowRieszCorrection i‖ *
        ‖actualEvenTailLowRieszCorrection j‖) ^ 2 =
        ‖actualEvenTailLowRieszCorrection i‖ ^ 2 *
          ‖actualEvenTailLowRieszCorrection j‖ ^ 2 := by ring
    _ ≤ (1 / 2000 : ℝ) * (1 / 2000 : ℝ) :=
      mul_le_mul
        (norm_sq_actualEvenTailLowRieszCorrection_le i)
        (norm_sq_actualEvenTailLowRieszCorrection_le j)
        (sq_nonneg _) (by norm_num)
    _ = (1 / 2000 : ℝ) ^ 2 := by ring

/-- The actual Schur correction fits exactly in the certified uniform
entrywise radius `evenCorrectionRadius = 1 / 2000`. -/
theorem actualEvenTailCorrectionGram_norm_le
    (i j : YoshidaEvenIndex) :
    ‖actualEvenTailCorrectionGram i j‖ ≤ (1 / 2000 : ℝ) := by
  exact (norm_inner_le_norm _ _).trans (correction_norm_product_le i j)

theorem actualEvenTailCorrectionGram_norm_le_correctionRadius
    (i j : YoshidaEvenIndex) :
    ‖actualEvenTailCorrectionGram i j‖ ≤
      (evenCorrectionRadius : ℝ) := by
  simpa only [evenCorrectionRadius, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat] using actualEvenTailCorrectionGram_norm_le i j

end ArithmeticHodge.Analysis.YoshidaEvenTailLowFunctional
