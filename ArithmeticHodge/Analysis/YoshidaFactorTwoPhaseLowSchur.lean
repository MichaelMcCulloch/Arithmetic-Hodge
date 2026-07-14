import ArithmeticHodge.Analysis.TwoByTwoSchur
import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointBilinear
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseFullProfile
import ArithmeticHodge.Analysis.YoshidaFourierModes

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLowSchur

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseFullProfile

/-!
# Exact finite-low phase block

The factor-two reflection channel has two finite Fourier sectors: the first
two hundred even modes and the first ten odd modes.  This file packages those
sectors into one genuine `210 x 210` real symmetric phase matrix.  The
off-diagonal normalization is fixed here: an entry `b * J / 2` in each
transpose block contributes exactly `b * J` to the quadratic form.

No positivity certificate is assumed or hidden in the definitions.  The
result below is an exact structural reduction of the finite-low obligation to
positive semidefiniteness of this concrete phase matrix.
-/

/-- The finite coordinate type of one reflection channel: `200 + 10` real
Fourier coordinates. -/
abbrev FactorTwoPhaseLowIndex := YoshidaEvenIndex ⊕ YoshidaOddIndex

/-- Pack even and odd Fourier coefficient vectors into the coupled low
coordinate space. -/
def factorTwoPhaseLowCoefficients
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    FactorTwoPhaseLowIndex → ℝ :=
  Sum.elim e o

/-- A symmetric block matrix with prescribed even, odd, and even--odd
blocks.  The lower-left block is definitionally the transpose of the
upper-right block. -/
def factorTwoPhaseBlockMatrix
    (E : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (O : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (C : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ) :
    Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ
  | Sum.inl i, Sum.inl j => E i j
  | Sum.inl i, Sum.inr j => C i j
  | Sum.inr i, Sum.inl j => C j i
  | Sum.inr i, Sum.inr j => O i j

/-- The block construction is Hermitian as soon as its two diagonal blocks
are Hermitian. -/
theorem factorTwoPhaseBlockMatrix_isHermitian
    {E : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ}
    {O : Matrix YoshidaOddIndex YoshidaOddIndex ℝ}
    (C : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (hE : E.IsHermitian) (hO : O.IsHermitian) :
    (factorTwoPhaseBlockMatrix E O C).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  cases i with
  | inl i =>
      cases j with
      | inl j => exact hE.apply i j
      | inr j => simp [factorTwoPhaseBlockMatrix]
  | inr i =>
      cases j with
      | inl j => simp [factorTwoPhaseBlockMatrix]
      | inr j => exact hO.apply i j

/-- Exact quadratic expansion of the coupled block on packed coefficients. -/
theorem factorTwoPhaseBlockMatrix_quadratic
    (E : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (O : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (C : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    let c := factorTwoPhaseLowCoefficients e o
    c ⬝ᵥ (factorTwoPhaseBlockMatrix E O C *ᵥ c) =
      e ⬝ᵥ (E *ᵥ e) + o ⬝ᵥ (O *ᵥ o) +
        2 * ∑ i, ∑ j, e i * C i j * o j := by
  classical
  have hcrossLeft :
      (∑ i : YoshidaEvenIndex,
          e i * ∑ j : YoshidaOddIndex, C i j * o j) =
        ∑ i : YoshidaEvenIndex, ∑ j : YoshidaOddIndex,
          e i * C i j * o j := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hcrossRight :
      (∑ j : YoshidaOddIndex,
          o j * ∑ i : YoshidaEvenIndex, C i j * e i) =
        ∑ i : YoshidaEvenIndex, ∑ j : YoshidaOddIndex,
          e i * C i j * o j := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  simp only [dotProduct, mulVec, factorTwoPhaseLowCoefficients]
  simp_rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, factorTwoPhaseBlockMatrix]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hcrossLeft, hcrossRight]
  ring

/-- The exact finite phase matrix.  `QE,QO` are the clean diagonal blocks,
`PE,PO` are the symmetric factor-two perturbation blocks, and `J` is the
alternating even--odd block. -/
def factorTwoFiniteLowPhaseMatrix
    (QE PE : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (QO PO : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (J : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (a b : ℝ) : Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ :=
  factorTwoPhaseBlockMatrix
    (QE + a • PE) (QO + a • PO) ((b / 2) • J)

/-- Expanding the finite phase matrix produces exactly
`Q + a P + b J`, with no triangle-inequality loss. -/
theorem factorTwoFiniteLowPhaseMatrix_quadratic
    (QE PE : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (QO PO : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (J : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) :
    let c := factorTwoPhaseLowCoefficients e o
    c ⬝ᵥ (factorTwoFiniteLowPhaseMatrix QE PE QO PO J a b *ᵥ c) =
      (e ⬝ᵥ (QE *ᵥ e) + o ⬝ᵥ (QO *ᵥ o)) +
      a * (e ⬝ᵥ (PE *ᵥ e) + o ⬝ᵥ (PO *ᵥ o)) +
      b * ∑ i, ∑ j, e i * J i j * o j := by
  classical
  have hcross :
      (∑ i : YoshidaEvenIndex, ∑ j : YoshidaOddIndex,
        e i * (((b / 2) • J) i j) * o j) =
        (b / 2) * ∑ i : YoshidaEvenIndex, ∑ j : YoshidaOddIndex,
          e i * J i j * o j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    change e i * ((b / 2) * J i j) * o j = _
    ring
  dsimp only
  rw [factorTwoFiniteLowPhaseMatrix,
    factorTwoPhaseBlockMatrix_quadratic]
  simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  rw [hcross]
  ring

/-- Positive semidefiniteness of the phase matrix closes the complete
finite-low scalar obligation for the given phase. -/
theorem finiteLowPhase_nonneg_of_posSemidef
    (QE PE : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (QO PO : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (J : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ)
    (hPSD : (factorTwoFiniteLowPhaseMatrix QE PE QO PO J a b).PosSemidef) :
    0 ≤
      (e ⬝ᵥ (QE *ᵥ e) + o ⬝ᵥ (QO *ᵥ o)) +
      a * (e ⬝ᵥ (PE *ᵥ e) + o ⬝ᵥ (PO *ᵥ o)) +
      b * ∑ i, ∑ j, e i * J i j * o j := by
  rw [← factorTwoFiniteLowPhaseMatrix_quadratic]
  simpa using
    hPSD.dotProduct_mulVec_nonneg (factorTwoPhaseLowCoefficients e o)

/-- A disk-uniform PSD certificate is exactly the reusable finite-low
certificate required by the endpoint phase argument. -/
theorem finiteLowPhase_nonneg_of_disk_posSemidef
    (QE PE : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (QO PO : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (J : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (hPSD : ∀ a b : ℝ, a ^ 2 + b ^ 2 ≤ 1 →
      (factorTwoFiniteLowPhaseMatrix QE PE QO PO J a b).PosSemidef)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤
      (e ⬝ᵥ (QE *ᵥ e) + o ⬝ᵥ (QO *ᵥ o)) +
      a * (e ⬝ᵥ (PE *ᵥ e) + o ⬝ᵥ (PO *ᵥ o)) +
      b * ∑ i, ∑ j, e i * J i j * o j :=
  finiteLowPhase_nonneg_of_posSemidef QE PE QO PO J e o a b
    (hPSD a b hab)

/-! ## Structural collapse of the even low block to `P₀/P₂`

The Fourier `Fin 200` block is useful for the historical clipped-form
certificate, but it is not the intrinsic low block of the endpoint clean
form.  The exact endpoint polarization splits every even profile into the
two Legendre modes `P₀,P₂` and a residual annihilating both moments.  The
following API keeps all factor-two phase terms in that smaller split.
-/

/-- The intrinsic two-dimensional even low profile. -/
def factorTwoEvenStructuralLowProfile (c d : ℝ) : ℝ → ℝ :=
  fun x ↦ c * centeredEvenP0 x + d * centeredEvenP2 x

theorem continuous_factorTwoEvenStructuralLowProfile (c d : ℝ) :
    Continuous (factorTwoEvenStructuralLowProfile c d) := by
  unfold factorTwoEvenStructuralLowProfile centeredEvenP0 centeredEvenP2
  fun_prop

theorem factorTwoEvenStructuralLowProfile_eq_smul_add
    (c d : ℝ) :
    factorTwoEvenStructuralLowProfile c d =
      c • centeredEvenP0 + d • centeredEvenP2 := by
  funext x
  simp only [factorTwoEvenStructuralLowProfile, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]

/-- Bilinearity under two real scalings, first at the correlation level. -/
theorem factorTwoCenteredCorrelationBilinear_smul_smul
    (c d : ℝ) (u v : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredCorrelationBilinear (c • u) (d • v) t =
      c * d * factorTwoCenteredCorrelationBilinear u v t := by
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_smul_left,
    factorTwoCenteredCrossCorrelation_smul_right,
    factorTwoCenteredCrossCorrelation_smul_left,
    factorTwoCenteredCrossCorrelation_smul_right]
  ring

/-- Bilinearity of the complete symmetric perturbation, including its
singular archimedean integral and both retained prime atoms. -/
theorem factorTwoCenteredSymmetricPerturbationBilinear_smul_smul
    (c d : ℝ) (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear (c • u) (d • v) =
      c * d * factorTwoCenteredSymmetricPerturbationBilinear u v := by
  have hfun :
      (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        factorTwoCenteredCorrelationBilinear (c • u) (d • v) t) =
      fun t ↦ c * d *
        (factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          factorTwoCenteredCorrelationBilinear u v t) := by
    funext t
    rw [factorTwoCenteredCorrelationBilinear_smul_smul]
    ring
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  rw [hfun, intervalIntegral.integral_const_mul,
    factorTwoCenteredCorrelationBilinear_smul_smul,
    factorTwoCenteredCorrelationBilinear_smul_smul]
  ring

/-- The symmetric perturbation is genuinely quadratic under real scaling. -/
theorem factorTwoCenteredSymmetricPerturbation_smul
    (c : ℝ) (u : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbation (c • u) =
      c ^ 2 * factorTwoCenteredSymmetricPerturbation u := by
  rw [← factorTwoCenteredSymmetricPerturbationBilinear_self,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_smul,
    factorTwoCenteredSymmetricPerturbationBilinear_self]
  ring

/-- Additivity in the first entry on the continuous form domain. -/
theorem factorTwoCenteredSymmetricPerturbationBilinear_add_left
    (u v w : ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    factorTwoCenteredSymmetricPerturbationBilinear (u + v) w =
      factorTwoCenteredSymmetricPerturbationBilinear u w +
        factorTwoCenteredSymmetricPerturbationBilinear v w := by
  have huv (t : ℝ) :
      factorTwoCenteredCorrelationBilinear (u + v) w t =
        factorTwoCenteredCorrelationBilinear u w t +
          factorTwoCenteredCorrelationBilinear v w t := by
    unfold factorTwoCenteredCorrelationBilinear
    rw [factorTwoCenteredCrossCorrelation_add_left u v w hu hv hw,
      factorTwoCenteredCrossCorrelation_add_right w u v hw hu hv]
    ring
  have huInt := intervalIntegrable_factorTwoCenteredSymmetricKernel
    u w hu hw
  have hvInt := intervalIntegrable_factorTwoCenteredSymmetricKernel
    v w hv hw
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  rw [show (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
      factorTwoCenteredCorrelationBilinear (u + v) w t) =
      fun t ↦
        factorTwoSymmetricWeight (yoshidaEndpointA * t) *
            factorTwoCenteredCorrelationBilinear u w t +
          factorTwoSymmetricWeight (yoshidaEndpointA * t) *
            factorTwoCenteredCorrelationBilinear v w t by
    funext t
    rw [huv]
    ring,
    intervalIntegral.integral_add huInt hvInt,
    huv, huv]
  ring

theorem factorTwoCenteredSymmetricPerturbationBilinear_smul_left
    (c : ℝ) (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear (c • u) v =
      c * factorTwoCenteredSymmetricPerturbationBilinear u v := by
  simpa using
    factorTwoCenteredSymmetricPerturbationBilinear_smul_smul c 1 u v

/-- Exact two-mode quadratic expansion of the symmetric perturbation. -/
theorem factorTwoCenteredSymmetricPerturbation_structuralLow
    (c d : ℝ) :
    factorTwoCenteredSymmetricPerturbation
        (factorTwoEvenStructuralLowProfile c d) =
      c ^ 2 * factorTwoCenteredSymmetricPerturbation centeredEvenP0 +
        2 * c * d *
          factorTwoCenteredSymmetricPerturbationBilinear
            centeredEvenP0 centeredEvenP2 +
        d ^ 2 * factorTwoCenteredSymmetricPerturbation centeredEvenP2 := by
  have h0 : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have h2 : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  rw [factorTwoEvenStructuralLowProfile_eq_smul_add,
    factorTwoCenteredSymmetricPerturbation_add_eq_bilinear
      (c • centeredEvenP0) (d • centeredEvenP2)
      (h0.const_smul c) (h2.const_smul d),
    factorTwoCenteredSymmetricPerturbation_smul,
    factorTwoCenteredSymmetricPerturbation_smul,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_smul]
  ring

/-- Exact low-to-residual expansion of the symmetric perturbation. -/
theorem factorTwoCenteredSymmetricPerturbationBilinear_structuralLow
    (c d : ℝ) (r : ℝ → ℝ) (hr : Continuous r) :
    factorTwoCenteredSymmetricPerturbationBilinear
        (factorTwoEvenStructuralLowProfile c d) r =
      c * factorTwoCenteredSymmetricPerturbationBilinear centeredEvenP0 r +
        d * factorTwoCenteredSymmetricPerturbationBilinear centeredEvenP2 r := by
  have h0 : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have h2 : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  rw [factorTwoEvenStructuralLowProfile_eq_smul_add,
    factorTwoCenteredSymmetricPerturbationBilinear_add_left
      (c • centeredEvenP0) (d • centeredEvenP2) r
      (h0.const_smul c) (h2.const_smul d) hr,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_left,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_left]

/-- Exact two-mode expansion of the alternating low-to-odd coordinate. -/
theorem factorTwoCenteredAlternatingCoupling_structuralLow
    (c d : ℝ) (o : ℝ → ℝ) (ho : Continuous o) :
    factorTwoCenteredAlternatingCoupling
        (factorTwoEvenStructuralLowProfile c d) o =
      c * factorTwoCenteredAlternatingCoupling centeredEvenP0 o +
        d * factorTwoCenteredAlternatingCoupling centeredEvenP2 o := by
  have h0 : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have h2 : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  rw [factorTwoEvenStructuralLowProfile_eq_smul_add,
    factorTwoCenteredAlternatingCoupling_add_left
      (c • centeredEvenP0) (d • centeredEvenP2) o
      (h0.const_smul c) (h2.const_smul d) ho,
    factorTwoCenteredAlternatingCoupling_smul_left,
    factorTwoCenteredAlternatingCoupling_smul_left]

/-- The phase-dependent `P₀/P₂` low Gram entries. -/
def factorTwoStructuralPhaseLow00 (alpha : ℝ) : ℝ :=
  yoshidaEndpointEvenLowGram00 +
    alpha * factorTwoCenteredSymmetricPerturbation centeredEvenP0

def factorTwoStructuralPhaseLow02 (alpha : ℝ) : ℝ :=
  yoshidaEndpointEvenLowGram02 +
    alpha * factorTwoCenteredSymmetricPerturbationBilinear
      centeredEvenP0 centeredEvenP2

def factorTwoStructuralPhaseLow22 (alpha : ℝ) : ℝ :=
  yoshidaEndpointEvenLowGram22 +
    alpha * factorTwoCenteredSymmetricPerturbation centeredEvenP2

/-- Strict positivity criterion for a real symmetric `2 x 2` quadratic. -/
theorem real_twoByTwo_quadratic_pos
    (q00 q02 q22 c d : ℝ)
    (h00 : 0 < q00) (hdet : 0 < q00 * q22 - q02 ^ 2)
    (hne : c ≠ 0 ∨ d ≠ 0) :
    0 < q00 * c ^ 2 + 2 * q02 * c * d + q22 * d ^ 2 := by
  have hid :
      q00 * (q00 * c ^ 2 + 2 * q02 * c * d + q22 * d ^ 2) =
        (q00 * c + q02 * d) ^ 2 +
          (q00 * q22 - q02 ^ 2) * d ^ 2 := by
    ring
  by_cases hd : d = 0
  · have hc : c ≠ 0 := by
      rcases hne with hc | hdne
      · exact hc
      · exact (hdne hd).elim
    rw [hd]
    norm_num
    exact mul_pos h00 (sq_pos_of_ne_zero hc)
  · have hright : 0 <
        (q00 * c + q02 * d) ^ 2 +
          (q00 * q22 - q02 ^ 2) * d ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _)
        (mul_pos hdet (sq_pos_of_ne_zero hd))
    have hscaled : 0 < q00 *
        (q00 * c ^ 2 + 2 * q02 * c * d + q22 * d ^ 2) := by
      rw [hid]
      exact hright
    exact ((mul_pos_iff.mp hscaled).resolve_right (by
      intro hneg
      exact (not_lt_of_ge h00.le) hneg.1)).2

/-- Recover the leading entry and determinant from strict positivity of the
associated quadratic form. -/
theorem real_twoByTwo_coefficients_pos_of_quadratic_pos
    (q00 q02 q22 : ℝ)
    (hpos : ∀ c d : ℝ, c ≠ 0 ∨ d ≠ 0 →
      0 < q00 * c ^ 2 + 2 * q02 * c * d + q22 * d ^ 2) :
    0 < q00 ∧ 0 < q00 * q22 - q02 ^ 2 := by
  have h00 : 0 < q00 := by
    have h := hpos 1 0 (Or.inl one_ne_zero)
    norm_num at h
    exact h
  refine ⟨h00, ?_⟩
  have hspecial := hpos q02 (-q00) (Or.inr (neg_ne_zero.mpr h00.ne'))
  have hid :
      q00 * q02 ^ 2 + 2 * q02 * q02 * (-q00) +
          q22 * (-q00) ^ 2 =
        q00 * (q00 * q22 - q02 ^ 2) := by
    ring
  rw [hid] at hspecial
  exact ((mul_pos_iff.mp hspecial).resolve_right (by
    intro hneg
    exact (not_lt_of_ge h00.le) hneg.1)).2

/-- The true affine `P₀/P₂` phase pencil is positive throughout `[-1,1]`
once its two signed endpoint matrices are positive.  This avoids any interior
determinant search: the quadratic form is the convex combination of its
endpoint forms. -/
theorem factorTwoStructuralPhaseLow_pos_of_endpoints
    (alpha : ℝ) (halphaLower : -1 ≤ alpha) (halphaUpper : alpha ≤ 1)
    (hplus00 : 0 < factorTwoStructuralPhaseLow00 1)
    (hplusDet : 0 <
      factorTwoStructuralPhaseLow00 1 *
          factorTwoStructuralPhaseLow22 1 -
        factorTwoStructuralPhaseLow02 1 ^ 2)
    (hminus00 : 0 < factorTwoStructuralPhaseLow00 (-1))
    (hminusDet : 0 <
      factorTwoStructuralPhaseLow00 (-1) *
          factorTwoStructuralPhaseLow22 (-1) -
        factorTwoStructuralPhaseLow02 (-1) ^ 2) :
    0 < factorTwoStructuralPhaseLow00 alpha ∧
      0 < factorTwoStructuralPhaseLow00 alpha *
          factorTwoStructuralPhaseLow22 alpha -
        factorTwoStructuralPhaseLow02 alpha ^ 2 := by
  let lambda : ℝ := (1 + alpha) / 2
  let mu : ℝ := (1 - alpha) / 2
  have hlambda : 0 ≤ lambda := by
    dsimp only [lambda]
    linarith
  have hmu : 0 ≤ mu := by
    dsimp only [mu]
    linarith
  have hsum : lambda + mu = 1 := by
    dsimp only [lambda, mu]
    ring
  have hquadratic (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
      0 < factorTwoStructuralPhaseLow00 alpha * c ^ 2 +
        2 * factorTwoStructuralPhaseLow02 alpha * c * d +
        factorTwoStructuralPhaseLow22 alpha * d ^ 2 := by
    let Qp := factorTwoStructuralPhaseLow00 1 * c ^ 2 +
      2 * factorTwoStructuralPhaseLow02 1 * c * d +
      factorTwoStructuralPhaseLow22 1 * d ^ 2
    let Qm := factorTwoStructuralPhaseLow00 (-1) * c ^ 2 +
      2 * factorTwoStructuralPhaseLow02 (-1) * c * d +
      factorTwoStructuralPhaseLow22 (-1) * d ^ 2
    have hp : 0 < Qp := real_twoByTwo_quadratic_pos _ _ _ c d
      hplus00 hplusDet hne
    have hm : 0 < Qm := real_twoByTwo_quadratic_pos _ _ _ c d
      hminus00 hminusDet hne
    have hconvex :
        factorTwoStructuralPhaseLow00 alpha * c ^ 2 +
            2 * factorTwoStructuralPhaseLow02 alpha * c * d +
            factorTwoStructuralPhaseLow22 alpha * d ^ 2 =
          lambda * Qp + mu * Qm := by
      dsimp only [lambda, mu, Qp, Qm]
      unfold factorTwoStructuralPhaseLow00
        factorTwoStructuralPhaseLow02 factorTwoStructuralPhaseLow22
      ring
    rw [hconvex]
    rcases hlambda.eq_or_lt with hlambdaZero | hlambdaPos
    · have hmuOne : mu = 1 := by linarith
      rw [← hlambdaZero, hmuOne, zero_mul, one_mul]
      simpa using hm
    · exact add_pos_of_pos_of_nonneg (mul_pos hlambdaPos hp)
        (mul_nonneg hmu hm.le)
  exact real_twoByTwo_coefficients_pos_of_quadratic_pos _ _ _ hquadratic

/-- Disk-uniform low-block closure from the two signed endpoint
certificates.  The second phase coordinate enters only to force
`alpha ∈ [-1,1]`. -/
theorem factorTwoStructuralPhaseLow_pos_of_endpoint_certificates
    (alpha beta : ℝ) (hab : alpha ^ 2 + beta ^ 2 ≤ 1)
    (hplus00 : 0 < factorTwoStructuralPhaseLow00 1)
    (hplusDet : 0 <
      factorTwoStructuralPhaseLow00 1 *
          factorTwoStructuralPhaseLow22 1 -
        factorTwoStructuralPhaseLow02 1 ^ 2)
    (hminus00 : 0 < factorTwoStructuralPhaseLow00 (-1))
    (hminusDet : 0 <
      factorTwoStructuralPhaseLow00 (-1) *
          factorTwoStructuralPhaseLow22 (-1) -
        factorTwoStructuralPhaseLow02 (-1) ^ 2) :
    0 < factorTwoStructuralPhaseLow00 alpha ∧
      0 < factorTwoStructuralPhaseLow00 alpha *
          factorTwoStructuralPhaseLow22 alpha -
        factorTwoStructuralPhaseLow02 alpha ^ 2 := by
  have halphaLower : -1 ≤ alpha := by
    nlinarith [sq_nonneg beta, sq_nonneg (alpha + 1)]
  have halphaUpper : alpha ≤ 1 := by
    nlinarith [sq_nonneg beta, sq_nonneg (alpha - 1)]
  exact factorTwoStructuralPhaseLow_pos_of_endpoints alpha
    halphaLower halphaUpper hplus00 hplusDet hminus00 hminusDet

/-- The two complete phase-dependent low-to-tail functionals.  The factor
`beta/2` is forced by the `2*c*ell` Schur normalization. -/
def factorTwoStructuralPhaseLowTail0
    (r o : ℝ → ℝ) (alpha beta : ℝ) : ℝ :=
  (∫ x : ℝ in -1..1,
      yoshidaEndpointEvenTailRepresenter0 x * r x) +
    alpha * factorTwoCenteredSymmetricPerturbationBilinear
      centeredEvenP0 r +
    (beta / 2) * factorTwoCenteredAlternatingCoupling centeredEvenP0 o

def factorTwoStructuralPhaseLowTail2
    (r o : ℝ → ℝ) (alpha beta : ℝ) : ℝ :=
  (∫ x : ℝ in -1..1,
      yoshidaEndpointEvenTailRepresenter2 x * r x) +
    alpha * factorTwoCenteredSymmetricPerturbationBilinear
      centeredEvenP2 r +
    (beta / 2) * factorTwoCenteredAlternatingCoupling centeredEvenP2 o

/-- The residual-plus-odd phase form left after removing `P₀/P₂`. -/
def factorTwoStructuralPhaseTail
    (r o : ℝ → ℝ) (alpha beta : ℝ) : ℝ :=
  factorTwoEndpointChannelPhase r o alpha beta

/-- Exact `P₀/P₂` low/tail expansion of the complete coupled endpoint phase.
This replaces the apparent `Fin 200` even low block by the intrinsic two-mode
Schur block while retaining every low-residual and low-odd term. -/
theorem factorTwoEndpointChannelPhase_structuralLowTail
    (r o : ℝ → ℝ) (hr : Continuous r) (hre : Function.Even r)
    (hzero : centeredEvenP0Coefficient r = 0)
    (htwo : centeredEvenP2Coefficient r = 0)
    (hlocal : LocallyLipschitzOn (Set.Icc (-1) 1) r)
    (ho : Continuous o)
    (c d alpha beta : ℝ) :
    factorTwoEndpointChannelPhase
        (factorTwoEvenStructuralLowProfile c d + r) o alpha beta =
      factorTwoStructuralPhaseLow00 alpha * c ^ 2 +
        2 * factorTwoStructuralPhaseLow02 alpha * c * d +
        factorTwoStructuralPhaseLow22 alpha * d ^ 2 +
        2 * c * factorTwoStructuralPhaseLowTail0 r o alpha beta +
        2 * d * factorTwoStructuralPhaseLowTail2 r o alpha beta +
        factorTwoStructuralPhaseTail r o alpha beta := by
  have hlow := continuous_factorTwoEvenStructuralLowProfile c d
  have hQ := yoshidaEndpointOddCleanQuadratic_fixed_low_tail_expansion
    r hr hre hzero htwo hlocal c d
  have hQ' :
      yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d + r) =
        yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * d +
          yoshidaEndpointEvenLowGram22 * d ^ 2 +
          2 * c * (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenTailRepresenter0 x * r x) +
          2 * d * (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenTailRepresenter2 x * r x) +
          yoshidaEndpointOddCleanQuadratic r := by
    rw [show factorTwoEvenStructuralLowProfile c d + r =
        fun x ↦ c * centeredEvenP0 x + d * centeredEvenP2 x + r x by
      funext x
      rfl]
    exact hQ
  have hP := factorTwoCenteredSymmetricPerturbation_add_eq_bilinear
    (factorTwoEvenStructuralLowProfile c d) r hlow hr
  have hPlow :=
    factorTwoCenteredSymmetricPerturbation_structuralLow c d
  have hPcross :=
    factorTwoCenteredSymmetricPerturbationBilinear_structuralLow c d r hr
  have hJ := factorTwoCenteredAlternatingCoupling_add_left
    (factorTwoEvenStructuralLowProfile c d) r o hlow hr ho
  have hJlow := factorTwoCenteredAlternatingCoupling_structuralLow c d o ho
  unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
    factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22 factorTwoStructuralPhaseLowTail0
    factorTwoStructuralPhaseLowTail2 factorTwoStructuralPhaseTail
  rw [hQ', hP, hPlow, hPcross, hJ, hJlow]
  unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
  ring

/-- Exact 2x2 Schur closure.  Consequently the remaining analytic work is
only positivity of the three phase-dependent low entries, their determinant,
and one adjugate bound for the two displayed complete functionals. -/
theorem factorTwoEndpointChannelPhase_structuralLowTail_nonneg
    (r o : ℝ → ℝ) (hr : Continuous r) (hre : Function.Even r)
    (hzero : centeredEvenP0Coefficient r = 0)
    (htwo : centeredEvenP2Coefficient r = 0)
    (hlocal : LocallyLipschitzOn (Set.Icc (-1) 1) r)
    (ho : Continuous o)
    (c d alpha beta : ℝ)
    (h00 : 0 < factorTwoStructuralPhaseLow00 alpha)
    (hdet : 0 <
      factorTwoStructuralPhaseLow00 alpha *
          factorTwoStructuralPhaseLow22 alpha -
        factorTwoStructuralPhaseLow02 alpha ^ 2)
    (hschur :
      factorTwoStructuralPhaseLow22 alpha *
          factorTwoStructuralPhaseLowTail0 r o alpha beta ^ 2 -
        2 * factorTwoStructuralPhaseLow02 alpha *
          factorTwoStructuralPhaseLowTail0 r o alpha beta *
          factorTwoStructuralPhaseLowTail2 r o alpha beta +
        factorTwoStructuralPhaseLow00 alpha *
          factorTwoStructuralPhaseLowTail2 r o alpha beta ^ 2 ≤
        (factorTwoStructuralPhaseLow00 alpha *
            factorTwoStructuralPhaseLow22 alpha -
          factorTwoStructuralPhaseLow02 alpha ^ 2) *
          factorTwoStructuralPhaseTail r o alpha beta) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoEvenStructuralLowProfile c d + r) o alpha beta := by
  rw [factorTwoEndpointChannelPhase_structuralLowTail
    r o hr hre hzero htwo hlocal ho c d alpha beta]
  exact TwoByTwoSchur.quadratic_add_tail_nonneg
    (factorTwoStructuralPhaseLow00 alpha)
    (factorTwoStructuralPhaseLow02 alpha)
    (factorTwoStructuralPhaseLow22 alpha)
    (factorTwoStructuralPhaseLowTail0 r o alpha beta)
    (factorTwoStructuralPhaseLowTail2 r o alpha beta)
    (factorTwoStructuralPhaseTail r o alpha beta)
    c d h00 hdet hschur

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLowSchur
