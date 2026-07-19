import ArithmeticHodge.Analysis.MultiplicativeWeilFarPrimeShellStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticRealImagSplitStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilDirectedCorrelationPhysicalStructural
import ArithmeticHodge.Analysis.YoshidaBombieriCrossMoments

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction ComplexConjugate

namespace ArithmeticHodge.Analysis.MultiplicativeWeilRealLogKernelStructural

noncomputable section

open MultiplicativeWeil
open ArithmeticHodge.Analysis.MultiplicativeWeilDirectedCorrelationPhysicalStructural
open YoshidaBombieriCrossDistribution
open YoshidaBombieriCrossMoments

/-!
# The complete Bombieri form as a real logarithmic kernel

The critical logarithmic pullback puts both halves of Bombieri's complete
cross in one translation coordinate.  The archimedean part is the sum of the
polar kernel and the exact renormalized Cauchy distribution.  The arithmetic
part is a symmetric discrete measure at the lags `+- log n`, with coefficient
`vonMangoldt n / sqrt n`.

Thus the complete kernel is translation invariant, but it is signed: every
prime-power atom is subtracted.  In particular the atom at `+- log 2` has a
strictly negative coefficient.  This is the exact obstruction to treating
the complete form as a positive-measure convolution in a monotone-cutoff
argument; any successful contraction has to retain cancellation between the
archimedean distribution and these arithmetic atoms.
-/

/-- The real polar weight in critical logarithmic coordinates. -/
def bombieriLogPolarKernel (u : ℝ) : ℝ :=
  Real.exp (u / 2) + Real.exp (-u / 2)

/-- The archimedean cross written entirely in logarithmic lag coordinates.
The second summand is the exact renormalized Cauchy distribution associated
to the digamma kernel. -/
def bombieriLogArchimedeanCrossSymbol
    (f g : BombieriTest) : ℂ :=
  (∫ u : ℝ, ((bombieriLogPolarKernel u : ℝ) : ℂ) *
      bombieriCriticalCrossCorrelation f g u) +
    bombieriCrossDigammaCauchySeriesValue f g

/-- Exact physical-coordinate realization of the local critical cross. -/
theorem bombieriLocalCriticalForm_eq_logArchimedeanCrossSymbol
    (f g : BombieriTest) :
    bombieriLocalCriticalForm f g =
      bombieriLogArchimedeanCrossSymbol f g := by
  have hplus := integral_exp_mul_bombieriCriticalCrossCorrelation
    (1 / 2 : ℝ) f g
  rw [bombieriCriticalMoment_neg_half_eq_mellin_one,
    bombieriCriticalMoment_half_eq_mellin_zero] at hplus
  have hminus := integral_exp_mul_bombieriCriticalCrossCorrelation
    (-(1 / 2) : ℝ) f g
  rw [show -(-(1 / 2 : ℝ)) = 1 / 2 by ring,
    bombieriCriticalMoment_half_eq_mellin_zero,
    bombieriCriticalMoment_neg_half_eq_mellin_one] at hminus
  have hplusInt := exp_mul_bombieriCriticalCrossCorrelation_integrable
    (1 / 2 : ℝ) f g
  have hminusInt := exp_mul_bombieriCriticalCrossCorrelation_integrable
    (-(1 / 2) : ℝ) f g
  have hcritical :
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, bombieriLocalCriticalCrossIntegrand f g v) =
        bombieriCrossDigammaCauchySeriesValue f g := by
    simpa only [bombieriLocalCriticalCrossIntegrand,
      bombieriCriticalSpectralProduct, mellinLinearMap_apply,
      mul_assoc] using
      normalized_localCriticalKernel_crossProduct_eq_cauchySeries f g
  rw [bombieriLocalCriticalForm_apply]
  unfold bombieriLocalCriticalPairing
  rw [hcritical]
  simp only [mellinLinearMap_apply]
  rw [← hplus, ← hminus,
    ← integral_add hplusInt hminusInt]
  unfold bombieriLogArchimedeanCrossSymbol bombieriLogPolarKernel
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  push_cast
  ring_nf

/-- The nonnegative size of the symmetric arithmetic atom at `+- log (k+1)`.
The index `k = 0` is the vacuous `n = 1` atom. -/
def bombieriLogPrimeAtomWeight (k : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt (k + 1) *
    (Real.sqrt (((k + 1 : ℕ) : ℝ)))⁻¹

/-- The symmetric arithmetic part of the complete logarithmic cross. -/
def bombieriLogPrimeAtomCrossSummand
    (f g : BombieriTest) (k : ℕ) : ℂ :=
  ((bombieriLogPrimeAtomWeight k : ℝ) : ℂ) *
    (bombieriCriticalCrossCorrelation f g
        (-Real.log (((k + 1 : ℕ) : ℝ))) +
      bombieriCriticalCrossCorrelation f g
        (Real.log (((k + 1 : ℕ) : ℝ))))

/-- The symmetric arithmetic part of the complete logarithmic cross. -/
def bombieriLogPrimeAtomCrossSymbol
    (f g : BombieriTest) : ℂ :=
  ∑' k : ℕ, bombieriLogPrimeAtomCrossSummand f g k

/-- One directed Mangoldt shell is exactly the pair of logarithmic atoms at
opposite lags. -/
private theorem bombieriLogPrimeAtomSummand_eq_directedShell
    (f g : BombieriTest) (k : ℕ) :
    bombieriLogPrimeAtomCrossSummand f g k =
      (ArithmeticFunction.vonMangoldt (k + 1) : ℂ) *
        (bombieriDirectedCorrelation g f (k + 1 : ℕ) +
          starRingEnd ℂ
            (bombieriDirectedCorrelation f g (k + 1 : ℕ))) := by
  let n : ℝ := ((k + 1 : ℕ) : ℝ)
  have hn : 0 < n := by
    dsimp only [n]
    positivity
  have hsqrt : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [← Real.exp_log (Real.sqrt_pos.2 hn), Real.log_sqrt hn.le]
  have hsqrt0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hn).ne'
  have hfg :=
    bombieriCriticalCrossCorrelation_eq_exp_mul_star_directedCorrelation
      f g (Real.log n)
  have hgf :=
    bombieriCriticalCrossCorrelation_eq_exp_mul_star_directedCorrelation
      g f (Real.log n)
  rw [Real.exp_log hn, hsqrt] at hfg hgf
  have hneg := bombieriCriticalCrossCorrelation_neg_eq_star_swap
    f g (Real.log n)
  unfold bombieriLogPrimeAtomCrossSummand
  change ((ArithmeticFunction.vonMangoldt (k + 1) *
      (Real.sqrt n)⁻¹ : ℝ) : ℂ) *
        (bombieriCriticalCrossCorrelation f g (-Real.log n) +
          bombieriCriticalCrossCorrelation f g (Real.log n)) = _
  rw [hneg, hgf, hfg]
  simp only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
  push_cast
  field_simp [hsqrt0]
  norm_num [n, Nat.cast_add, Nat.cast_one]

/-- The complete polarized prime cross is precisely the symmetric atomic
logarithmic kernel, with no support restriction or truncation. -/
theorem bombieriPolarizedPrimeCross_eq_logPrimeAtomCrossSymbol
    (f g : BombieriTest) :
    bombieriPolarizedPrimeCross f g =
      bombieriLogPrimeAtomCrossSymbol f g := by
  rw [bombieriPolarizedPrimeCross_eq_primeDirectedShell]
  unfold bombieriPrimeDirectedShell bombieriLogPrimeAtomCrossSymbol
  apply tsum_congr
  intro k
  exact (bombieriLogPrimeAtomSummand_eq_directedShell f g k).symm

/-- The full translation-invariant logarithmic operator: the continuous/
renormalized archimedean distribution minus the symmetric Mangoldt atoms. -/
def bombieriCompleteLogKernelCrossSymbol
    (f g : BombieriTest) : ℂ :=
  bombieriLogArchimedeanCrossSymbol f g -
    bombieriLogPrimeAtomCrossSymbol f g

/-- Exact complete-kernel identity.  This is an unconditional structural
identity, rather than a reformulation of positivity or RH. -/
theorem bombieriCompleteLogKernelCrossSymbol_eq_globalCross
    (f g : BombieriTest) :
    bombieriCompleteLogKernelCrossSymbol f g =
      bombieriTwoBlockGlobalCrossSymbol f g := by
  unfold bombieriCompleteLogKernelCrossSymbol
  rw [← bombieriLocalCriticalForm_eq_logArchimedeanCrossSymbol,
    ← bombieriPolarizedPrimeCross_eq_logPrimeAtomCrossSymbol]
  rfl

/-- Common normalized dilation, i.e. common translation of the critical
logarithmic pullbacks, leaves the complete logarithmic kernel unchanged. -/
theorem bombieriCompleteLogKernelCrossSymbol_normalizedDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (f g : BombieriTest) :
    bombieriCompleteLogKernelCrossSymbol
        (normalizedDilation lambda hlambda f)
        (normalizedDilation lambda hlambda g) =
      bombieriCompleteLogKernelCrossSymbol f g := by
  rw [bombieriCompleteLogKernelCrossSymbol_eq_globalCross,
    bombieriCompleteLogKernelCrossSymbol_eq_globalCross]
  exact bombieriTwoBlockGlobalCrossSymbol_normalizedDilation
    lambda hlambda f g

/-- The real lag correlation used by the real-valued reduction. -/
def bombieriRealLogCorrelation
    (f g : BombieriTest) (u : ℝ) : ℝ :=
  (bombieriCriticalCrossCorrelation f g u).re

/-- The explicitly real archimedean logarithmic cross. -/
def bombieriRealLogArchimedeanCross
    (f g : BombieriTest) : ℝ :=
  (∫ u : ℝ, bombieriLogPolarKernel u *
      bombieriRealLogCorrelation f g u) +
    (bombieriCrossDigammaCauchySeriesValue f g).re

/-- The explicitly real symmetric Mangoldt atomic cross. -/
def bombieriRealLogPrimeAtomCross
    (f g : BombieriTest) : ℝ :=
  ∑' k : ℕ, bombieriLogPrimeAtomWeight k *
    (bombieriRealLogCorrelation f g
        (-Real.log (((k + 1 : ℕ) : ℝ))) +
      bombieriRealLogCorrelation f g
        (Real.log (((k + 1 : ℕ) : ℝ))))

private theorem bombieriLogPolarCross_integrable
    (f g : BombieriTest) :
    Integrable (fun u : ℝ ↦
      ((bombieriLogPolarKernel u : ℝ) : ℂ) *
        bombieriCriticalCrossCorrelation f g u) := by
  have hplus := exp_mul_bombieriCriticalCrossCorrelation_integrable
    (1 / 2 : ℝ) f g
  have hminus := exp_mul_bombieriCriticalCrossCorrelation_integrable
    (-(1 / 2) : ℝ) f g
  apply (hplus.add hminus).congr
  filter_upwards [] with u
  unfold bombieriLogPolarKernel
  push_cast
  ring_nf
  rfl

private theorem bombieriLogPrimeAtomCrossSummand_summable
    (f g : BombieriTest) :
    Summable (bombieriLogPrimeAtomCrossSummand f g) := by
  exact (bombieriPrimeDirectedShell_summable f g).congr fun k ↦
    (bombieriLogPrimeAtomSummand_eq_directedShell f g k).symm

/-- Taking the real part of the complex archimedean symbol gives the
displayed real lag integral. -/
theorem bombieriRealLogArchimedeanCross_eq_re
    (f g : BombieriTest) :
    bombieriRealLogArchimedeanCross f g =
      (bombieriLogArchimedeanCrossSymbol f g).re := by
  unfold bombieriRealLogArchimedeanCross
  unfold bombieriLogArchimedeanCrossSymbol
  rw [Complex.add_re]
  congr 1
  calc
    (∫ u : ℝ, bombieriLogPolarKernel u *
        bombieriRealLogCorrelation f g u) =
        ∫ u : ℝ, (((bombieriLogPolarKernel u : ℝ) : ℂ) *
          bombieriCriticalCrossCorrelation f g u).re := by
      apply integral_congr_ae
      filter_upwards [] with u
      unfold bombieriRealLogCorrelation
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    _ = (∫ u : ℝ, ((bombieriLogPolarKernel u : ℝ) : ℂ) *
          bombieriCriticalCrossCorrelation f g u).re :=
      integral_re (bombieriLogPolarCross_integrable f g)

/-- Taking the real part of the complex arithmetic symbol gives the
displayed real symmetric atomic series. -/
theorem bombieriRealLogPrimeAtomCross_eq_re
    (f g : BombieriTest) :
    bombieriRealLogPrimeAtomCross f g =
      (bombieriLogPrimeAtomCrossSymbol f g).re := by
  unfold bombieriRealLogPrimeAtomCross
  unfold bombieriLogPrimeAtomCrossSymbol
  rw [Complex.re_tsum (bombieriLogPrimeAtomCrossSummand_summable f g)]
  apply tsum_congr
  intro k
  unfold bombieriLogPrimeAtomCrossSummand bombieriRealLogCorrelation
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_re]

/-- The complete explicitly real lag kernel: archimedean distribution minus
the symmetric Mangoldt atoms. -/
def bombieriCompleteRealLogKernelCross
    (f g : BombieriTest) : ℝ :=
  bombieriRealLogArchimedeanCross f g -
    bombieriRealLogPrimeAtomCross f g

/-- The real complete kernel computes the real part of the global Hermitian
cross for arbitrary complex tests. -/
theorem bombieriCompleteRealLogKernelCross_eq_globalCross_re
    (f g : BombieriTest) :
    bombieriCompleteRealLogKernelCross f g =
      (bombieriTwoBlockGlobalCrossSymbol f g).re := by
  unfold bombieriCompleteRealLogKernelCross
  rw [bombieriRealLogArchimedeanCross_eq_re,
    bombieriRealLogPrimeAtomCross_eq_re,
    ← bombieriCompleteLogKernelCrossSymbol_eq_globalCross]
  rfl

/-- On coefficient-conjugation-fixed tests the complete kernel is genuinely
real, not merely a formula for the real part. -/
theorem bombieriCompleteLogKernelCrossSymbol_eq_ofReal_of_conjugate_fixed
    (f g : BombieriTest)
    (hf : bombieriConjugateTest f = f)
    (hg : bombieriConjugateTest g = g) :
    bombieriCompleteLogKernelCrossSymbol f g =
      ((bombieriCompleteRealLogKernelCross f g : ℝ) : ℂ) := by
  rw [bombieriCompleteLogKernelCrossSymbol_eq_globalCross]
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    exact (bombieriCompleteRealLogKernelCross_eq_globalCross_re f g).symm
  · simp only [Complex.ofReal_im]
    exact bombieriTwoBlockGlobalCrossSymbol_im_eq_zero_of_conjugate_fixed
      f g hf hg

/-- The diagonal specialization is exactly Bombieri's complete quadratic. -/
theorem bombieriFunctional_quadratic_re_eq_completeRealLogKernel
    (g : BombieriTest) :
    (bombieriFunctional (bombieriQuadraticTest g)).re =
      bombieriCompleteRealLogKernelCross g g := by
  rw [← bombieriTwoBlockGlobalCrossSymbol_self]
  exact (bombieriCompleteRealLogKernelCross_eq_globalCross_re g g).symm

/-- Every arithmetic atom has nonnegative magnitude. -/
theorem bombieriLogPrimeAtomWeight_nonneg (k : ℕ) :
    0 ≤ bombieriLogPrimeAtomWeight k := by
  unfold bombieriLogPrimeAtomWeight
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- The first nontrivial arithmetic atom has its exact classical weight. -/
theorem bombieriLogPrimeAtomWeight_one :
    bombieriLogPrimeAtomWeight 1 =
      Real.log 2 / Real.sqrt 2 := by
  unfold bombieriLogPrimeAtomWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime
    (by norm_num : Nat.Prime 2)]
  norm_num only [Nat.cast_ofNat, div_eq_mul_inv]

/-- Sharp sign obstruction: in the complete kernel the atom at each of
`+- log 2` occurs with this strictly negative coefficient. -/
theorem neg_bombieriLogPrimeAtomWeight_one_lt_zero :
    -bombieriLogPrimeAtomWeight 1 < 0 := by
  rw [bombieriLogPrimeAtomWeight_one]
  exact neg_neg_of_pos (div_pos (Real.log_pos (by norm_num)) (by positivity))

end

end ArithmeticHodge.Analysis.MultiplicativeWeilRealLogKernelStructural
