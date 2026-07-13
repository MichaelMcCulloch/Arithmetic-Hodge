import ArithmeticHodge.Analysis.MultiplicativeWeilTwoBumpSpectralSymbol
import ArithmeticHodge.Analysis.YoshidaRenormalizedGeometricKernel

set_option autoImplicit false

open Real
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoAdjacentKernel

open YoshidaRenormalizedGeometricKernel

noncomputable section

/-!
# Rank-one series for the factor-two adjacent-cell kernel

The growing polar exponential cancels the first term of the digamma geometric
series exactly.  Keeping the remaining series intact is the structural form
needed for a dimension-free Schur or Bessel estimate.
-/

def factorTwoAdjacentSmoothKernel (t : ℝ) : ℝ :=
  2 * Real.cosh (t / 2) - oddKernel t / 2

theorem factorTwoAdjacentSmoothKernel_eq_exp_sub_tsum
    {t : ℝ} (ht : 0 < t) :
    factorTwoAdjacentSmoothKernel t =
      Real.exp (t / 2) -
        ∑' m : ℕ, Real.exp (-oddRate (m + 1) * t) := by
  have hall := hasSum_oddExponentials ht
  have hscaled := hall.mul_left (1 / 2 : ℝ)
  have hscaled' :
      HasSum (fun k : ℕ ↦ Real.exp (-oddRate k * t))
        (oddKernel t / 2) := by
    convert hscaled using 1
    · funext k
      ring
    · rw [oddKernelSeriesForm_eq_oddKernel ht.ne']
      ring
  have htail :
      HasSum (fun m : ℕ ↦ Real.exp (-oddRate (m + 1) * t))
        (oddKernel t / 2 - Real.exp (-oddRate 0 * t)) := by
    simpa only [Finset.sum_range_one] using
      (hasSum_nat_add_iff' 1).2 hscaled'
  rw [htail.tsum_eq]
  unfold factorTwoAdjacentSmoothKernel
  rw [Real.cosh_eq]
  unfold oddRate
  norm_num
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoAdjacentKernel
