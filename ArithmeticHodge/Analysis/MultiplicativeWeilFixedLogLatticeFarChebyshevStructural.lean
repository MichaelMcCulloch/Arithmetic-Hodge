import ArithmeticHodge.Analysis.MultiplicativeWeilFixedLogLatticeGramStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMangoldtDiscrepancyAbelStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFixedLogLatticeFarChebyshevStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMangoldtDiscrepancyAbelStructural

/-!
# Exact Chebyshev form of the far fixed-lattice band

Three half-octave lattice steps already have relative scale strictly larger
than two.  Thus every positive lattice lag at least three lies in the strict
support-separation regime of the physical Abel identity.
-/

/-- Every fixed half-octave lattice point from lag three onward is strictly
larger than two. -/
theorem two_lt_fixedLogLatticePoint_of_three_le
    {k : ℤ} (hk : 3 ≤ k) :
    2 < fixedLogLatticePoint k := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkReal : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have harg :
      Real.log 2 < (k : ℝ) * (Real.log 2 / 2) := by
    calc
      Real.log 2 < (3 : ℝ) * (Real.log 2 / 2) := by
        nlinarith
      _ ≤ (k : ℝ) * (Real.log 2 / 2) :=
        mul_le_mul_of_nonneg_right hkReal (by positivity)
  calc
    (2 : ℝ) = Real.exp (Real.log 2) :=
      (Real.exp_log (by norm_num : (0 : ℝ) < 2)).symm
    _ < Real.exp ((k : ℝ) * (Real.log 2 / 2)) :=
      Real.exp_lt_exp.mpr harg
    _ = fixedLogLatticePoint k := rfl

/-- At every positive fixed-lattice lag at least three, the complete global
cross is exactly the Chebyshev-error pairing minus the nonsingular physical
kernel, with all separation hypotheses discharged by base support `[1,2]`.
-/
theorem sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_fixedLogLattice_far_eq_chebyshevError_sub_kernel
    (f g : BombieriTest) (k : ℤ) (hk : 3 ≤ k)
    (hf : tsupport f ⊆ Set.Icc 1 2)
    (hg : tsupport g ⊆ Set.Icc 1 2) :
    ((Real.sqrt (fixedLogLatticePoint k) : ℝ) : ℂ) *
        bombieriTwoBlockGlobalCrossSymbol f
          (normalizedDilation (fixedLogLatticePoint k)
            (fixedLogLatticePoint_pos k) g) =
      (∫ x : ℝ in Set.Ioi 0,
        ((Chebyshev.psi (fixedLogLatticePoint k * x) -
            fixedLogLatticePoint k * x : ℝ) : ℂ) *
          deriv (fun y : ℝ ↦
            starRingEnd ℂ (bombieriDirectedCorrelation f g y)) x) -
      ∫ x : ℝ in Set.Ioi 0,
        starRingEnd ℂ (bombieriDirectedCorrelation f g x) /
          ((x * ((fixedLogLatticePoint k * x) ^ 2 - 1) : ℝ) : ℂ) := by
  apply
    sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_chebyshevError_sub_kernel
      f g (fixedLogLatticePoint_pos k)
      (by norm_num) (by norm_num) (by norm_num) hf hg
  simpa only [div_one] using two_lt_fixedLogLatticePoint_of_three_le hk

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFixedLogLatticeFarChebyshevStructural
