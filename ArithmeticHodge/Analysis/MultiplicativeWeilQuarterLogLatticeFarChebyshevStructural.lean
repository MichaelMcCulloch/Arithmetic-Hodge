import ArithmeticHodge.Analysis.MultiplicativeWeilCorrectedChebyshevPotentialStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeGramStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeFarChebyshevStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilCorrectedChebyshevPotentialStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilQuarterLogLatticeGramStructural

/-!
# Corrected Chebyshev representation of quarter-lattice far crosses

A normalized quarter-lattice seed is supported in `[1, q₂]`, where
`q₂ = sqrt 2`.  Consequently a relative dilation by `qₖ` is strictly
separated as soon as `3 ≤ k`.  Thus every lag beyond the two Fejer-tapered
neighbor lags has the exact Chebyshev-error plus corrected-potential form.
-/

/-- Quarter-lattice points are strictly increasing. -/
theorem quarterLogLatticePoint_strictMono :
    StrictMono quarterLogLatticePoint := by
  intro m n hmn
  unfold quarterLogLatticePoint
  apply Real.exp_lt_exp.mpr
  apply mul_lt_mul_of_pos_right
  · exact_mod_cast hmn
  · have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity

/-- Every lag at least three separates two normalized quarter-lattice
supports. -/
theorem quarterLogLatticePoint_two_lt_of_three_le
    (k : ℤ) (hk : 3 ≤ k) :
    quarterLogLatticePoint 2 < quarterLogLatticePoint k := by
  exact quarterLogLatticePoint_strictMono (lt_of_lt_of_le (by omega) hk)

/-- Every normalized quarter-lattice cross at lag at least three has the
corrected-potential form. -/
theorem sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_quarterLogLattice_far_eq_chebyshevError_add_correctedPotential
    (f g : BombieriTest) (k : ℤ) (hk : 3 ≤ k)
    (hf : tsupport f ⊆ Set.Icc 1 (quarterLogLatticePoint 2))
    (hg : tsupport g ⊆ Set.Icc 1 (quarterLogLatticePoint 2)) :
    ((Real.sqrt (quarterLogLatticePoint k) : ℝ) : ℂ) *
        bombieriTwoBlockGlobalCrossSymbol f
          (normalizedDilation (quarterLogLatticePoint k)
            (quarterLogLatticePoint_pos k) g) =
      (∫ x : ℝ in Set.Ioi 0,
        ((Chebyshev.psi (quarterLogLatticePoint k * x) -
            quarterLogLatticePoint k * x : ℝ) : ℂ) *
          deriv (fun y : ℝ ↦
            starRingEnd ℂ (bombieriDirectedCorrelation f g y)) x) +
      ∫ x : ℝ in Set.Ioi 0,
        ((correctedChebyshevPotential
            (quarterLogLatticePoint k * x) : ℝ) : ℂ) *
          deriv (fun y : ℝ ↦
            starRingEnd ℂ (bombieriDirectedCorrelation f g y)) x := by
  apply
    sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_chebyshevError_add_correctedPotential
      f g (quarterLogLatticePoint_pos k)
      (by norm_num) (by norm_num) (quarterLogLatticePoint_pos 2) hf hg
  simpa only [div_one] using
    quarterLogLatticePoint_two_lt_of_three_le k hk

/-- Actual physical quarter-lattice cells inherit the lag-three-and-beyond
corrected-potential formula.  The right side depends only on the signed lag
and the two normalized seeds. -/
theorem sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_quarterLogLatticeRescale_far_eq_chebyshevError_add_correctedPotential
    (n m : ℤ) (f g : BombieriTest) (hfar : 3 ≤ n - m)
    (hf : tsupport f ⊆ Set.Icc 1 (quarterLogLatticePoint 2))
    (hg : tsupport g ⊆ Set.Icc 1 (quarterLogLatticePoint 2)) :
    ((Real.sqrt (quarterLogLatticePoint (n - m)) : ℝ) : ℂ) *
        bombieriTwoBlockGlobalCrossSymbol
          (quarterLogLatticeRescale n f)
          (quarterLogLatticeRescale m g) =
      (∫ x : ℝ in Set.Ioi 0,
        ((Chebyshev.psi (quarterLogLatticePoint (n - m) * x) -
            quarterLogLatticePoint (n - m) * x : ℝ) : ℂ) *
          deriv (fun y : ℝ ↦
            starRingEnd ℂ (bombieriDirectedCorrelation f g y)) x) +
      ∫ x : ℝ in Set.Ioi 0,
        ((correctedChebyshevPotential
            (quarterLogLatticePoint (n - m) * x) : ℝ) : ℂ) *
          deriv (fun y : ℝ ↦
            starRingEnd ℂ (bombieriDirectedCorrelation f g y)) x := by
  rw [bombieriTwoBlockGlobalCrossSymbol_quarterLogLatticeRescale]
  exact
    sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_quarterLogLattice_far_eq_chebyshevError_add_correctedPotential
      f g (n - m) hfar hf hg

end

end ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeFarChebyshevStructural
