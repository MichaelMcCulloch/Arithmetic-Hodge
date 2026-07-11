import ArithmeticHodge.Analysis.ZetaZeroCount

namespace ArithmeticHodge.Analysis

/-- Functional-equation symmetry exchanges the upper and lower halves of the
critical strip, with analytic multiplicities preserved. -/
theorem xiCriticalStripZeroCount_lower_eq_upper_scratch (T : ℝ) :
    xiZeroCount 0 1 (-T) 0 = xiZeroCount 0 1 0 T := by
  simpa using xiZeroCount_one_sub 0 1 0 T

#print axioms xiCriticalStripZeroCount_lower_eq_upper_scratch

end ArithmeticHodge.Analysis
