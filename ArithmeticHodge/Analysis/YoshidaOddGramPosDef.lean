import ArithmeticHodge.Analysis.YoshidaDiagonalMomentEnclosures
import ArithmeticHodge.Analysis.YoshidaOddRealSpaceAssembly
import ArithmeticHodge.Analysis.YoshidaSineMomentEnclosures

set_option autoImplicit false

open scoped ComplexOrder

namespace ArithmeticHodge.Analysis.YoshidaOddGramPosDef

noncomputable section

open YoshidaDiagonalMomentEnclosures
open YoshidaOddGramPrefix
open YoshidaOddIntervalCertificate
open YoshidaOddMomentTargets
open YoshidaOddRealSpaceAssembly
open YoshidaSineMomentEnclosures

/-!
# Unconditional positivity of Yoshida's complete odd low-mode block

The exact clipped/moment bridge and the proof-producing sine and diagonal
enclosures discharge every hypothesis of the interval Schur certificate.
-/

/-- The actual clipped ten-mode odd Gram matrix is positive definite. -/
theorem clippedOddFullGram_posDef : clippedOddFullGram.PosDef :=
  clippedOddFullGram_posDef_of_bridge_and_target_enclosures
    clippedOddFullMomentBridge
    sineTargetEnclosures_from_series192
    diagonalTargetEnclosures_from_certificate

end


end ArithmeticHodge.Analysis.YoshidaOddGramPosDef
