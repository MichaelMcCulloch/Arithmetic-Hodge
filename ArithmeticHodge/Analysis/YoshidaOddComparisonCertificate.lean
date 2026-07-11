import ArithmeticHodge.Analysis.RationalPosDefCertificate

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace ArithmeticHodge.Analysis

/-!
# Exact odd Yoshida comparison certificate

This module stores the rational `10 × 10` comparison matrix for Yoshida's odd
block and replays its exact `LDLᴴ` factorization.  The resulting positive
definiteness theorems are purely algebraic; the analytic comparison with the
true corrected Gram matrix is a separate obligation.
-/

def yoshidaOddComparison10 : Matrix (Fin 10) (Fin 10) ℚ := ![
  ![63 / 512, -(91 / 512), -(73 / 512), -(31 / 256), -(27 / 256),
    -(49 / 512), -(45 / 512), -(41 / 512), -(39 / 512), -(37 / 512)],
  ![-(91 / 512), 117 / 128, -(63 / 512), -(55 / 512), -(25 / 256),
    -(23 / 256), -(21 / 256), -(5 / 64), -(37 / 512), -(9 / 128)],
  ![-(73 / 512), -(63 / 512), 347 / 256, -(25 / 256), -(23 / 256),
    -(43 / 512), -(5 / 64), -(19 / 256), -(9 / 128), -(17 / 256)],
  ![-(31 / 256), -(55 / 512), -(25 / 256), 851 / 512, -(43 / 512),
    -(5 / 64), -(19 / 256), -(9 / 128), -(17 / 256), -(33 / 512)],
  ![-(27 / 256), -(25 / 256), -(23 / 256), -(43 / 512), 243 / 128,
    -(19 / 256), -(9 / 128), -(17 / 256), -(33 / 512), -(1 / 16)],
  ![-(49 / 512), -(23 / 256), -(43 / 512), -(5 / 64), -(19 / 256),
    1069 / 512, -(35 / 512), -(33 / 512), -(1 / 16), -(31 / 512)],
  ![-(45 / 512), -(21 / 256), -(5 / 64), -(19 / 256), -(9 / 128),
    -(35 / 512), 1151 / 512, -(1 / 16), -(31 / 512), -(15 / 256)],
  ![-(41 / 512), -(5 / 64), -(19 / 256), -(9 / 128), -(17 / 256),
    -(33 / 512), -(1 / 16), 1221 / 512, -(15 / 256), -(29 / 512)],
  ![-(39 / 512), -(37 / 512), -(9 / 128), -(17 / 256), -(33 / 512),
    -(1 / 16), -(31 / 512), -(15 / 256), 1283 / 512, -(29 / 512)],
  ![-(37 / 512), -(9 / 128), -(17 / 256), -(33 / 512), -(1 / 16),
    -(31 / 512), -(15 / 256), -(29 / 512), -(29 / 512), 1339 / 512]
]

def yoshidaOddComparison10L : Matrix (Fin 10) (Fin 10) ℚ := ![
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-(13 / 9), 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-(73 / 63), -(1516 / 3029), 1, 0, 0, 0, 0, 0, 0, 0],
  ![-(62 / 63), -(1301 / 3029), -(4117424 / 11133845), 1, 0, 0, 0, 0, 0, 0],
  ![-(6 / 7), -(1152 / 3029), -(3660376 / 11133845),
    -(2393365603 / 7304709298), 1, 0, 0, 0, 0, 0],
  ![-(7 / 9), -(1051 / 3029), -(3354834 / 11133845),
    -(2192178737 / 7304709298), -(1760017649575 / 5477401595643),
    1, 0, 0, 0, 0],
  ![-(5 / 7), -(963 / 3029), -(3089189 / 11133845),
    -(2027738007 / 7304709298), -(1627763048717 / 5477401595643),
    -(1518811051261949 / 4415794839266231), 1, 0, 0, 0],
  ![-(41 / 63), -(893 / 3029), -(2865971 / 11133845),
    -(1881100503 / 7304709298), -(1509697178105 / 5477401595643),
    -(1408561517935355 / 4415794839266231),
    -(1444423476414783536 / 3675102233535782813), 1, 0, 0],
  ![-(13 / 21), -(840 / 3029), -(542387 / 2226769),
    -(889422340 / 3652354649), -(1434082146950 / 5477401595643),
    -(1338065551138682 / 4415794839266231),
    -(1372141434824927612 / 3675102233535782813),
    -(503644873903627025147 / 1003557538322298450899), 1, 0],
  ![-(37 / 63), -(805 / 3029), -(2579123 / 11133845),
    -(850704252 / 3652354649), -(1371762612668 / 5477401595643),
    -(1279890564942179 / 4415794839266231),
    -(1312431114375892414 / 3675102233535782813),
    -(481710145333908751425 / 1003557538322298450899),
    -(286934058981571001518729 / 358843898432320643688653), 1]
]

def yoshidaOddComparison10D : Fin 10 → ℚ := ![
  63 / 512,
  3029 / 4608,
  11133845 / 10855936,
  3652354649 / 2850264320,
  5477401595643 / 3740011160576,
  4415794839266231 / 2804429616969216,
  3675102233535782813 / 2260886957704310272,
  3010672614966895352697 / 1881652343570320800256,
  358843898432320643688653 / 256910729810508403430144,
  32550872422740888070024259 / 45932018999337042392147584
]

private theorem yoshidaOddComparison10L_isUnit :
    IsUnit yoshidaOddComparison10L := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have htri : yoshidaOddComparison10L.BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> simp_all [yoshidaOddComparison10L]
  rw [Matrix.det_of_lowerTriangular yoshidaOddComparison10L htri]
  norm_num [yoshidaOddComparison10L, Fin.prod_univ_succ]

private theorem yoshidaOddComparison10D_pos :
    ∀ i, 0 < yoshidaOddComparison10D i := by
  decide +kernel

set_option maxHeartbeats 10000000 in
private theorem yoshidaOddComparison10_factorization :
    yoshidaOddComparison10 =
      yoshidaOddComparison10L * Matrix.diagonal yoshidaOddComparison10D *
        yoshidaOddComparison10Lᴴ := by
  decide +kernel

set_option maxHeartbeats 10000000 in
theorem yoshidaOddComparison10_posDef_real : Matrix.PosDef
    ((Rat.castHom ℝ).mapMatrix yoshidaOddComparison10) := by
  exact rationalLDL_posDef_real
    yoshidaOddComparison10 yoshidaOddComparison10L yoshidaOddComparison10D
    yoshidaOddComparison10L_isUnit yoshidaOddComparison10D_pos
    yoshidaOddComparison10_factorization

set_option maxHeartbeats 10000000 in
theorem yoshidaOddComparison10_posDef_complex : Matrix.PosDef
    ((Rat.castHom ℂ).mapMatrix yoshidaOddComparison10) := by
  exact rationalLDL_posDef_complex
    yoshidaOddComparison10 yoshidaOddComparison10L yoshidaOddComparison10D
    yoshidaOddComparison10L_isUnit yoshidaOddComparison10D_pos
    yoshidaOddComparison10_factorization

end ArithmeticHodge.Analysis
