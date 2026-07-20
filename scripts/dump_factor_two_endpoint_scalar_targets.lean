import ArithmeticHodge.Analysis.YoshidaFactorTwoCleanEntryTargets

/-!
# Exact factor-two endpoint scalar target dump

Run from the repository root with:

```text
lake env lean --run scripts/dump_factor_two_endpoint_scalar_targets.lean
```

The output is a single JSON value.  Rational endpoints are emitted in their
normalized Lean `Rat` representation as `[numerator, denominator]` pairs.
Only the scalar target tables are evaluated; no matrix entries are formed.
-/

open ArithmeticHodge.Analysis
open ArithmeticHodge.Analysis.YoshidaEvenIntervalCertificate
open ArithmeticHodge.Analysis.YoshidaFactorTwoCleanEntryTargets
open ArithmeticHodge.Analysis.YoshidaFactorTwoScalarTargetSelectors

private def ratPairJson (q : ℚ) : String :=
  "[" ++ toString q.num ++ "," ++ toString q.den ++ "]"

private def intervalJson (I : RatInterval) : String :=
  "{\"lower\":" ++ ratPairJson I.lower ++
    ",\"upper\":" ++ ratPairJson I.upper ++ "}"

private def modeIntervalJson (mode : Nat) (I : RatInterval) : String :=
  "{\"mode\":" ++ toString mode ++
    ",\"lower\":" ++ ratPairJson I.lower ++
    ",\"upper\":" ++ ratPairJson I.upper ++ "}"

private def writeTable (name : String) (target : Fin 201 → RatInterval) : IO Unit := do
  IO.print ("    \"" ++ name ++ "\":[")
  for i in List.finRange 201 do
    if i.val != 0 then
      IO.print ","
    IO.print (modeIntervalJson i.val (target i))
  IO.print "]"

def main : IO Unit := do
  IO.println "{"
  IO.println "  \"schema\":\"arithmetic-hodge.factor-two-endpoint-scalars.v1\","
  IO.println "  \"mode_range\":[0,200],"
  IO.println "  \"tables\":{"
  writeTable "S" (fun i ↦ cleanSineTarget i.val)
  IO.println ","
  writeTable "D" (fun i ↦ cleanDiagonalTarget i.val)
  IO.println ","
  writeTable "s" symmetricSinTarget
  IO.println ","
  writeTable "c" symmetricAffineCosTarget
  IO.println ""
  IO.println "  },"
  IO.println "  \"constants\":{"
  IO.println ("    \"invPi\":" ++ intervalJson evenInvPiInterval ++ ",")
  IO.println ("    \"invSqrtTwo\":" ++ intervalJson evenInvSqrtTwoInterval ++ ",")
  IO.println ("    \"endpointScale\":" ++ intervalJson factorTwoEndpointScaleTarget)
  IO.println "  }"
  IO.println "}"
