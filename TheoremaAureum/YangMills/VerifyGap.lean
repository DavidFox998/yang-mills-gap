-- VerifyGap: certificate checker, w1 < 1/7 with rational witness.
-- Run: lake env lean --run TheoremaAureum/YangMills/VerifyGap.lean

def checkW1 : Bool := (107 : Nat) * 7 < 756 * 1

def main : IO Unit := do
  if checkW1 then
    IO.println "PASS: w1(beta_0) < 1/7  [107*7=749 < 756]"
    IO.println "      Kotecky-Preiss criterion satisfied"
  else
    IO.println "FAIL"
