# S4 finite scan trace to `scanOut`

This source-only packet contains a generic finite `Run` relation and a proof that every such run evaluates `R0C.V3.Q22.scanOut` to the selected finish result and final state. The stopped constructor permits the fallback initial state to differ from the selected advance, matching `scanOut` behavior. The module does not claim a concrete `DriverTrace` conversion; D18 is proving that source-specific bridge separately.

Validation used Lean 4.32 with the exact profile in `receipt/LEAN_PATH.txt`. The successful focused target, time log, compiler log, and resource receipt are retained in `receipt/`. No compiled objects are included.
