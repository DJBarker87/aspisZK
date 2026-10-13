# Focused final-response extraction

`FinalResponses.lean` was compiled as `R1FinalResponses` in the pinned
`aspis-r1-concrete-decoder-20261013` Lean cache. The successful source SHA256
is `041f6abb554f333b560ec3edbf907d2800d9a4c0338f418aef19ed6d06fbdbfa`.
Attempt h exited 0 in 1.52 s, with peak RSS 3,143,876 KiB and zero swap, under
`MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`, Lean
threshold 5000 MB. Its `#print axioms` results for all four exported theorems
are `[propext, Classical.choice, Quot.sound]`; none reports `sorryAx`.

The additional direct import
`Mathlib.AlgebraicTopology.SimplexCategory.Basic` is a cache-closure repair for
the existing `Wide.Terminal` declaration. In that module the generated
`Fintype` instance for `ToType` can be selected for a concrete `Fin` domain.
Earlier attempts d-g exposed the missing generated symbol
`SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat` when that
declaration was specialized without importing its defining module. Attempt h
imports that narrow Mathlib module and uses the same instance environment; it
does not alter theorem statements, thresholds, or premises. The failed attempt
logs, source hashes, resource receipts, and timing logs are retained here.

The narrow import-only change to
`AspisFormal/K1/V7ExactCorrelatedAgreementIncidence.lean` also compiled as
`AspisFormal/K1/V7ExactCorrelatedAgreementIncidence` (attempt b, exit 0, 0.85 s,
peak RSS 1,673,128 KiB, zero swap; source SHA256
`b9c9db627bdfd6e615a5bfae1dbbe70c336af1137799308e41b749650dc9da98`). Its
two printed axiom sets are `[propext, Classical.choice, Quot.sound]`.

These are focused Lean compilation results only; they are not a full package or
release replay.
