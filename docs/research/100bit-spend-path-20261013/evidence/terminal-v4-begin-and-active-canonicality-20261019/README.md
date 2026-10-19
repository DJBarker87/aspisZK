# Terminal v4 begin μ/zc and active-literal proof packet

This packet freezes checked proof artifacts and selected failed diagnostics. It does not claim the full active selector-loop induction.

## Green results

- `TerminalV4PublicSoundnessWithBeginMuV2.terminal_success_arithmetic_of_actual_begin`: the actual begin-path arithmetic result including μ/zc. Frozen successful attempt is v2d. Source SHA `c82d72e341f3588cc4f4032a78fb49533e78dca9098c0e5f8d71772038951181`, object SHA `2e870821bcf7692da205e615fd654c93203a943d5dbf0edec816067a012149d4`. Exit 0, 39.08 s, max RSS 2,684,485,632 B, process swaps 0. `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
- `TerminalV4ActiveLiteralCanonical.sum_6144_success_canonical`: concrete sparse mask 6144 canonicality; helper covers the second selected bit at mask 4096. Source SHA `051a6fe0925ee3aac76edf90300a7b60493dc60a89cb5c9cf71f6b3351ffc8e9`, object SHA `16f872a3a32977dcfe68772300ceae4170388ff1078b095db05a99f01dd3c5ef`. Exit 0, 5.51 s, max RSS 2,263,515,136 B, process swaps 0.
- `TerminalV4ActiveLiteralLoopCanonical.active_loop_good`: generic actual-loop induction, conditional on `maskStepOK` for every block (the concrete full mask-table premise is not yet derived). Source SHA `c206c829d6da2abff4000eda7659ec9efd6568a4c99ce6ad186e1b45853a0814`, object SHA `c567dc91bfdc5bc085590dc537e0e216a80fac539902f88813e580a3bf059e19`. Exit 0, 12.00 s, max RSS 2,212,446,208 B, process swaps 0.
- Both active-literal theorem axiom audits report only `[propext, Classical.choice, Quot.sound]`; exact audit sources and logs are included.

## Open proof gap and failed diagnostics

The attempted generic selector-loop induction is **not proved**. Failed v4, v5, and v6 sources/logs/receipts are retained under `attempts/failed-*`. Latest v6 failed with array-index success application mismatches and recursive-loop alias transport mismatches; no object was produced. Next useful proof work is a generic Result-bind/index-success lemma or a finite mask-table proof discharging `maskStepOK` for the actual masks.

## Reproducibility and dependency roots

Each successful attempt directory contains the exact Lean command, frozen source, log, and receipt. Receipts record full ordered `LEAN_PATH`; this packet includes the produced OLean artifacts but not the entire transitive dependency cache. The direct source imports are listed in those receipts. Lean 4.32.0 was used. `SHA256SUMS` covers every packet file other than itself and the archive.
