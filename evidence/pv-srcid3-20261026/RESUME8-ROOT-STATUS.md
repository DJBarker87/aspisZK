# Source root-parent route

Accepted new source results (each exact source/object receipt is authoritative):

- PV_Src_ExternalCopy.source: for every U32[16] state, the owned extracted
  external_owned Result equals R0PoseidonCopy.external_linear exactly. The
  intermediate block loop, unreduced U64 column sums, output-lane recurrence,
  overflow bounds, canonicality and field model are proved symbolically.
- PV_Src_PortFullRoundCopy.initial and final_round: for canonical input state
  and canonical constant row, the actual nonlinear-loop/external-call body at
  PV_Src_ExternalReference.dictionary equals the modulo copy's full_round.
- PV_Src_PortInternalRoundCopy.source: for canonical state and constant below p,
  the actual internal-round Result body equals the modulo copy internal_round
  at the frozen INTERNAL_SHIFTS.
- PV_Src_Port{Initial,Internal,Final}RoundStep.source: each actual trace-loop
  iteration replaces its arithmetic body by the proved copy, retaining every
  callback Result and callback-state change. The named next-result premise
  describes the iterator operation, not an arithmetic correctness assumption.

Finite iterator composition and frozen constant-instance checks are separate
focused targets; acceptance is recorded only by their exact successful receipts.
The complete hash_fields/sponge-to-parent correspondence and initial plus twenty
adjacent parent equations remain open. Lean parent cells remain 0 -> 0/21.
PV_Src_RootCertificate.source_eq is unchanged and still requires all 21 parent
cells at the same explicit dictionary. No literal root table replaces the helper.

The full-helper prefix11 comparison, unwind33, was retried once under ruling(i)
with taskset0-3 and 900s timeout. It timed out at900.003123s, exit124,
cgroup peak5141737472 bytes, swap0. This is not equality evidence or a checked
counterexample. Metadata confirms no stubs and no verified stubs. The split
prefix01 comparison is prepared under cfg(kani); its receipt determines status.

No deployed premise is removed. RunJoin's newly published external P6 gate is
retained read-only; Records/R_shipped and the installed native compiler return,
selected compilation, public/snapshot binding and non-vacuity remain missing.
The deployed five fields remain 5 -> 5. L1/L2/L3, E1/E2, actual RunJoin,
proof-account client association, simE and the complete observer are unchanged.
Target not yet established.
