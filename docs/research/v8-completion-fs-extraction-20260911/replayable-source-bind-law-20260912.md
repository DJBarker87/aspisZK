# Replayable source dependent bind law — 2026-09-12

`lean/FSV8ReplayableSourceBindLaw.lean` proves the causal finite-tape
composition for the replayable source. The preprogram is run first; only a
`MachineHalt.returned observation` starts the continuation, instantiated with
that observation's body and initial digest. Oracle abort and out-of-fuel
halts remain terminal and do not start a verifier script.

The current finite-tape interpreter and compiled V7 OracleMachine are equal
pointwise under explicit total/fresh/tape room bounds, and their pushforward
PMFs over the uniform finite tape are equal. The promoted theorems are
`replayableBind_pointwise_eq` and `replayableBind_current_law_eq_v7_law`.

This is an exact finite-tape/current-to-V7 dependent composition only. It does
not construct the actual adversary capability or Rust/Aeneas source adapter,
and does not prove programmed-fork/K1.6 scheduling or deployed ROM coupling.
Those remain explicit next adapters; no acceptance or independence claim is
made.

Evidence is recorded in
`results/v8-completion-fs-extraction-20260911/replayable-source-bind-law-v1/report.json`.
