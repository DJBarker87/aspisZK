# S3/S9 exact helper source-cut extraction evidence

This is a source-cut extraction artifact, not a Lean proof packet and not an
accepted Rust refinement. The copied bodies of `kpowers`,
`factored_s2_libra_weights`, and `Weights::scalar_factor` match the retained
`weights.rs` source spans byte-for-byte; `check_source_cut.py` verifies those
spans and requires each complete copied body exactly once in `input/lib.rs`.
The input `Pair::pair` is a normalized candidate body, not the frozen source `Pair::pair` (the method hashes and lengths are recorded in `manifest.json`). The free root `pair_root` forwards to this candidate method. Thus the emitted Pair is not a source re-pin; helper source equivalence, candidate-method equivalence, and caller control-flow/result refinement remain separate open obligations.

The NUC Charon command exited 0 and produced a nonempty valid `Pair.llbc`
(708 KiB, `has_errors=false`, 164 function declarations). Its runner then
exited 1 after the command because a receipt-construction variable was only
initialized on the Aeneas branch. The retained `runs/charon-v1/receipt.json`
is a forensic subprocess receipt rebuilt from the preserved command, GNU-time
log, stdout, reservation, and LLBC. It records both subprocess exit 0 and
wrapper exit 1. Do not relabel this as a clean runner receipt. The script bug
was fixed before Aeneas; no source or tool input changed.

Aeneas then completed successfully under a fresh 2 GiB high / 3 GiB max / zero
swap cgroup. It emitted nonempty `Types.lean`, `Funs.lean`, external template,
and translation map. `translation.json` declares the three expected functions:
`weights.kpowers`, `weights.Weights.scalar_factor`, and
`weights.factored_s2_libra_weights`.

The generated Lean is diagnostic only. `Funs.lean` has generated
`maxHeartbeats=1000000` and `maxRecDepth=2048` overrides, which are forbidden
for accepted work and have not been stripped or compiled. The external
Aeneas template declares `core.array.from_fn` and
`Iterator.fold.default` as axioms. Both must be replaced by reviewed P6
operation models in a mechanically checked, option-clean adapter before any
axiom audit or semantic proof. The copied extraction harness defines the six field-operation bodies as `do fail panic` stubs: `QM31.mul`, `QM31.square`, `WideExact.add`, `WideExact.mul`, `WideExact.mul_m31`, and `WideExact.mul_qm31`. These are not implementations of the frozen field methods and cannot be used to prove the helper result. The next adapter must replace each with a typed operation slot and connect those slots to accepted field owners. No Lean compile, `#print
axioms`, or Rust differential test is included here.

The source-level algebra check is only an explanatory map: the helper computes
the four `S2LibraFactoredIdentity.factored` coefficient expressions when its
field operations satisfy the corresponding algebra. It is not a proof of those
operations or of the caller. Whole `Weights::pair` and its result/state join to
`OraclePortFrozenOrder.dV_frozen` remain open.


The current extraction does **not** translate the frozen `Weights::pair` method. The input method is a normalized candidate whose transformations are not proved equivalent to the frozen method. In particular, do not consume the emitted Pair body as an accepted production/source theorem. The extraction is useful only as helper-emission evidence and a candidate cut for subsequent operation/model work.
