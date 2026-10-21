# Checkpoint ABI pass 5

Base `30e4f18dbd541c5b2f9fa90afa9c1cab92fd21ba`, branch
`codex/cx-ckpt-abi5-20261021`. New Lean modules only. No shipped source,
protected candidate, sibling module, wallet/key or ELF modification.
No push or merge. Complete checkpoint source join remains open.

## Stage 1: short-circuit reference to the new checkpoint stage

`OraclePortCkptAbi5Stage.stage_observation` proves exact evaluation equality
between the saved-ten short-circuit reference (whose decoded result drives
twelve continuation steps) and `OraclePortCheckpointOracleC5.writeResume`.
It holds for every oracle world and arbitrary retained proof/public bytes,
with distinct queries. Both ordered address/answer log and returned state
are equal; all six reads, including repeats, are retained.

`reached_stage` specializes this equality to the actual
`OraclePortFrozen2.checkpoint`, constructing Context from p/i/v as that stage
does. It derives distinctness from `input p q tr = some i` and
`queries tr = some q`, without assuming final acceptance or a supplied
unique-query fact. These are **model/reference** hypotheses and results,
not Rust Prepared/Accumulator provenance or a source cone inhabitant.

Attempt 2 exits 0: 16.933184292 seconds, peak RSS 3,581,673,472 bytes,
zero swaps, revision `30e4f18dbd541c5b2f9fa90afa9c1cab92fd21ba`.
Both axiom lines are `[propext, Classical.choice, Quot.sound]`.
The first attempt's incorrect qualified sampler name is retained as a failed
receipt; its compiler-recovery axiom output is excluded from proof evidence.
Exact targets, argv, source/import hashes, dependencies and full output are
in `manifest.json` and per-attempt directories. The shared mkdir lock and
private objects are used; no shared object is overwritten.

This closes pass 4's *reference/model stage mismatch* under the reached
sampler domain. The model now accounts for the reads. It does not close
actual Rust byte, allocation or caller lowering, or the enriched two-pass
AcceptedRunJoin. No headline premise is removed.
