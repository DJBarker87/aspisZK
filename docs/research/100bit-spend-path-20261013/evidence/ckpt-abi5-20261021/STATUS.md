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

## Stage 2: canonical C5 representation

`OraclePortCkptAbi5Codec.c5_k_bytes` identifies C5.encodeK itself with the
complete four-word LE32 byte list in emitted c0.a/c0.b/c1.a/c1.b order.
`c5_wide_halves` and `c5_e_bytes` identify C5.encodeE with all eight raw
words in c0-then-c1 order. `decoded_k_bytes` / `decoded_e_bytes` obtain the
required canonicality from success of the extracted strict reference
decoders. No raw noncanonical writer value is silently quotiented.

These close the previously missing **C5 side** of the representation
bridge. They do not state that extracted encode_k/e_byte/body_byte returns
those bytes, or identify the production reader with decode_k_spec/e_spec.
All 18 body fields and checksum still need complete source identification.

Attempt 4 exits 0: 29.148580375 seconds, peak RSS 3,117,940,736 bytes,
zero swaps, revision `ca3caa95e`. All five new theorem axiom reports are
`[propext, Classical.choice, Quot.sound]`. Attempts 1–3 are retained:
finite-list length simplification, div-by-one at four limb boundaries and
the actual List.ofFn_add/pair equivalence interface needed explicit proofs.
No failed compiler-recovery axiom output is accepted. No resource cap changed.
