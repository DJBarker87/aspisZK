# Checkpoint ABI pass 3

Branch `codex/cx-ckpt-abi3-20261021`, base `6881031b8`. Local commits only.
No shipped file or existing Lean module is edited. No ELF rebuild is triggered.
The checkpoint cone remains open; no AcceptedRunJoin is claimed.

## Stage 1 — section checks and fixed-list composition

The prior full TX2 reader composition is not rerun. Six new focused Kani
roots pass: `sections::{raw_sections,wide_section,qm31_section,query_section,
semantic_section,weight_section}`. Every root installs `stub_verified` for
all four field-codec contracts. Those contract bodies are unchanged from
pass 2, whose successful contract receipts are reused. Private reader helpers
are a byte-exact contiguous excerpt of `verifier.rs`, validated by
`tools/oracle-port-ckpt-abi3/generate.py --check`, not an assertion that a
separately linked public `resume` call has been verified. Atomic e/k tests
use local buffers; raw-cursor transport is separately proved in Lean.

`OraclePortCkptAbi3Sections.schedule_exact` identifies the nine named
sections with the full raw-read schedule. `raw_schedule_total` proves exact
immutable bytes and offset 1736 for every panic continuation.
`fixed_composition` composes exact per-section `Except` semantics, including
short-circuit rejection, over precisely that schedule. Its atomic equalities
remain named hypotheses; constructing the Rust semantic states and proving
the emitted caller is this composition remains open. This generic theorem
is not a concrete reader or cone join.

The final section Lean attempt is 2: exit 0, 13.357798 seconds, peak RSS
2,249,392,128 bytes, zero swaps, source revision `6881031b8`. All four
`#print axioms` reports are subsets of `{propext, Classical.choice, Quot.sound}`.
The initial reserved-keyword parse error is retained as failed evidence.
The std inventory's final attempt 3 passes; earlier unknown-name/syntax
inspection attempts are retained, never counted as proofs.

| Kani root | Exit | Wall seconds | Peak RSS KiB |
|---|---:|---:|---:|
| raw | 0 | 190.710588 | 1788420 |
| wide | 0 | 1.598244 | 279260 |
| qm31 | 0 | 1.478513 | 277696 |
| query | 0 | 16.504455 | 520500 |
| semantic | 0 | 4.844890 | 281976 |
| weight | 0 | 64.792781 | 2384828 |

All have zero swaps, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64, optimized verification compilation, and unwind assertions.
Exact commands, source hashes/revision, dependency fingerprint, logs, GNU
time and cgroup peaks are in `host/receipts/*-v1/`; reservations are in
`host/`. `#print axioms` is N/A for Rust gates. Lean commands, dependency
hashes, revision, axiom output and resource metrics are in `manifest.json`.

## Roadmap recorded after stage 1

Symbolic proof/public lengths; C5/extracted kernel identification and Rust
reached-state provenance; std owned-iteration/physical allocation boundary;
TX1/TX2 caller joins and the concrete checkpoint Site from the S10 worker.
Existing pass-2 evidence remains evidence for its recorded source/domain.

## Stage 2 — symbolic proof/public lengths

`proofs::frozen_writer_all_bounded_lengths` passes against the linked frozen
writer, for arbitrary backing bytes and symbolic `proof_len ≤ 57607` and
`public_len ≤ 1880`, including empty slices. Each hash call checks exact
slice pointer **and metadata**, rather than looping over proof/public bytes.
This proves the call receives the entire original borrowed slice of that
symbolic length. Output bytes and checksum-body bytes remain independently
universally indexed. The S2, next=10, 64-weight and canonical-wide-input
restrictions are unchanged; raw QM31 words remain arbitrary.

`proofs::reader_authentication_all_bounded_lengths` passes over the same
lengths, arbitrary checkpoint bytes of length 1768 and arbitrary digest
answers. The byte-exact source authentication prefix checks header and all
three short-circuit digest comparisons, including exact source slice identity
and checksum-body slice identity. Every subsequent source reader statement
is independent of proof/public/hash, as the source excerpt boundary shows.
This is a certificate for the **authentication prefix**, not a rerun or
certificate of full resume/driver composition. The six field-section roots
are unchanged and their successful receipts are reused.

Both final gates use unwind 70 and explicit unwind assertions. Writer:
exit 0, 63.006556 seconds, 2,040,116 KiB peak RSS. Reader prefix: exit 0,
2.917657 seconds, 299,224 KiB peak RSS. Both have zero swaps and the required
6G/8G/zero-swap/64-task caps. Source revision `6e2b4eb8a`; exact source and
command pins are in `host/receipts/lengths-{writer,reader}-v1/`. Rust axiom
reports are N/A. Five inherited pass-2 reservation files accidentally copied
with the initial host snapshot were removed from this packet; actual pass-3
preflight records and every pass-3 attempt remain retained.

## Stage 3 — representation condition and std owned iteration

`OraclePortCkptAbi3Canonical.canonical_word_bytes` proves the word-level
byte projection agrees with its exact-field quotient on canonical words.
`not_all_words_canonicalized` proves an unconditional extension to all U32
words is false: the raw limb P and zero have identical residues but different
LE32 encodings. The proof uses the existing symbolic four-byte decoder law,
not reduction of checkpoint vectors. This is a representation obstruction,
not a counterexample to a correctly restricted accepted-run join. Successful
strict resume can provide canonicality, so deriving it from that path is a
possible next step. All raw QM31 words in the writer certificate must not be
silently interpreted as canonical C5 field values.

Final Canonical attempt 1: exit 0, 14.751043 seconds, peak RSS 3,488,006,144
bytes, zero swaps, revision `6e2b4eb8a`. All three axiom audits are standard.
The full extracted sparse-byte function has **not** been identified with C5.
In particular, word canonicality alone is not the complete four/eight-limb
codec bridge or Prepared/Accumulator representation theorem.

`OraclePortCkptAbi3OwnedIter.owned_contents` proves that length-indexed
iteration using the actual imported std `IntoIteratorVec.into_iter` and
`IteratorIntoIter.next` consumes all Vec contents exactly once, in order,
and leaves an empty iterator. It assumes no step/next specification supplied
by a caller. Final attempt 1: exit 0, 3.495536 seconds, peak RSS 2,255,929,344
bytes, zero swaps, revision `6e2b4eb8a`. Three new standard axiom audits.
This closes owned-iterator **content in that std model**, not adoption of
mutable/shared Rust iteration in the checkpoint helpers.

Physical allocation remains open. The inspected std model represents Vec
as a bounded list, `with_capacity` ignores its argument, and owned IntoIter
is another Vec. Rust `heap::filled` calls `try_reserve_exact` and can return
Allocation; resume separately calls `Box::new`. These physical effects are
absent from the inspected content model. Kani's standard no-malloc-failure
model and a bounded-list theorem must not be promoted to physical allocator
availability, capacity, deallocation or Drop semantics.

## Stage 4 — caller/S10 audit and exact residual

The S10 packet landed on research during this job. Its
`OraclePortS10ModelInventory.lean`, `S10-INVENTORY-20261021.md` and final
attempt-7 receipt were imported byte-for-byte from research. No S10 module
was authored or edited here. The module supplies a five-site **model** tree;
it explicitly excludes checkpoint resume, the outer Rust driver and Pool.
`OraclePortCkptAbi3S10Boundary.no_checkpoint_site` kernel-checks that no Site
with owner `.checkpointAbi`, for any declaration name, is in that inventory.
Final boundary attempt 1: exit 0, 7.280634 seconds, peak RSS 3,629,137,920
bytes, zero swaps, revision `81ee9fcab`, axiom report `[propext]`.
The S10 worker's own standard-axiom receipt is reused, not rerun.

The requested checkpoint-cone accepted-run join is **not discharged**.
`driver-obligations.json` pins the exact tx1/tx2_common source spans and
lists each missing source-to-model statement. In particular:

- Instantiate the semantic section states/equalities and identify the
  complete emitted resume caller with that composition, including ordinary
  errors, field assembly, allocation and Box.
- Prove the complete extracted four/eight-limb codec and sparse-byte layout
  identification with all C5 blocks. The canonical-word lemma is a local
  part, not that theorem.
- Identify actual Rust `prepare`, `Accumulator::new`, `query_loop(0..10)` and
  `pending.finish` with the precise `p,q,i` reached in `dV_frozen` and its
  C3 saved-ten accumulator. Pass 2 supplies the model inputs and uniqueness;
  its arbitrary Context is not Rust context provenance.
- Supply the physical allocation and shared/mutable iteration source/std
  boundary. Owned-iterator content is proved in the imported std model.
- Construct the actual source checkpoint Site/Signature and both caller
  joins, then the raw accepted-log and enriched two-pass join required by
  `OraclePortFrozenOrderJoin.AcceptedRunJoin`. The landed model inventory
  supplies none of that checkpoint source Site. The six authentic checkpoint
  reads cannot simply be erased before an unchanged tail (pass-2 theorem).

These are source/translation/caller obligations, not new cryptographic
assumptions. No generic whole-reader or whole-driver premise was introduced
to stand in for their discharge. Runtime P2/P2-prime snapshot/carrier binding
remains separate. The CONE-AUDIT checkpoint row is updated and remains (d).
No endpoint or headline premise is deleted. No frozen full manifest replay
is launched while the concrete source/driver closure is incomplete.

## Final focused audit

`OraclePortCkptAbi3Freeze`, final attempt 2: exit 0, wall 9.865317 seconds,
peak RSS 3,564,716,032 bytes, zero swaps, source revision `81ee9fcab`.
Seventeen final `#print axioms` lines cover all eleven authored theorems,
the drain definition, the pass-2 extracted byte function and the four landed
S10 model theorems. Every report is a subset of `{propext, Classical.choice,
Quot.sound}`. The earlier successful freeze predates the landed S10 import;
adding that import and its boundary theorem is the source/environment change
justifying the final focused union audit. It is not a full frozen replay.
No shared object was overwritten; all authored objects remain in the private
pass-3 cache and the S10 cached object is a read-only import.

All eight Kani gates pass. Four unchanged codec contract checks are reused
only after `reuse.py` verifies identical specs, helper/contract bodies and
contract roots, and validates their historical source/receipt hashes.
`source-pins.json` checks 197 local/host Rust/Cargo inputs, including builder
writer dependencies, with zero mismatches. `host/toolchain.json` records Kani
0.67.0 and executable hashes/sizes. Each root's historical source hash stays
attached to that root; the audit checks the additive length-root include
rather than relabelling the earlier section checks as a new source run.

Recheck without rebuilding:

```
python3 -B tools/oracle-port-ckpt-abi3/generate.py --check
python3 -B tools/oracle-port-ckpt-abi3/reuse.py
python3 -B tools/oracle-port-ckpt-abi3/audit.py
```

For an explicit read-only remote snapshot comparison, run
`python3 -B tools/oracle-port-ckpt-abi3/source-pins.py`. The S10 dependency
snapshot and exact obligations can be refreshed with `dependencies.py`.
No shipped crate/program, existing Lean module, protected lean-candidate,
wallet/key or ELF changed. ELF rebuilds and runtime/adversarial suites are
therefore not triggered. No local target directory, binary or object is
committed. The target checkpoint-cone join is **not yet established**.
