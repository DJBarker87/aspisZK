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

## Next stages

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
