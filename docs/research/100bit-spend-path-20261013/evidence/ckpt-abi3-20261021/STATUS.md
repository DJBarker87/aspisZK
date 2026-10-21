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
