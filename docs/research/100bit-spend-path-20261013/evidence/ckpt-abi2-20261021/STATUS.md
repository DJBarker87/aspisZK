# Checkpoint ABI continuation

Base ec56a3486, branch codex/cx-ckpt-abi2-20261021. Local commits only.

The current frozen source has not changed since the prior packet. Checkpoint
serialization lives in verifier.rs; candidate::tx1 writes after pending.finish,
and candidate::tx2_common resumes before the second query range. The model
`dV_frozen` contains neither checkpoint operation. Therefore a reference codec
roundtrip alone cannot discharge its surrounding driver identity.

Stages in progress: eliminate the Formatter dependency by proving that the
panic continuation is unreachable; exact per-function codec adoption with
explicit finite bounds; reached-state and driver composition. Every proof
receipt records revision, source and dependencies, command, exit, wall, peak
RSS, swap and complete axioms. Existing Lean and sibling modules are read-only.

## Stage 1 — panic continuation independence

`OraclePortCkptAbi2Unwrap` proves raw-read totality and exact immutable bytes
for every panic continuation, observational independence between any two
panic continuations, and totality of all saved-ten raw reads. This removes
the former unwrap-on-Ok premise for this explicit library model. It does not
assert that a concrete emitted Formatter instance is imported or identified.

Final local attempt 2: exit 0, wall 13.111534 seconds, peak RSS 2,240,479,232
bytes, zero swaps, source revision ec56a3486. All four axiom audits are
standard; the first failed attempt used a nonexistent scalar extensionality
lemma and is retained as failed evidence. No existing Lean module changed.

## Stage 2 — reached model inputs

`OraclePortCkptAbi2Reached.accepted_inputs` extracts the parsed proof, query
function and SourceInputs from acceptance of `dV_frozen`, and derives the
query decode and injectivity from that reached sampler row. The matching
support data are the data read from the actual typedRows. No query uniqueness
premise is supplied externally. `accepted_reference_resume` then proves that
saving and resuming the recurrence from those data and the reached rho always
returns the complete saved-ten model state. Retained semantic Context remains
an explicit parameter; this does not identify Rust preparation or query_loop.

Focused attempt 1: exit 0, wall 22.648015 seconds, peak RSS 3,572,154,368
bytes, zero swaps, revision 118175311; both axiom reports standard.

## Stage 3 — Vec content and non-erasure of checkpoint reads

`OraclePortCkptAbi2Vec.push_exact` / `append_exact` prove total exact content
for the same bounded-list Vec model used in the builder track, under explicit
machine-size bounds. This is value semantics, not a physical allocation or
Drop theorem. `OraclePortCkptAbi2StdInventory` prints the actual imported
model to make that distinction checkable. It introduces no allocator axiom.
Final Vec attempt 2: exit 0, 5.557012 seconds, RSS 2,253,717,504 bytes, zero
swaps. Its first attempt omitted the list-cons length rewrite; retained as
failed evidence. Inventory attempt 5 is the final accepted inspection;
earlier command-syntax probes are retained and never treated as proofs.

`OraclePortCkptAbi2DriverObstruction` proves that authentic write/resume plus
an unchanged tail preserves the tail verdict but adds exactly six ordered
reads. Thus this particular substitution cannot erase checkpoint operations,
even on accepted tails. It is **not** a counterexample to an independently
instantiated full Rust/frozen-model driver identity. Final attempt 2: exit 0,
8.033791 seconds, RSS 3,516,989,440 bytes, zero swaps, standard axioms for
all three theorems. The missing namespace import in attempt 1 is retained.
