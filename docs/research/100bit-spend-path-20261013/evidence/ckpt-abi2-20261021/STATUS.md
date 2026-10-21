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

## Stage 4 — linked writer and field-codec P6 checks

At revision 78d23d694, all five final focused Kani gates pass, with explicit
unwinds and unwind assertions. The tool's standard no-malloc-failure model
is part of this P6 boundary; it is not an allocator-availability theorem.
`source-pins.json` verifies 184 local/host source inputs with zero mismatches.
The standalone crate calls the actual shipped checkpoint function; no frozen
body is copied into the writer proof. The hash protocol checks its three
calls and compares an arbitrary checksum-body byte, and the result comparison
uses an independently arbitrary output byte. Domain: S2, next=10, 64 weights,
canonical wide inputs, arbitrary other stored fields, proof length 3 and
public length 5. The lengths are an explicit unclosed generalization.

| Final gate | Exit | Wall seconds | GNU time peak RSS KiB | Cgroup peak bytes |
|---|---:|---:|---:|---:|
| decode-k | 0 | 2.077659 | 274664 | 183173120 |
| decode-e | 0 | 0.862832 | 160124 | 60751872 |
| encode-k | 0 | 16.383739 | 3893988 | 4885409792 |
| encode-e-byte | 0 | 3.643164 | 287184 | 194007040 |
| writer | 0 | 70.143351 | 2036572 | 2808582144 |

Every final gate has zero swaps and limits MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64. Rust/translation receipts record `#print axioms`
as N/A. Full exact commands, source fingerprints, stdout/stderr and time
reports are in `host/receipts/final-*`. Historical failed CLI, missing input,
trait/Arbitrary, unwind and extraction attempts are retained.

The first wide encoder's iterator/pointer formula stalled; its replacement
checks one byte, and an 8-bit object-ID encoding makes that exact symbolic
check finish in seconds. No cap was increased. The new sparse reference
avoids building a second 1736-byte vector. Pinned extraction succeeds after
replacing unsupported iterator/borrow patterns by explicit scalar byte
selection and fixed LE limb reads. `extraction-normalization.json` records
removal of generator heartbeat/recursion overrides; no limits are raised.

## Complete-cone boundary

The requested checkpoint-cone accepted-run join is **not discharged**.
The broad reader roots timed out in capped scopes, including the verified
field-decoder version; they remain diagnostic. Field contracts and a writer
check are not relabelled a full reader theorem. The extracted sparse byte
reference is not yet identified in Lean with the physical C5 codec.
Rust Prepared/query_loop/pending.finish state provenance, actual Vec/heap and
owned-iterator behavior, arbitrary proof/public lengths, and both surrounding
entry/driver identities remain open. Model provenance and bounded-list Vec
content do not discharge those source statements.

The six-read non-erasure theorem stops the specific proposal to discard the
checkpoint stage in an ordered-log join. It does not refute a separate full
caller identity. No `ConeJoin .checkpointAbi`, `AcceptedRunJoin`, new endpoint,
or premise deletion is claimed. The cone row remains (d). No full frozen
release replay is run while its concrete source/driver join is incomplete.
No existing Lean module, sibling cone, protected candidate, shipped crate,
wallet/key or ELF changed. The ELF rebuild condition is therefore inapplicable.
