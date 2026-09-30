# R95–R98: one-buffer authentication and exact public query entry

2026-09-30; base `da1110c9f49179292d332e1d300f618ba2d8f5d4`.
Research only. Neither under-1M execution nor full security is achieved.

| Complete verifier | World 0 CU | World 1 CU | Decision |
|---|---:|---:|---|
| Pushed R93 control | 1,130,010 | 1,128,272 | Retained |
| R95 one-buffer Merkle walk | 1,125,130 | 1,123,392 | Compose |
| R96 seven-product square | 1,125,978 | 1,124,239 | Reject regression |
| R97 opt-level 2 | — | — | Reject stack failure |
| R98 explicit query guard | **1,125,129** | **1,123,391** | Selected research endpoint |

These are complete executions on the same two R84 proofs. Both actual 1M
honest runs still exhaust; **125,129 CU remains** on the larger fixture.
Corrupted combined finals reject with Custom(6), without resource failure, at
both caps. Heap stays 262,144 bytes and simulated accounts are unchanged.
No proof bytes, security parameters or validation checks change. The single-CU
R98 difference is incidental, not an optimization claim.

## Native changes and rejected experiments

R95 reads each Merkle frontier in increasing order and writes its parents below
the unread children in the same buffer, then truncates. Every range, ordering,
shape, root and exact-consumption check remains. C1/C2 inputs and the complete
ordered, segmented hash-call history are unchanged, including for a stateful
hash backend. The existing core two-buffer implementation remains the host
reference. The private helper returns only a boolean; no public scratch-array
postcondition is silently changed.

Its independent checker passes **594 honest schedules / 8,230 total cases**,
including malformed frontiers, duplicate/reordered/out-of-range entries,
corruptions, empty inputs and depth boundaries. Both actual host proof audits,
3,282 wire cases (3,281 checked rejections), SBF stack/table gates and complete
runtime pass. Savings are **4,880 CU per fixture**.

R96 replaces canonical squaring with a seven-integer-product identity using
explicit bounded arithmetic. It passes 262,144 squares, 256 boundary cases,
independent i128 field arithmetic and u128 intermediate-range checks, plus the
source and runtime gates. It is 848 / 847 CU slower than R95 and is not composed.
No proof effort is spent promoting this rejected kernel.

R97 revisits opt-level 2 after the source and recorder-frame changes. It still
produces 4,352- and 4,416-byte frames plus semantic call-frame overwrite
diagnostics. The compiler's zero exit does not override the stack gate: the
runner rejects the ELF and does not simulate it. Unchanged host results are
reused by exact pins, not replayed. Fat LTO, one codegen unit and overflow
checks remain enabled.

The selected ELF SHA-256 is
`47d9f5f2b7fd2d800b6be8df54cd6d9db4d3da08f1b518406a0aef8167301b30`.

## Exact selected query entry

R98 replaces `!bound.is_power_of_two()` with the equivalent short-circuit guard
`bound == 0 || (bound & (bound - 1)) != 0`. The zero case prevents underflow.
This removes the unsupported ctpop operation from the actual-source extraction;
it introduces no primitive axiom or synthetic loop. The checker compares the
retained source over **1,000,096 guard cases and 7,128 public calls**, including
SHA, zero and stateful hash backends, invalid bounds, draw limits, duplicates,
zero count, errors, final transcript state and complete ordered hash calls.
The original transcript KAT remains pinned. An initial checker import failure
is retained, followed by the corrected passing build.

Pinned Charon/Aeneas extraction of the actual selected source passes. Existing
types and inner/outer loops are token-identical after namespace normalization;
only the exact generated guard/public-entry suffix is new. Nothing is replaced
with a model loop. Charon takes 12.88 s / 609,716 KiB peak RSS; Aeneas takes
0.72 s / 91,548 KiB; both exit zero with zero swaps.

| Final focused Lean target | Exit | Wall | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| `AspisV8R19/QueryEntrySource` | 0 | 1.40 s | 2,526,676 | 0 |
| `AspisV8R19/QueryEntryExecution` | 0 | 2.96 s | 3,699,008 | 0 |

Lean 4.32.0 reuses 362 cached predecessors, with 310 transitive source/runtime
pins. Focused failures and their fixes precede one final changed-leaves replay.
The four audits cover `selected_entry`, `public_result`, `decode_finish` and
`public_value_state`. All use only the standard propext/choice/quotient axioms;
three additionally inherit the existing opaque `core.fmt.Formatter` type.
There are no new axioms, admissions, ctpop assumptions or final warnings.

The proved statement is the selected public sampler's guard, typed result and
final transcript state for an arbitrary total deterministic hash function.
It is **not yet** its complete observed shared-oracle history or probabilistic
law. The next sampler step is that exact observer and memoized-oracle bridge.

## Evidence and security boundary

`python3 docs/research/v8-full-view-zk-20260912/tools/check_r98_evidence.py`
audits the parent evidence, source deltas, runtime, malformed controls, stack
failures, extraction, focused Lean metrics and axioms, and the 159-artifact
manifest. Raw registers, ELFs, proof fixtures and keys are not collected.
NUC cgroups use host/Lean 5/7 GiB, SBF 12/16 GiB, runtime 2/3 GiB and collection
1/2 GiB, always with MemorySwapMax=0. All retained process swap counts are zero.
The Solana skill's malformed-input, source, stack and full-runtime checks remain
selection gates, not substitutes for cryptographic proofs.

The first profile proposition remains universal actual-source C1/H1/G joint
affine-image compatibility for R84, including p0/p2, all legal same-public
witness differences, adaptive/degenerate prefixes and justified exception
losses. Finite rank certificates do not prove it. Causal posterior simulation,
seed/C2 commitment composition, visible retry/publication and full privacy
remain open. Soundness separately needs coherent pre-beta quotient-pair
extraction and actual shared-oracle/loss accounting. All negative regressions
remain. R84 is not security-promoted; no deployment or wallet operation.
