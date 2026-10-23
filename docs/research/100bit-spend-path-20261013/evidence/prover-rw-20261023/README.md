# Prover rewrite gate packet

Adoption candidate on `codex/cx-prover-rw-20261023`; baseline `084f714ccd`.
Stage 1 design is committed as `eb362eae2b` in `design/PROVER-RW-20261023.md`.
No push, merge, protocol change, trust extension or key cleanup is performed.

## Implementation frontier

The intermediate source rewrites the retry owner to a counted loop and splits
opening/publication into `PreparedOpening` and `Publication` owned results:
`prepare_opening`, `finish_opening`, `publish_compact`. The per-loop helpers
`round`, `fold`, `encoded_slice`, `folded_leaves`, `publication_indices` use
counted loops. Ordered gamma batching, inactive accumulation, primal/dual folds,
opening bytes and batch/tree slot order are retained. Query sorting/dedup is
explicit insertion on at most 22 public indices. Folded encoding still precedes
folded salt derivation, preserving the original returned-error order.

This is **not the complete pipeline rewrite**. Mask derivation/application,
semantic builder/sumcheck, C1/C2 commitment ownership/trees, query scanner and
selected entropy caller remain their previous implementations. Arithmetic,
hash, blocked P_R1 internals and fixed-range parallel evaluations are unchanged.
No claim of Aeneas acceptance, new leaf contracts, L1 equality or real refinement
is made from the source shape or fixture tests.

## Gate method

`prover_rw_gate` uses deterministic insecure test coins with domain-separated
public nonce, field entropy and leaf seed, through the real
`prove_masked_retrying_with` and durable ledger. Coins 0–4 are used on both
transfer and withdrawal. The timer includes the complete retrying prover call
and P_R1, with the fixed v2 16-worker setting. Strict tx1/tx2 verification runs
outside the timed call. Ledgers, generated proofs and binaries stay on the build
host; there are no account keys or funded accounts created by the gate.

Baseline and candidate are separate optimized binaries in a private workspace:
`/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/`.
Source caches are copied from the existing v2 workspace, not modified in place.
Native commands run under 6G/8G/no-swap/64-task scopes, Cargo -j4. Runtime scopes
run sequentially with no build from this task competing. A pre-existing peer Z3
job is active: timings are shared-host measurements and do not identify a causal
rewrite slowdown. No job belonging to another worker is stopped.

`compare.py` compares actual complete proof/public bytes on the host, plus
returned status, audit, attempt/callback counts, then calculates five-sample
medians and applies both <15 s and <=110% baseline criteria. Hashes are exported
only after the full-byte comparison. Ten paired successful attempts do not
satisfy the required 1,000-run corpus or rejected-attempt coverage.

`source-scope.json` is an assessment of host-only source edits and inherited
full verifier pins, **not** a fresh SBF rebuild/byte identity receipt. Native
receipt source revisions name the pre-implementation design commit; complete
per-file hashes identify the tested dirty source. The later implementation
commit records those exact source bytes. A redundant copy of the harness at
`src/crates/aspis-r1-cost-probe/prover_rw_gate.rs` appears in candidate hash
inventories; Cargo does not compile it (the example is under `examples/`).

## Formal status

No Lean compile, Kani run or Aeneas extraction has been launched. Compile budget:
0/100 Lean, 0/60 Kani. No assumptions discharged, added or changed. Conjunct 1 of
`RustProverRefinement`, the D166 joint trace transport, L1/L2 source event image,
expanded thread/runtime model and L3 remain open. Prior model/helper results are
eligible for reuse only after source/domain checks, not attributed to this rewrite.

Timing results and the stop/continue decision are recorded in
`opening-comparison.json` once the paired measurements finish.

## Performance stop and handoff

`compare.py` exited **3** for the requested absolute timing stop. The completed
five-sample results (16 workers; seconds) are:

| Fixture | Current v2 baseline median | Intermediate rewrite median | Change |
|---|---:|---:|---:|
| Transfer | 15.205470563 | 16.415735081 | +7.96% |
| Withdrawal | 15.678505408 | 17.112834344 | +9.15% |

Both relative <=10% gates pass; both strict <15 s gates fail. Baseline itself
also exceeds 15 s in this shared-host run. This is not evidence that the source
change caused the timing difference. No unchanged remeasurement is performed,
no threshold is relaxed, and no further implementation/proof campaign starts.
The intermediate source and failed gate remain reviewable on this branch.

All ten full-byte paired comparisons pass (five varied coin tapes on each of
two fixtures), with identical Ok status, full audit, attempt and callback counts.
Every proof passes strict tx1/tx2. Every run succeeds on attempt one: rejected
attempt coverage and the required 1,000 full differential runs are **not done**.
The frozen three-ELF rebuild/byte comparison, L1 record gate, leaf-contract audit,
Aeneas extraction and Stage 3 theorem are **not done**. The partial Stage 2 commit
must not be read as a completed rewrite or as adoption authorization.

The four capped native scopes all exit 0, with zero swaps:

| Target | Wall seconds | GNU time peak RSS KiB |
|---|---:|---:|
| Baseline optimized harness build | 31.816 | 563596 |
| Baseline ten proof runs | 154.236 | 706000 |
| Owned opening optimized build | 5.500 | 312276 |
| Owned opening ten proof runs | 168.394 | 698016 |

Exact targets, compiler/CPU/flags, complete source pins, cgroup peaks, limits,
stdout/stderr and GNU time logs are under `receipts/`; admission snapshots are
under `reservations/`. `tested-source-audit.json` compares all 619 baseline and
620 candidate pinned files with their intended source, including explicit
harness-only additions. Candidate build/timing source inventories are identical;
the three changed compile inputs still match the committed working source.
Rust/#print axioms: N/A. Lean budget used 0/100; Kani budget used 0/60.
No prior formal gate is promoted to this source revision.

**Target not yet established.** Next deliverable is lead review of the failed
performance gate and a justified source/environment change before another timing
attempt. After that, complete the owned mask/semantic/commitment/entropy phases,
all remaining Stage 2 gates, then extracted real-attempt/model correspondence and
the retry/observable/experiment composition for conjunct 1. There is no new
security premise, failure-event enlargement or contract change in this packet.

## Continuation after lead performance review

The lead superseded the implementation absolute stop: use the interleaved
same-session <=110% relative gate during implementation, and reserve the
single <15 s measurement for a quiet host with load and other capped jobs
recorded. The original stop and its receipts above remain historical evidence.
This does not authorize adoption or relax any equivalence/security obligation.

The continued source changes counted mask sampling/application and D expansion,
semantic guards/claims/transcript assembly, sumcheck accumulation, commitments,
encoding geometry, host-only binary trees and query scanning. The C1/C2 interface
no longer constructs arrays of column loans. Geometry/tree levels use structural
recursion. Opening/publication own their commitments and use small byte-assembly
helpers. Fixed arithmetic, hashing, P_R1 and parallel numerical kernels retain
their v2 implementations. Worker-internal TLS remains inside the unchanged
parallel boundary; there is no claim that the complete runtime is TLS-free.

One intermediate interleaved session measured candidate/v2 ratios 0.970814
(transfer) and 1.005147 (withdrawal), five samples each, configured 16 workers.
All ten proof/public byte comparisons and returned fields passed. Later ownership
fixes still require their final paired gate; these numbers are not attributed to
untested later source. An earlier diagnostic session briefly overlapped this
worker's extraction probe; that probe was stopped and its timing pair is not
release timing evidence.

Allocator instrumentation on the intermediate full pipeline measured about
262,000 fewer allocations and 34.5 MB fewer cumulative requested bytes per proof
than v2, with complete proof/public byte equality. These are diagnostic counts,
not peak memory or timing evidence; later helper splits are separately pinned.
The three verifiers were actually rebuilt and compared directly with retained
ELF files: all bytes equal at the required d7d42f77…, 2b2a9f0e… and 121f3e29… pins.
Host-only later edits do not change that compiled verifier dependency closure.

The first ten-pair differential smoke passed full returned records and supplied
HashFn input/output streams, including exhaustion, duplicate reservations, entropy
failure and a rejected prefix followed by a real successful proof. This is seven
successful proof pairs plus three error pairs, not the required 1,000-run gate.
The expanded harness varies honest amounts/salts and both statement variants,
programs a stateless first-attempt mask-expander rejection, and exercises actual
filesystem permission failure. Linux inotify observes actual ordered ledger
create/close events between entropy callbacks; final ledger bytes and actual
public worker records are compared too. A native candidate preflight passed these
paths on both variants. Its paired corpus and current-source timing are pending.
The supplied HashFn stream observer does not claim to intercept immutable ledger
or runtime-internal hashing; whole-experiment oracle transport remains formal work.

Charon accepts the expanded actual generic per-attempt cone. Aeneas accepts the
small round and folded-leaf probes; full-cone preflights have exposed and guided
successive ownership fixes. A full accepted extraction and model theorem are not
yet claimed. The immutable CT/pole receipt audit reuses 24 passing receipts with
matching selected body hashes; the complete external-call contract inventory is
still open. No new Kani run or Lean compile has been performed (0/60 and 0/100).
The common rules require assigned env J attempt numbers; a range was requested.

**Stage 2 and Stage 3 remain incomplete. Target not yet established.** Next:
finish direct extraction preflight, freeze the tested source, execute the paired
1,000-run corpus and final interleaved relative gate, complete the leaf contract
inventory, then prove the per-attempt/model components using the assigned Lean
range. The real RunJoin, ordered oracle/observer transport and L1/L2 coupling
remain obligations; output equality alone is not asserted to discharge conjunct 1.

### Additional local contracts and source boundary

Seven new Kani invocations have run: four passed, two timed out at 120 s,
and one was rejected before compilation because the CBMC argument flag needed
`-Z unstable-options`. The bounded compact-value comparison covers arbitrary
32-byte input plus retained output on error (557 properties). The row-14 record
comparison covers arbitrary 32-byte payloads, including noncanonical encodings
(942 properties). The parametric private-leaf (128/480-byte value) and binary
parent contracts check the exact digest slice grammar, single invocation and
arbitrary returned answer. They do not prove SHA-256 semantics or full-sequence
codec correctness. Failed broad harness sources are retained under
`tools/prover-rw-20261023/contracts/timeout-*.rs.txt`. The row-tag/length symbolic
record query reached 6,707,290,112 bytes cgroup peak before its timeout; it was
replaced with the fixed-row obligation, without a cap increase.

The selected semantic record owner and compact publication encoder are now
host-only counted implementations. Shared verifier files remain unchanged. The
external inventory distinguishes constant initializer opacity from function
opacity; neither is counted as a discharged contract merely because translation
can name it. The true conjunct-1 endpoint is the `RunJoin` statement in
`ProverCommitDeployedFuel22.lean:121`, not literal output equality alone.

Historical extraction receipts before the next source checkpoint retain the
old design revision label `eb362eae2b`; their actual dirty source is identified
by the complete per-file SHA map and retained immutable LLBC inputs (which
include source contents). That label must not be read as a clean-source release
claim. Later checkpoint receipts will use the actual committed revision.

The subsequent `phase-paired-002` predecessor binary passed all twelve paired
records, full public/proof bytes and supplied-oracle logs, including both
variants, rejected-prefix success and real permission failure (143.27 s wall,
703032 KiB peak RSS, zero swaps). This overlapped a compilation and is functional
evidence only. The current source has compiled via `extract-attempt-023`; full
Aeneas translation remains stopped in `sample_source_d`. This checkpoint is
partial Stage 2, with the 1,000-run and final timing gates still pending.
