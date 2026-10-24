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

### Later continuation checkpoint

The all-class native preflight (`all-classes-paired-001`) passes twenty paired
whole retry-owner executions, both variants in every tape class, including
twelve full successful proof pairs and two forced rejected-prefix successes.
Full records, L1 event order and public/proof bytes are equal; oracle logging
was off for this run. Wall 420.81 s, peak RSS 710092 KiB, zero swaps. Its
immutable `corpus-candidate-009` predates the latest ownership refinements.

The final verifier dependency assessment triggered a fresh rebuild after the
additional gated module declarations in lib.rs. `proverw002` default/devnet/Pool
rebuilds exit 0, then literal byte comparisons against retained S2E files pass
at all three required full pins. No binary or key file is committed. All
generated SBF keypairs remain retained on the host with mode 600.

Three exact single-cell volatile-write Kani frame contracts now pass for salt
bytes, M31 and QM31, including arbitrary raw bits and an unchanged two-cell
frame. These bodies are retained verbatim with SHA bindings in the contract
kit. Ten new invocations total: seven passing harnesses, two timeouts and one
CLI preflight rejection. The full leaf inventory remains open; these local
contracts are not a whole-destructor, whole-pipeline or privacy theorem.

Aeneas has progressed through semantic/sumcheck owners, opening batching,
folding, opening transcript and compact publication. Fixed three-point,
eight-pair and six-slot operations use explicit calls; small bounded owned
collections use structural recursion. The query scan still consumes the same
precomputed eight pairs, including unused suffixes. Current source fixes remain
subject to the frozen 1,000-run and final interleaved gates. No Lean theorem
has been checked; an assigned env J range is still required.

### Owned phase checkpoint after extraction preflights

The mask-column and balance owners, semantic oracle, sumcheck round owner,
D-tail recurrence, commitment lanes, query scanner, and opening assembly have
been refactored. This checkpoint is partial Stage 2, not adoption evidence.
Charon attempt 051 compiles/extracts the current source; Aeneas translation
remains a diagnostic until the complete cone succeeds and Lean checks it.
The last full comparisons apply to their individually pinned predecessor
binaries. A fresh final relative timing session and 1000-case corpus are pending.
Two additional direct shipped CT field codec checks pass, taking this task to
13 Kani invocations (9 pass, 3 timeout, 1 CLI rejection). The complete external
contract inventory and per-attempt/model theorem remain open.

### Frozen implementation checkpoint `532c5e48ec`

Production source is pinned for the new native gates. `corpus-candidate-011`
and `pipeline-002` build successfully in optimized mode, each under the original
6G/8G/no-swap/64-task limits. Their binary hashes and complete source maps are
retained in the corresponding receipts; the revision marker includes only the
subsequent gate orchestration change. No source change is made while the final
relative session and corpus use these immutable binaries.

Charon `extract-attempt-051` exits 0 (108.776 s, 539180 KiB RSS, zero swap).
Aeneas `aeneas-attempt-048` fails in the single-loop
`Commitment::fill_opening`, source lines 196–204, with a context-join error
(`InterpJoin.ml:2209`). Earlier query-scan and commitment-construction diagnostics
are retained. No generated whole-attempt Lean program is accepted or compiled;
no opaque external template is installed as an axiom. The 103-function external
inventory is an obligation list, not a contract certificate.

The current codec Kani checks invoke shipped CT field functions directly:
`exact_full_width_codec` proves canonical eight-limb byte order and decoding
(2.532 s, 300096 KiB RSS); `raw_qm31_embedding_codec` proves arbitrary raw
four-limb normalization, subfield image and decoding (2.623 s, 304900 KiB RSS).
Both exit 0, zero swap. These extend the local leaf evidence without asserting
whole-prover equivalence or complete leaf coverage.

The 120-second `dtail-kani-001` timeout is retained. Its cgroup peak is
1236897792 bytes, with no memory events or swap. It has no proof verdict and
is not retried unchanged or with a higher cap. The remaining formal deliverable
is an accepted extraction of the actual attempt/caller plus a source-to-model
proof that preserves all errors, effects, ordered oracle events and L1 records.
The retained R1 outer-owner theorem still has its explicit PrefixContract and
BodyContract premises. It does not instantiate the new body, RunJoin, fixed bad
event/seed-query transport or L1/L2 joint law. Conjunct 1 remains open.

`interleaved-pipeline-002` passes the relative implementation gate: transfer
median v2 16.182755431 s, candidate 16.238331921 s (ratio 1.0034343033);
withdrawal v2 15.989252766 s, candidate 16.097186048 s (ratio 1.0067503644).
Five alternating pairs per fixture, 16 workers, all compared return fields and
full proof/public bytes equal. Host contention is recorded; these numbers do
not judge the final absolute gate. `corpus-1000-001` is now running its required
1000 full retry-owner paired cases on the same frozen production source.

### Interrupted predecessor corpus and opening ownership probe

`corpus-1000-001` was deliberately interrupted with SIGINT to its own Python
driver after 70 matching pairs: 38 complete proof pairs and 8 rejected-prefix
pairs. Exit 130, wall 897.240 s, GNU-time peak RSS 606544 KiB, cgroup peak
1222713344 bytes, pids peak 35, zero swap and memory-pressure events. This is
partial supporting evidence, not the 1000-run gate. Its ledgers and outputs
remain retained. The reason is a necessary production source change to resolve
the known opening-owner extraction failure; no unchanged replay is planned.

The minimal opening ownership probe now translates with Charon and Aeneas
(`opening-owner-probe-004`, `opening-owner-aeneas-004`). It separates recursive
owned value assembly from an owned enum-to-path selector. This is a shape
diagnostic with a minimal commitment frame and actual field/opening types,
not a proof about the complete production commitment. Its replacement is now
being checked in the actual complete attempt cone before another source freeze.
Two retained R2 framing gates are additionally reused only after verbatim body,
constant and archived-harness/input-hash checks; see reused-r2-contracts.json.

### Decoder contract correction

The first arbitrary-input decoder harness incorrectly asserted that a short
QM31 slice returns None. Kani `field-codec-kani-arbitrary_field_decoders`
finds a reachable slice-index panic (exit 1). The rejected harness is retained
verbatim at tools/prover-rw-20261023/contracts/rejected/field_codec_contracts-v1.rs.txt.
QM31::from_le_bytes requires at least 16 bytes; the selected host-wire caller
checks its row length and passes a 16-byte cell. No shared decoder source changes.
The concrete witness [0;15] panics, while WideExact decoding [0;31] returns
None; `decoder-short-witness-001` checks this in optimized Rust (exit 0, 8.045 s,
581536 KiB RSS, zero swap).

The corrected full-length arbitrary-byte contract
`field-codec-kani-arbitrary_field_decoders_len16` passes: full-width and QM31
decoding succeeds exactly for canonical little-endian limbs, preserves all
limbs, and WideExact rejects wrong length. Exit 0, 1.905 s, 289884 KiB RSS,
zero swap. Budget used: 15 Kani invocations, 10 pass, 3 timeout, 1 CLI rejection,
1 rejected short-input contract. No caller-length invariant is silently assumed
as a proof of the complete pipeline; that binding remains an explicit obligation.

### Further checked local kernel boundaries

`inverse-chain-kani-001` passes the actual fixed inversion chain's 38 ordered
multiplication calls against the retained field source, for canonical nonzero
inputs and arbitrary canonical multiplication answers (3.817 s, 199812 KiB RSS).
`generic-inverse-kani-001` checks the separate CodeField M31 zero guard and its
61-call generic exponentiation route (5.119 s, 201620 KiB). These are parametric
source/control contracts over retained, checked CT multiplication; they do not
alone assert a new inverse-field-value theorem. The model-side fixed-chain facts
in ProverCommitInverse48 remain eligible for an explicit typed binding.

`hash-fn-kani-001` checks the complete private_leaf_hash/LegacyHashFn route, one
call with exact three-slice framing/identity and an arbitrary answer (1.619 s,
301548 KiB). It adds no SHA-256 or freshness assertion.

Both symbolic-exponent encodings timed out at 90 seconds (power-chain-kani-001,
public exponent below 1024; power-chain-kani-002, the selected 0..27 range).
Their original sources are retained in contracts/rejected. No cap/timeout was
raised. power-chain-kani-003 instead enumerates the tiny public domain 0..27
while keeping the canonical base and all arithmetic answers symbolic. It passes
all ordered multiply/square calls and results in 58.600 s, 966952 KiB RSS, no
swap. This covers the selected weights caller's j % 28 exponent range, not
arbitrary public exponents or an unconditional power-value theorem.

representation-kani-raw_base_embeddings and
representation-kani-canonical_scalar_equalities pass the actual F/C/K/E
embedding/representation boundaries (0.745/1.247 s, 186372/199088 KiB RSS).
scalar-adapter-kani-001 passes all twelve actual F/K/E CodeField arithmetic
forwarders with exact operands, one delegated call and returned value, over
already checked CT scalar contracts (4.549 s, 214248 KiB RSS). All exit 0 with
zero swaps. The full external-call/domain audit remains open; these checks are
not a per-attempt/model certificate. Budget: 24 Kani invocations, 17 passes,
5 timeouts, 1 CLI rejection, 1 rejected short-input contract; Lean 0/100.

### Actual per-attempt extraction accepted

Charon extract-attempt-067 and Aeneas aeneas-attempt-064 accept the complete
actual prove_masked_with_attempt control cone, through compact publication.
Aeneas exits 0 in 15.611 s, peak RSS 601472 KiB, zero swaps. Its retained immutable
LLBC input has 19 embedded source bindings and all match the source map at
launch. Funs.lean and Types.lean are emitted on the host; external templates
remain unbound and no generated whole-program module has been Lean-compiled.
This establishes extractability only, not source/model output equality, the
complete leaf-contract gate, a RunJoin, or an adoption result. The selected
proof-account caller/retry root is now being extracted separately.

The added raw-writer gate passes: all raw QM31 limbs, exact 16-byte output,
unchanged adjacent bytes, and decoding iff every limb is canonical
(raw-writer-kani-001: 2.542 s, 311396 KiB RSS, zero swap).
The direct factory preflight initially lacks a pre-existing Kani-only reference
directory and fails compilation; the unchanged tools/r1-builder-reference
sources are copied into the host workspace and included in receipt hashing.
The direct factory success/nonzero test then times out at 90 seconds. Its
replacement checks the small 32-byte nonzero primitive and equivalent word
model first (factory-kani-v3-zero32_kernel_contract: exit 0, 4.489 s, 496732 KiB).
The factory-level test still times out at 90 seconds after that composition.
These control-loop timeouts are retained and not promoted to kernel results.
The remaining zero-seed-exhaustion and OS-error factory harnesses have not run.
No entropy marginal law, factory-wide state theorem, or full caller certificate
is claimed from these checks. Formal control belongs to the extracted owner.

### Caller integration follow-up

The first full proof-account caller translation stops at the retry callback loop.
The replacement transfers the callback by value through at most eight recursive
steps, preserving S2 admission, callback indices, first-success publication,
Rejected-only retry and other-error propagation. The next translation reaches
the actual durable reservation path. Its formatter loop also fails the Aeneas
loop join; a direct hexadecimal loop fails at the same join. The current
replacement owns the filename through 32 recursive byte steps. It preserves
the 69-byte lowercase SHA-256 hexadecimal filename with .burn suffix and the
same reservation hash and filesystem operations. Failed translations are
retained as aeneas-caller-001 through -003, with corresponding source pins.

The accepted per-attempt translation has 161 unbound type/function template
holes, enumerated in continuation/translation-attempt-064-audit.json. None
has been installed as an axiom. Translation acceptance is not Lean checking
or a proof of the per-attempt/model equality. Kani usage is 29/60 invocations:
19 passes, seven timeouts, one CLI rejection, one rejected short-input
contract and one compilation failure. Lean usage remains 0/100.

### Complete caller translation accepted

extract-caller-005 exits 0 (113.734 s, 540160 KiB RSS);
aeneas-caller-005 exits 0 (20.669 s, 667048 KiB RSS), both zero swap.
The actual selected proof-account caller now translates through the 64-byte
factory, durable reservation, recursive retry owner and all per-attempt
control. continuation/translation-caller-005-audit.json pins emitted files
and enumerates 287 unbound template holes. This is translation acceptance,
not a Lean theorem or the source/model equality. Local production source
pins were compared against the accepted translation receipt. The source is
being frozen for pipeline-003 relative timing and corpus-1000-002.

### Frozen source relative gate

Production source checkpoint: 9c131667ca00f4daae78da6299b09a9fe0d00da9.
Both optimized final harness builds pass. pipeline-003 performs five
interleaved v2/candidate runs per fixture, 16 workers per process. Transfer
medians: v2 17.196330087 s, candidate 17.349946833 s (ratio 1.0089331122).
Withdrawal: v2 18.316932724 s, candidate 17.042244310 s (ratio 0.9304092867).
Both satisfy the lead's relative 1.10 gate. Full returned fields and proof/public
bytes match. Scope wall 350.007 s, peak RSS 688980 KiB, zero swap. Load samples
and all ten paired timings are in interleaved-pipeline-003.json. No absolute
under-15 conclusion is drawn from these contended-host values.

corpus-1000-002 starts only after that relative pass. It uses the complete
retry owner, varied genuine transfer/withdrawal statements and ten tape/error
classes, including rejected prefixes. All cases compare status, audit, proof,
public bytes, actual L1 records/events and public worker events; four selected
pairs also compare complete supplied-oracle streams. Its progress is partial
until completed_pairs=1000 and complete=true. Production source remains frozen
while independent contract and diagnostic allocation jobs run under separate
original resource caps. The generic tower inverse contract is Kani invocation
30/60; its result is pending.

### Final allocation counts and inverse adapter contract

The frozen source allocation profile runs once; the unchanged v2 profile
is reused rather than replayed. Transfer: 262147 fewer allocations, 62 fewer
reallocations and 34537821 fewer cumulative requested bytes. Withdrawal:
262161 / 62 / 34546109 fewer respectively. Returned status/callbacks/audit
and complete proof/public bytes match. This is allocation instrumentation,
not a timing or peak-memory measurement (scope 56.222 s, 687084 KiB RSS,
zero swaps). See allocations-candidate-002-comparison.json.

The first generic inverse-adapter encoding fails compilation at Rust's
stub-attribute macro recursion limit. Reducing attribute expansion compiles,
but the combined 61-product lower chain times out at 120 seconds. The next
encoding composes the already checked canonical M31 generic inverse contract;
its first form still exceeds the macro limit, so unused stub attributes are
removed without changing the contract or raising limits. tower-inverse-kani-004
passes (exit 0, 48.979 s, 953464 KiB RSS, zero swaps). It compares actual
CodeField C/Q/E inverse control, lower operation operands, order, errors and
outputs against the retained generic scalar algorithm. Lower arithmetic and
base inverse are supplied by their previously checked canonical contracts;
answers remain arbitrary canonical values. This is not a new unconditional
inverse field-law theorem. The rejected encodings and all failures are retained.
Usage: 33/60 Kani invocations, 20 passes, eight timeouts, three compilation
failures, one CLI rejection and one rejected short-input contract. Lean 0/100.

The ordinary leaf HashFn path also passes plain-hash-fn-kani-001: arbitrary
tag, arbitrary 480-byte backing array and arbitrary length 0..480, exact
one-call two-slice frame and arbitrary returned answer (exit 0, 2.739 s,
317888 KiB RSS, zero swap). This covers the actual plain leaf entry point,
including its LegacyHashFn delegation; it adds no SHA-256 or privacy claim.
The complete caller inventory contains 104 opaque project functions and
28 constant initializers. It is recorded separately from all 287 external
template holes, which also include types and standard/environment operations.
The complete leaf-contract gate remains open. budget-audit.json derives the
actual 34/60 invocation count from immutable receipts: 21 pass, eight timeout,
three compile failures, one CLI rejection and one rejected draft contract.

### Domain checks and sampler reuse audit

The C/Q/E inverse adapter also passes with every lower-operation input
explicitly checked canonical (tower-inverse-kani-005: 101.551 s, 2970148 KiB,
no swap). Adding those domain assertions to the combined cached multiplier
replay times out at 90 s; the existing complete trace equality is retained,
and the separate actual-code canonical-domain check passes
(prepared-domain-kani-001: 50.934 s, 1847132 KiB, no swap). Its constructor
and multiply use independent arbitrary canonical lower-answer tapes. These
are separate local facts, not a compiled composition theorem.

Actual S2 row/tag/from-tag and checked index/reversal/child-parent interfaces
pass two focused Kani harnesses (1.271/1.770 s, 210960/209460 KiB, no swap).
No full coefficient-copy or circle geometry conclusion is inferred.

One native long-division word-step bit-blast times out at 120 s. The small
Mersenne arithmetic fact instead passes in 1.494 s, 202132 KiB, no swap: a
bounded quotient and remainder reconstruct the dividend using shifts and
subtraction. This alone is not native division equality or a sampler law.
The failed exact-step harness is retained.

The dependency audit then locates existing complete division-pass and total
QM31 sampler proofs. All eight archived Rust declaration cuts still occur
verbatim; the entire sampler.rs hash is unchanged. Four checked Lean modules
have matching proof-source hashes, exit-0 receipts and standard-axiom audits
(reused-sampler-proofs.json). This is eligible local reuse, not a new theorem.
A focused actual sampler extraction accepts (Charon 189.330 s, 538228 KiB;
Aeneas 0.732 s, 70752 KiB; zero swaps), with no external template holes. Its
uncompiled emitted Lean sources are retained under generated-sampler.
The new release lowering uses wrapping integer operations where the retained
proved program uses checked operations. sampler-lowering-delta.json records
that explicit transport obligation and the nominal coordinate conversion;
source-cut identity alone does not discharge it. No sampler-specific Kani
bit-blast is being repeated with larger limits.

Budget audit: 42/60 Kani invocations (27 pass, ten timeout, three compile
failures, one CLI rejection, one rejected draft contract); Lean 0/100. The
assigned env J range is still absent. external-obligations-caller005.json
records the remaining kernel/model boundaries without assuming their desired
whole-body equality. The complete leaf-contract and source/model gates remain
open. Production source remains frozen at 9c131667ca for the active corpus.

### Corpus midpoint resource review

At 510 matching pairs the run remains active, with the frozen production
source unchanged. The midpoint snapshot records 1017569280 anonymous bytes,
2428628992 file-cache bytes, peak total cgroup charge 6443712512 bytes,
pids peak 37, zero swap, no OOM/max events and 74 GiB disk available.
The 6 GiB soft-limit events reflect the retained oracle-log cache; the
original 6G/8G/no-swap/64-task limits remain. See
corpus-1000-002/resource-review-midpoint.json. This is a partial checkpoint,
not a completed differential or absolute timing gate.

### Final 1000-pair differential gate: passed

corpus-1000-002 completes all 1000 pairs on production source
9c131667ca00f4daae78da6299b09a9fe0d00da9, exit 0: 600 successful
proof pairs (100 after a rejected prefix) and 400 error-path pairs, with exactly
100 cases in each tape class. Every complete returned record, actual L1
ledger record/event stream and public worker event stream matches. All
public/proof byte files match literally; four selected complete supplied
oracle streams also match literally. Successful outputs pass strict tx1/tx2
verification. Scope wall 14050.833 s, GNU time peak RSS 619596 KiB, swap 0;
aggregate cgroup peak 6443712512 bytes, pids peak 37, no max/OOM events.
The soft-limit events include retained oracle-log page cache, as reviewed
at the midpoint. differential-1000-final.json is the concise release-gate
summary; the 1000 individual comparison files and full receipt are retained.
This is empirical equivalence on those cases, not universal model refinement.

### Final quiet-host check: blocked, absolute timing unmeasured

The post-corpus check finds one populated 8 GiB peer scope:
run-r398b48eab4d44c4295b8e78a9cd95da9.scope. It belongs to
s126-real-sdk-20261021, original_point_matches_fission with solver Z3.
Its orphaned Z3 PID 2095724 has parent 1, about 22 h 43 min elapsed and
99.9% CPU at inspection. Load is 4.47 7.29 8.16. The peer process is not
killed, and no absolute timing sample is launched. quiet-final-preflight.json
retains the inventory. Once the lead coordinates a quiet host, run the
already prepared absolute-timing.py pipeline-003 under the capped runner,
without repeating the unchanged 1000-pair corpus.

### Handoff boundary

The candidate remains unadopted and unmerged. Stage 2 still needs the quiet
absolute gate and the complete per-leaf contract/binding audit. Stage 3 has
translation evidence but no new checked per-attempt/model theorem. The
required assigned env J range has not been supplied; Lean use remains 0/100,
Kani 42/60 (27 passes, ten timeouts, three compilation failures, one CLI
rejection and one rejected draft contract). No source/model, RunJoin, E1/E2
distribution, L1/L2 joint coupling, observer/oracle transport or compiler/native
experiment instance is silently assumed closed. The exact external inventory
and explicit remaining obligations are in external-obligations-caller005.json,
sampler-lowering-delta.json and design/PROVER-RW-20261023-PROOF-STATUS.md.
Conjunct 1 and the security target are not yet established. No push or merge
is performed, and retained keys and host evidence are preserved.
