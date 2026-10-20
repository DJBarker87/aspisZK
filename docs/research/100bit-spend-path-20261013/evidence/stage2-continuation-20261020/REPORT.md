# Stage-2 continuation (2026-10-20)

VERIFIER SOURCE CHANGE. Branch `codex/cx-stage2b-20261020`; no push.
Continuation of `../stage2-refactor-extraction-20261020/REPORT.md` and
`../../design/STAGE2-REFACTOR-20261020.md`. Retained build workspace:
`/home/dombarker/project-offloads/codex-cx-stage2b-20261020`.

## Fix and extraction boundary

The old report's span description was incorrect: zero-based columns
237:20–22 identify **`&v`**, not `&a`. The initial accumulator-only experiment
still failed on the View borrow. The successful repair preserves the early
inactive decoder and folded-root authentication, then constructs the relation
View after the query loop. Its folded_root is None because finish_relation
reads only round0, round1 and final_message (mechanically checked by
`harness/check-specialization.py`). No authentication check was removed.

Translating the whole cone exposed additional pinned-translator loan joins:
Reader/cursor loops, returned aggregate references, mixed Prepared root/query
loans, scratch arrays, insertion sort, geometry prefix products, mutable
weight iteration, accumulator optional borrows, and Merkle sibling reads.
Small concrete helpers isolate these loans, owned results carry query state,
and explicit ordered tree calls preserve the three-root order. The batched
accumulator is the old Some branch, mechanically checked after transparent
getter expansion and invariant width hoisting. The legacy optional/audit path
remains. The compact wire format, account layout, challenge/hash grammar,
Pool/registry ids and accepted variant set are unchanged by these edits.
These are source checks and regression evidence, not a universal equivalence
proof.

`attempts.json` indexes every source-changing attempt, its exact patch and
source hashes, both phase receipts, and failure diagnostics. The first full
success is attempt 43. Later changes address runtime CU and the emitter's
indentation limit: the ten semantic-alpha reads move to a concrete helper so
the complete resume body parses and type-checks without raising Lean limits.
No unchanged extraction failure was retried and no memory cap was raised.
Each retained LLBC has its own SHA/size/input pins; LLBC and executable
binaries stay on the host.

The root is the actual `crate::verifier::candidate::tx2_authenticated`.
All parser, orchestration, resume, query, accumulation, relation and Merkle
bodies remain concrete; no synthetic orchestrator replaces them. Existing
arithmetic/heap/hash/weights/domain/dot/pairing/trace methods remain explicit
backend frontiers. Only the layouts of Point, SecureCirclePoint, M31, CM31,
QM31 and WideExact are included through the opaque arithmetic boundary.
Pinned Charon/driver/Aeneas hashes are verified before execution.

## First local facts

- `Stage2ContinuationParse.successful_length`: successful compact parse
  implies equality with the fixed PROOF_BYTES length. The source parser and
  existing explicit-operation adapter are mechanically matched by
  `harness/check-parse.py`.
- `AspisR1Stage2.resume_rehash_checkpoint_field`: success of the **complete
  emitted resume body**, with typed callees universally parameterized, implies
  that the proof digest equals the stored bytes 16..48, assuming the named
  byte-comparison soundness premise. The theorem records the actual slice
  read, singleton proof-digest input conversion and digest result. Later
  checkpoint decoding is retained, not cut off at the authentication prefix.
- `AspisR1Stage2.stage2_twelve_ordered_calls`: the **three entire emitted
  query-loop definitions**, with only query_values parameterized, equal the
  Result-carrying loop model. A successful run from next=10 consists of
  twelve sequential query calls ending at next=22. The successful-query
  increment is derived from the complete emitted query/accumulation bodies
  and checked Usize addition, with arbitrary typed arithmetic/trace callees.
  No increment premise is needed in the final theorem. The Chain records each intermediate
  accumulator and batched-weight state and each successful call in order.

`proofs/*/receipt.json` contains exact module/source/import/compiler hashes,
revision, command, exit, wall, peak RSS, swaps and complete #print axioms.
Successful audits use only a subset of propext, Classical.choice, Quot.sound.
Failed elaborations (including their sorryAx diagnostics) are historical
failures, never accepted proof evidence. The final source modules contain no
sorry, admit, axioms, native_decide or new resource-limit settings. Raw Aeneas
output keeps the emitter's existing settings; generated external templates
are not imported as assumed proofs.

## Gates and ELF

Final source: `2ec37343acfb1b857cbec6569ad3175930a962bb`.
Final extraction: `checkpoint-k-inline-55`; Charon exit 0 (82.140 s,
549,820 KiB RSS, zero swaps), Aeneas exit 0 (20.261 s, 911,412 KiB,
zero swaps). LLBC: `4c36344e1de0f90dfa074fc35a0664408b4f258a11c72617d7a0241fd6aa3182`, 7,009,222 bytes, has_errors=false.
The last inline attribute changes no generated proof-adapter body; all four
binding checks pass against the final output, so unchanged proofs are not
recompiled. `proofs/final-binding.json` ties the final emission to the exact
compiled modules and their actual earlier compilation revisions.

- Codec: 1,233 outputs, byte-identical to the frozen baseline.
- Ordered trace/call-count/acceptance comparisons pass for both adopted and
  audit paths; 1,095 adopted calls and 583 audit calls match the adoption baseline.
- Program: 33 tests, including 23 checkpoint cases. Default crate and detail
  suites pass (detail: 16). Pool: 87/118/123/123 unit tests plus 2 integration
  tests per suite (default/R1/all/v7).
- Proof-size teeth and strict/authenticated tx2 pass; 9,253 trace entries
  match and proof/public/checkpoint mutations are rejected.
- Strict complete-linked-ELF stack audit passes. Stripped ELF SHA-256:
  `9672cc4842d478313293133f5597e8da5a352842f2fbf96371b5fa189fe0f16a`,
  1,506,920 bytes. Linked ELF:
  `ad197ee7d811d288e2092b76dd613e0f69e24453cf94752704a77dc3dd0b223d`,
  1,562,592 bytes. SBF build: exit 0, 29.532 s, 648,676 KiB RSS, zero swaps.
- All six fixtures are accepted. Each stage 1 is ≤ its B1; each settlement
  is ≤ its B1 + 10,000. Smallest margins: 281 CU (transfer-255 stage 1)
  and 201 CU (withdrawal-13 settlement). These are measured fixture gates,
  not an all-input CU theorem.

| Fixture | Stage 1 CU | Settlement CU | Settlement − B1 |
|---|---:|---:|---:|
| transfer-13 | 1,197,177 | 1,138,451 | +8,694 |
| transfer-255 | 1,199,286 | 1,169,491 | +8,425 |
| transfer-1023 | 1,193,428 | 1,169,239 | +8,265 |
| withdrawal-13 | 1,193,569 | 1,148,749 | +9,799 |
| withdrawal-255 | 1,193,699 | 1,178,702 | +8,179 |
| withdrawal-1023 | 1,195,178 | 1,176,274 | +6,011 |

The unchanged saved adoption proofs run through the **new SBF ELF** with the
pinned adoption driver and B1 Pool/registry. Its native dependency is old;
independent freshly compiled native tests supply this packet's native checks.
Runtime input hashes (driver, Pool, registry, proof/public fixtures) are
verified again at final collection.

P_R1: **8/8 accepted and strictly/densely verified**. The separate retry
loop accepts in one attempt and verifies. Optimized gate exit 0; wall
345.230 s; peak RSS 587,044 KiB; zero swaps. `final/r1p-retry-gate.json`
contains per-attempt verdicts and durations. `final/runs.json` and its 21
receipts record commands, exact source hashes/revision, exits, timing, RSS,
swap and scope caps; every final-source gate exits 0. Historical failures are retained under `historical-runtime/`; a CU
criterion failure stopped later gates. Restoring the isolated limb loops
recovered most overhead. Removing the measured-slower query adapters and
looped checkpoint-query reader restored the transfer budgets; inlining
Reader::k recovered 354 settlement CU per fixture and closed withdrawal-13.
No budget was relaxed. Source bytes were translated before their source
commit; lowering receipts keep the actual base marker plus exact source
hashes/patches, while final pins verify equality to committed source 2ec37343a.

The literal required RUSTFLAGS `-C link-arg=-Wl,--threads=4` works with native
cc, but the SBF linker is direct rust-lld and rejects the cc-style -Wl flag.
The first SBF build failed before linking. A pinned target-only executable
shim converts exactly that one argument to --threads=4 and invokes the pinned
platform-tools rust-lld; it preserves the literal RUSTFLAGS and logs calls.
This is an explicit toolchain adaptation, not a compiler or optimization
profile change. Complete-linked-ELF strict stack audits passed for the
subsequent measured candidates.

## Diagnostic profiling

`profiling/comparison.json` compares observer-enabled source b2f138abf with
7d4c136f0 on the same transfer-13 proof. It points to query/flush costs, with
smaller Merkle and resume deltas. These are diagnostic builds and are excluded
from release CU criteria. The first baseline profiling command incorrectly
reused the candidate artifact from the shared Cargo cache after copying a tree
with older input mtimes; identical ELF hashes exposed this. That comparison is
invalid and retained as `baseline-execution.json`. Refreshing the three changed
Rust inputs plus the program input forced the intended rebuild under a new
receipt, `baseline-refreshed`; metadata confirms the separate manifest paths.
No failed release criterion has been relaxed.

## Resources and obligations

Every Rust, Charon, Aeneas and SBF command runs in its own MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64 scope. Native arithmetic/proof
work is optimized with -j4; Charon uses one compiler job. The host has a
55 GiB working reservation limit; populated scopes are checked before jobs.
No job reached the mandatory 24 GiB review point or used swap. Focused local
Lean uses the prescribed mkdir lock, one -j1/-M4400 process and a private
object directory. An intermediate resource inventory saw another worker’s unbounded Lean scope
and raised a metadata assertion; this task’s scopes stayed capped. The next
inventory again showed only our 8G retry scope. No other job was touched.
Metadata-only collection also initially encountered a null LLBC declaration
slot; skipping null slots fixed collection while preserving every required
concrete-body assertion. Both preflight failures are retained under
`metadata-failures/`. All task keys and refundable authorities are retained;
there is no network deployment or key cleanup.

Remaining: instantiate the explicit operation adapters with concrete backend
models and prove their correspondence; prove full source/model/Checks
refinement (R13/R12), field arithmetic and Merkle backend correctness;
authenticated checkpoint provenance and skipped-value canonicality (R15);
all-input oracle/first-read bounds (R19); deployment/release-certificate correspondence
and analytical CU bound (S8). Whole-cone Aeneas emission and the first shape
facts do not discharge these obligations. The raw Funs/Types output is pinned;
it is not claimed as a fully compiled backend-complete verification package.
