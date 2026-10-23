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
