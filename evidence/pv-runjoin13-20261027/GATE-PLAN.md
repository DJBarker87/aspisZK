# Combined records/op223 gate plan — lead-owned, not executed here

Run gates (b) and (c) once on the final candidate containing both the records rewrite from
2910da23a3 and the lead-selected op223 change. Record the exact combined commit before
building; do not substitute this records-only snapshot for that candidate. Compare against
the pre-rewrite source at dd58cab6376dbd844f32ae764d88c4ca3d780e37 (the entry revision of this task), with an exhaustive crates/programs/lockfile diff. If integration uses a different control, record its exact revision and prove its shipped source content is identical to this control before counting the run.
Retain the exact control and candidate revisions, source hashes, harness/comparator hashes,
toolchains, feature lists, binary hashes and command/environment receipts. The lead supplies
the final combined revision and host directory; these are deliberately not invented here.

Use the method on codex/pv-rebase-20261026 in tools/pv-rebase-20261026/native.py,
compare-fixtures.py, corpus-pipeline.py (corrected v3) and design/PV-REBASE-20261026.md.
Overlay the same diagnostic examples/tools into both private source snapshots without
altering library implementation. Build each harness with cargo build --release --locked
--offline -j 4 -p aspis-r1-cost-probe --example NAME --features
optimized-terminal,r1p-check,ct-host-prover for BOTH variants. This entry control already has ct-host-prover; the older rebase experiment's candidate-only selector must not introduce a feature mismatch into this two-rewrite comparison.
NAME is prover_rw_gate for (b) and prover_rw_differential for (c). Pin the native toolchain
and all optimization/linker flags identically across variants. Preserve a binary per variant.

Every build/run requires an admitted reservation receipt, stdout/stderr captured before
collection, and one capped scope at a time: MemoryHigh=6G MemoryMax=8G MemorySwapMax=0
TasksMax=64. Record whether time is in compilation or complete retry-owner proof generation
and P_R1 elimination. Honor quiet windows and reservation refusals; never increase caps.

## (b) Fixed-coin fixtures

Run research first, candidate second, fresh output paths, the complete retrying owner
harness with deterministic coin 0, one transfer and one withdrawal. Invoke each pinned
prover_rw_gate binary as `prover_rw_gate FIXTURE_OUTPUT 0 1` (record its command.json).
Compare each public.bin and proof.bin byte for byte, plus status, callbacks, attempts and
audit with the unchanged compare-fixtures.py logic. Require strict tx1/tx2 verification of
both proofs. Record byte sizes and SHA-256 for all four byte artifacts per source. Any
difference is a failed gate and must be reported, never repaired by changing the comparator.

## (c) 1,000-run differential

Use the unchanged crates/aspis-r1-cost-probe/examples/prover_rw_differential.rs and
tools/prover-rw-20261023/compare-corpus.py. Use fresh corpus paths for this new combined
source pair; old-source cases cannot count toward it. For coin in 1000..1999, invoke each
variant as:

    prover_rw_differential OUTPUT COIN 1 LOG_ORACLE

LOG_ORACLE=1 exactly for 1006, 1007, 1010, 1011, otherwise 0. The harness chooses its ten
tape classes unchanged. Compare each pair with:

    python3 compare-corpus.py BASELINE_OUTPUT CANDIDATE_OUTPUT COMPARISON_JSON

Use corrected v3 scheduling: at most three prover processes total across both variants,
accounting for both variants' 16-worker P_R1 teams. Check pids.events.max == 0 after each
comparison and at completion; a task-limit event invalidates the cohort, not a proof result.
Preserve memory/swap/pids peaks and events, resource reviews and all failures. Require
1,000 passing pairs, 600 successful proof pairs, 100 forced-rejected-prefix pairs, 400
error-tape pairs and four complete ordered supplied-oracle-stream comparisons. Compare
all returned/ledger/event records and full public/proof bytes; require strict tx1/tx2 on
successful proofs. Resume only completed cases from this exact source/environment cohort;
retain incomplete or invalidated output rather than silently overwriting it.

These are finite adoption measurements. They do not discharge universal source refinement,
RunJoin, E1/E2, L1/L2/L3, or the deployed privacy endpoint. No additional T field is allowed.
