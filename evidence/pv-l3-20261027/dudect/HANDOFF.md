# D289 / V374 preparation handoff

Target not yet established. V374 was OPEN/P before this task and remains OPEN/P.
No premise is removed, added, weakened or moved into T. V371 remains the stated
DOITM OFF limitation. This task delivers preparation, synthetic feasibility/cost
checks and static artifact comparisons. It supplies no qualifying measurement,
constant-time theorem, full-prover timing result or privacy claim.

The final binaries are pinned in ready.json. The candidate is exactly the
requested 73070ddd51 source with the recommended recipe. The harness is the
standalone tools/pv-dudect package, source-linked to that candidate. No release
program depends on either new tools crate; metadata/release-dependency-isolation.json
includes the default r1-cost-probe program as required by ruling (l). Existing
release source/pins are not changed. No Lean/Kani, wallet/account keys, proof,
transaction, OS-entropy sample, or nonce reservation was produced.

V374-PLAN-v2.md in ../dual/ requests one 15-minute quiet window, 12 separately
reported experiments, 1m samples/class each, dudect percentile crops and Welch
|t| 4.5 threshold. The lead must schedule it. The prepared future entrypoint
reads the existing marker; no preparation code writes one. Binaries survive
under the job's host bin/; cargo targets are deleted after static validation.
Offline statistical analysis follows the window under a separate admitted cap.

Validation: optimized harness and recommended devnet_spend builds, pinned
source/feature review, conservative normalized symbol comparisons, Python
syntax checks and a synthetic known-value Welch accumulator check. All actual
host scopes are indexed in run-index.json with target, exit, wall, RSS, swap,
revision and N/A axioms. Candidate build: exit 0, 109.778s, 1,897,906,176-byte
cgroup peak, swap 0. Final harness build: build-harness@6 exit 0. No memory
kill, raised cap, reservation refusal or unchanged full regression occurred.

Dry@2 is the final 1,000/class check, **not a measurement**; all 12 families
completed with zero migrations and expected result counts. It writes only
aggregate cost summaries; no raw timing sample CSV or leakage statistic was
created. Earlier dry is retained as superseded: final build changed the
measurement-window parser to accept fractional epoch deadlines and added
fail-closed sampler-result checks. Both changes are recorded source changes,
not an unchanged rerun. Other harness builds correspond to compiler typo fix,
warmup/status instrumentation, serialization/rejection-class refinement and
source dependency tracking. First build wrapper failed before Cargo due to an
incorrect rustc path; build-harness@2 then exposed a QM31 constructor typo
(exit 101); both were fixed without touching crates/ or raising caps.

Instruction result: compressor and QM31::try_inv match; M31 and pole full
symbols differ in cold panic metadata; sampler has return-register differences;
scalar sampler/seed checks have different function boundaries. See
INSTRUCTION-EQUIVALENCE.md for locations and strict attribution. Results will
speak for the harness binary, with only the specifically matched leaf binding.

Next concrete deliverable: lead schedules the window, invokes the pinned
window entrypoint, retains raw CSV/environment/status/monitor receipts and
runs the preregistered offline analysis. Lead review must address any crossing,
incomplete budget or artifact mismatch before changing V374.
