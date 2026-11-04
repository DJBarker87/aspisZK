# NFL handoff — cone map refresh

**Numbers are status, not new credit. Target not yet established.**

## Established claim and deliverables

This job maps all **587** NFK function occurrences to canonical S1–S10 subjects or their frozen directed call prerequisites, with an explicit reason, same-transaction path and body hash for every assignment. The authoritative status remains **219 CLOSED / 2 QUALIFIED / 366 OPEN**. No cone gains a new CLOSED status, and no theorem premise is newly discharged.

- [NFL_CONEMAP.md](NFL_CONEMAP.md): canonical four-column ten-row table, counts and per-cone families, historical retirements, remaining conditions and unchanged Rc10 status.
- [NFL_ROW_TO_CONE.json](NFL_ROW_TO_CONE.json): exhaustive occurrence mapping, anchors, paths, input hashes, frozen source revision, support references and overlapping counts.
- [NFL_GAPS.md](NFL_GAPS.md): absent runtime/release/budget/Pool obligations, uncovered native counterparts, qualification, no-cone bucket and all 32 raw Rc7 P rows.
- [NFL_PREMISE_COVERAGE.json](NFL_PREMISE_COVERAGE.json): machine-readable 32-row P crosswalk, candidate sites/counts, native/global distinction, accepted historical retirement references and zero new discharges.
- [NFL_ATTEMPTS.jsonl](NFL_ATTEMPTS.jsonl), [NFL_VALIDATION.json](NFL_VALIDATION.json), [NFL_HISTORICAL_RECEIPT_REVIEW.json](NFL_HISTORICAL_RECEIPT_REVIEW.json) and NFL_FINAL_CHECK.json: audit trail and validation scope.

Builders are NFL_build.py and NFL_report.py; NFL_validate.py performs receipt/source consistency checks only. Every input is already committed and hash-pinned or read from a pinned Git object. No downloaded or uncommitted source is required.

## Assumptions and historical boundary

Discharged here: **none**. Added by this job: **none**. Changed: **none**. Retained explicitly: RuntimePersistence, RuntimeSyscall/RuntimeSha256Value, Allocator/entry/runtime/SDK/std, P6/D188 option A / NativeContractSemanticTransport and P7. NFK already adds RuntimeReturnData (ab) and RuntimeMemcmp (ac), still **pending owner confirmation**. Their conditional ledger statuses are preserved and never counted as discharging the trust laws. Pool return-data association is independently OPEN.

The original map's initial Rc7 matrix is superseded on the same date by Rc8/Rc9/Rc10 appendices. S6's scoped historical CLOSED status and FIs/FGm round/dot retirements are reused from that dated map and the stored Rc10_059 receipt; this job does not transport their theorem statements to the later frozen Rust inventory. Native/global L142–L146, runtime association L159/L185/L181, L166 Result/effects/rejected-prefix association and L187/L188 release gates remain as identified in the canonical last appendix. L154 and a simultaneous joint release witness stay separate gates. The D188 rejected Parse-versus-panic discrepancy stays explicit.

## What slices touch

Q has 0/2 CLOSED roots; geometry is QUALIFIED in both TXs. S has 7/7 CLOSED roots conditionally on ab/ac. No entire cone has zero shared-prerequisite intersection with both slices. S1/S2/S3/S9 principal subject anchors are outside both slices and remain OPEN in NFK, while generic arithmetic overlaps. S8 is only partly outside: residue updates TX1:195/TX2:125 are CLOSED in Q; accumulator/compact/final-dot roots remain OPEN outside it. S2 runtime association and S10 artifact/replay/audit obligations have no adequate function counterpart. No occurrence is wholly outside the ten-cone universe because S10 explicitly covers every source site; eight OPEN rows have only S10 placement under the selected directed cuts and are listed for review.

## Validation performed and reused

Fresh read-only Python audit: all 587 frozen body hashes and 41 complete source-file hashes checked against Git revision `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`; every assignment path checked, independent graph closures recomputed, global/cone/Q/S counts reconciled, ledger uncompressed hash sidecar checked, and all 32 raw Rc7 P rows inventoried. Exit 0; wall time and audit revision in NFL_VALIDATION.json. No new Lean/Kani/Rust/native command, source extraction, axioms check, cold replay or host build. Historical Rc10_059 metadata/axioms are explicitly reused, not rerun. No K2-quarantined or K3-suspended result is promoted or newly credited.

Final packaging checks reconcile table numbers, tracked scope, branch and file-size cap; NFL_FINAL_CHECK.json hashes the delivered artifacts. No output exceeds 20 MiB. Only NFL_ files in evidence/conemap2-20261104/ are changed. No push.

## Remaining blocker and next concrete deliverable

A lead-reviewed source/model/domain crosswalk and concrete composition is still needed to retire any remaining premise; a shared CLOSED helper is insufficient. Next: review the exact anchor cuts and eight S10-only placements, supply the missing Q geometry retarget receipt and query/four-dot composition, instantiate native/global Pair/matching/semantic endpoint laws and same runtime/Pool association, then perform coherent final release replay L187 and trust/adoption/artifact audit L188. Owner confirmation of ab/ac is pending rather than presumed. The fixed security target is unchanged.

Stage commits: `575913df90d` (occurrence mapping), `a571069870a` (cone report, gaps and receipt validation). Final packaging is a separate local commit, `Finalize cone map handoff and checks`.
