# NEZ authoritative ledger handoff

**202/587 composed occurrences CLOSED; 385 OPEN. Target not yet established.** This is +114 occurrences over NEN's 88. TX1: 101/345; TX2: 101/242. Unique functions: 109/434 CLOSED.

| Slice | Attributed CLOSED occurrences (disjoint) | CLOSED inventory membership (overlapping) | Unique CLOSED functions | TX1 membership | TX2 membership | CLOSED roots |
|---|---:|---:|---:|---:|---:|---:|
| Q | 120 | 122 | 61 | 61 | 61 | 0/2 |
| S | 82 | 84 | 50 | 42 | 42 | 2/7 |

Four occurrences overlap: M31::from_le_bytes and WideExact::to_limbs, each in both TXs. They count once globally. NEX itself checks 82 S occurrences; unified S membership also includes the two inherited Q-certified WideExact::to_limbs occurrences. The union has 109 unique functions, not 61+50. Per-function occurrence/status records are in NEZ_per_function; every occurrence is listed in NEZ_LEDGER.md.

## Exact claim and root references

NEZ_LEDGER.json.xz retains the complete authoritative NEN baseline, historical claims, receipt statuses and qualifications, then integrates every requested merged lane and current C3-BIN rulings. Unchanged NDT/NCZ baseline structural invariants and unchanged NEO/NET/NEI/NEM/NEQ/NEU/NEX certificate gates execute. NEN's exit-0 full replay and content-addressed outputs/source pins are reused, rather than relabelled as a new historical replay. NEZ adds explicit current-support binding, K-3/K-2 denial, source-route identity, claim/certificate maps, trust-use inventory and reconciliation.

Two S roots are CLOSED-CONDITIONAL hybrid certificates (three occurrence rows):

- Statement validator, TX1:276 and TX2:169: NEM_ValidatorComposed.result_state_effects, evidence/slice-s-compose5-20261102/NEM_L018/receipt.json, plus reached payment/lane/late domain theorems and checked NEE/NEL native caller frames. Complete statement and retained root qualifications: NEM_COMPOSED.md and NEZ_certificates at those rows.
- Statement encoder, TX2:165: NEQ_EncoderOracle.result_state_effects/substitution, evidence/slice-s-compose6-20261102/NEQ_L007/receipt.json, plus NEQ_LateBorrow, NEQ_RootFrame and NEQ_EncoderDomains, exact child arguments, arbitrary late poststate, outside frame and typed complete return. Complete statement and retained qualifications: NEQ_COMPOSED.md and NEZ_certificates.

All inner caller/callee/domain/Result/carrier/state/ordered-effect obligations are credited only through complete checked instances. Root-owned PacketDomain/PhysicalInterpretation and source/ABI/library/allocator/runtime/tool/P6 transport qualifications remain. These are not kernel-only Rust theorems or an artifact-connected composed security theorem. No missing source-refinement proof is reclassified as a cryptographic assumption.

Actual validator CLOSED counts: NEB 66, NEE 6, NEJ 14, NEL 22, NEN 88, NEO 130, NET 144, NEI 66, NEM 50, NEQ 68, NEU 72, NEX 82. NEO/NET totals include inherited global rows; S continuation totals are S rows. NEZ_validator_coverage distinguishes these scopes.

**Every slice-reported CLOSED row is accepted: zero unified rejections.** NEZ_rejected_slice_closures is empty; the final artifact check verifies that the union of reported CLOSED IDs minus actual CLOSED IDs equals the complete rejection list. All 202 reported occurrences reconcile; no discarded closure is hidden.

## Trust, suspensions and assumptions

Ruling z(1) is the exact deployed cfg-constant None/no-effect specialization, preserving phase argument evaluation. Historical function-pointer quarantine is unchanged. Ruling z(2)'s regenerated committed inputs, direct fixed-backend payload, seven-operation order and six original mutations are rechecked; this closes no full inverse or Q root. Generic backends remain excluded. Field multiplication is not Kani credit.

Ruling aa retains existing Allocator trust: safe Box certificates require same value, same fresh allocation/ownership and exact error cleanup, with original matched controls. Unsafe/MaybeUninit remains under the earlier P6 ruling. Per-row aa uses are explicit in NEZ_rulings_used.

Ruling ab ADDS RuntimeReturnData. It is not a removal or part of RuntimeSyscall. Five individually inventoried model theorem uses: NEX_ReturnData.set_preserves_order/runtime_bound/observable (NEX_L014), and NEX_EmitRuntime.result_state_effects/success (NEX_L039). One OPEN support consumer: emit_result, TX2:219, tagged RuntimeReturnData. CLOSED native uses: 0; CLOSED roots using ab: 0. The native binding/encoder/ordered exact bytes/no-later-write obligations remain OPEN. The Pool's immediate post-CPI read, program-id check and same-context/no-intervening-CPI association is separately OPEN. Model event laws do not prove platform readback, and Unit cannot erase the event.

No SUSPENDED or K-2 quarantined receipt is restored. Newly selected receipts that NEN only inventoried as OPEN receive explicit receipt-pinned rule-16 review under the unchanged native/source/control/feature gates, with the original review retained in NEZ_prior_review. Four fold occurrences use checked immutable actual-body D188 source proofs with zero Kani credit; they do not select historical failed native receipts. NEZ_claims/NEZ_certificates identify the actual current selection. NEN_* fields remain historical audits.

No protocol, frozen implementation, numerical security contract, carrier or failure event changed. Existing RuntimePersistence and other trust rows remain. RuntimeReturnData is the one explicit addition. The unchanged 100-bit per-attempt, privacy and two-transaction target remains not established.

## Validation actually run

- Committed-source complete NEZ status refresh and output round-trip: exit 0, wall 356.660307 s, sampled aggregate peak RSS 1,226,964,992 bytes. Receipt NEZ_FINAL.json.
- 18 NEZ mutation checks: exit 0, wall 2.517793 s, sampled aggregate peak RSS 501,841,920 bytes. Receipt NEZ_TESTS.json.
- 19 unchanged NEN mutation checks: exit 0, wall 71.060824 s, sampled aggregate peak RSS 428,752,896 bytes. Receipt NEZ_NEN_TESTS.json.
- Final focused artifact/report/reconciliation checks: exit 0, wall 2.340116 s, sampled aggregate peak RSS 584,318,976 bytes. Receipt NEZ_ARTIFACTS_CANONICAL.json.

The full status refresh ran source revision b6c824f7fa7454fb622ef4cf994af22e059a6d44; exact command, source SHA256, RSS sampling and limits are in NEZ_FINAL.json. Subsequent changes affect only markdown(): NEZ_ARTIFACTS_CANONICAL proves every other validator AST node equals the successful committed source, checks report order independence, canonical compressed-data SHA256, coverage, active receipt denials and exhaustive closure reconciliation. No unchanged full gate replay or mutation suite was repeated for reporting edits. NEZ_OUTPUTS.json pins delivered bytes.

All runs here are Python/Git status checks: 0 Lean, 0 Kani, 0 native/SBF builds, no remote or wallet/key operations. Python aggregate RSS watchdog is 7 GiB with 0.5-second samples; swap is explicitly unmeasured on Darwin. No new #print axioms ran. Historical exact-source axiom audits are rechecked/reused by the original gates (only propext, Classical.choice, Quot.sound). This is not a new formal release replay. NDT's historical replay and 53 baseline mutation checks are reused through NEN's pinned evidence; 19 NEN checks ran afresh here.

The ledger is 68,927,602 bytes uncompressed and therefore delivered as NEZ_LEDGER.json.xz with NEZ_LEDGER.json.sha256. All committed files are below 20 MB. Failed sparse-input probes, NEZ_BUILD1's support-reader error, NEZ_BUILD2's provisional support-selection mistakes and reporting corrections are retained in NEZ_ATTEMPTS.jsonl, stdout/stderr and NEZ_DEVELOPMENT.md. No failed or provisional result earns final credit.

## Remaining obligations and next deliverable

385 occurrences remain OPEN. Q's query_loop and QueryGeometry::for_range need the actual remaining loop/native reserve/callee-domain/full Result/frame joins identified in NET_HANDOFF/NET_REMAINING; z(2) cannot supply a missing inverse bridge. S's next concrete work is the split terminal-parent return/validator native association, then public forwarding/Box/root join; independently finish actual result binding and 792-byte encoder native association before emit_result under explicit RuntimeReturnData. Request/reconstruction/scanner blockers and complete remaining-member lists remain in NEX_STOP_AUDIT and the requested slice handoffs. Root-local certificates do not close these parents or the release theorem.

## Repository disposition and reproduction

Actual existing branch codex/cx-ledger5-20261104 retained; the brief named codex/cx-ledger5-20261029. Stage 1: ceb98f78094 (input inventory). Stage 2: b6c824f7fa7 (validator implementation). Stage 3 commits these authoritative outputs and handoff. All changes are confined to evidence/ledger5-20261104. Nothing pushed. Shipped source and artifact pins are unchanged; no ELF rebuild or fresh source-to-ELF claim.

Recompute and compare (status checks only):

    python3 evidence/ledger5-20261104/NEZ_validate.py

Focused final artifacts/report check:

    python3 evidence/ledger5-20261104/NEZ_artifact_checks.py

Mutation suite:

    python3 evidence/ledger5-20261104/NEZ_tests.py

Use NEZ_run.py <receipt-name> <python-target> [args] for a new metered receipt only when source/input changes or evidence is missing. No Lean or Kani is authorized by this handoff.
