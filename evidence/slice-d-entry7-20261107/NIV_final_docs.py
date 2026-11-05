from pathlib import Path
import json
E=Path(__file__).resolve().parent;x=json.loads((E/'NIV_AUDIT.json').read_text());ex=json.loads((E/'NIV_EXPORT.json').read_text());s=x['kani_budget']['classifications'];f=x['formal_budget']
(E/'NIV_HANDOFF.md').write_text(f'''# NIV entry7 handoff

Target not established. No new composed rows or CLOSED candidates; all17 assigned entry occurrences remain OPEN. Baseline is ledger12/NIR_LEDGER, not presumed ledger13 adoption. Frozen revision4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; headline AspisR1.RPx_Deployed.deployed. Frozen3, L154 statement parameter, narrowed D188, privacy and per-attempt100-bit target retained; no grinding or work-normalized credit.

## Results and gates

One authorized deployed compiler warm build; binding preflight successful; single permitted extraction succeeded (NIV_L022). Actual frozen entry and process bodies emitted. All opaque external templates remain UNCOMPILED evidence, never axioms in an admitted module. NIV_RawBoundary exposes every reached external primitive and child; NIV_ExtractedForward proves body/source profile association; NIV_ForwardPacket composes complete model replies, same descriptors, state/effects and rejection frames. Native primitive/profile and full local-call-log realization remain OPEN.

NIV_SnapshotSequence/Domain/Write establish complete model record production and SDK borrow/drop/copy histories under the SAME world, apply admission1/admission2 via the named RuntimeEntrypointAdmission contract and retain explicit returned-byte length obligations. They do not prove native ABI. NIS Digest/Public/Error carriers and NHL_Tx1Model/NHT_Tx2AuthModel candidate laws are reused read-only. No candidate-success premise supplied. NIV_OwnedPrefixes and NIV_AuthPrefixes supply explicit abort-prefix cuts.

Combined import NIV_L027 PASS; fidelity fixtures NIV_L0328 PASS; raw ax2 NIV_L033 all41 roots only standard axioms; NFX NIV_L034 exit0 over{x['NFX']['loaded_modules']} modules, no dangling/import disagreement. Current source hashes match every compiled receipt in NIV_SOURCE_MANIFEST.json. The raw audit and scanner binaries are pinned before/after invocation. No unchanged full replay repeated.

## Native budget and limits

120/120 Kani consumed: {s.get('bounded_positive',0)} bounded positives, {s.get('matched_failing_control',0)} matched failing controls and {s.get('diagnostic',0)} diagnostic failures. Full native domains are not inferred from fixtures. Forwarding probes cover all27 result tags, arbitrary Customu32, fixed Borsh string; SDK probes cover all76 scalar/metadata byte coordinates across3/7 independent one-byte account buffers, child-Err branch and one arbitrary lamport frame word; registry probes cover10 ordered errors in both deployed policy instantiations. None is a composed-row closure.

Formal scopes{f['scopes_used']}/90 ({f['lean_compiles']} Lean compiles, with failed revisions retained), extraction1/1, warm build1. All scopes had fresh admission allowed:true plus exit0 and unchanged MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64; Lean-M7000. Maximum accepted scanner RSS7258412KiB, swap0. Every exact command, target, revision, source/dependency hashes, exit, wall, peak RSS, swap and axioms is in per-attempt receipts and NIV_RESULTS.tsv. Early Lean-only receipts omitted CARGO_TARGET_DIR; no Cargo ran there, and the omission is retained honestly in NIV_TARGET_DIRS.json rather than rewriting evidence.

Failures: K023 invalid deferred-error fixture; K038 all-alias/full-field timeout, no retry; K039 harness-wide lamport memcmp unwind, replaced by arbitrary word; K060 conflicting unused data-contract stub, removed while retaining actual data body. Formal parser/namespace/proof and owned warm/preflight repairs are recorded in NIV_FAILING_STEP.md. No cap/timeout increase, no unchanged killed/timed-out rerun. No field multiplication in Kani, SHA unwind, new native function contract, writable static, K-2-dependent credited claim or new trust row. RuntimeCpiReadonlyEntry7 unused.

## Retained workspace and next deliverable

Host /home/dombarker/project-offloads/codex-cx-slice-d-entry7-20261107; ONE source corpus NIV_src (historical aliases NIJ_src/NHY_src), native CARGO_TARGET_DIR NIV_target, extraction/warm target NIV_NHR_target. Exact KMX patch pinned and frozen source/lock/graph checked before every native run, lock unchanged afterward; offline deployed features. Original source and shipped files remain unchanged, so no ELF rebuild performed; inherited f8c0ec72… /63ad3e9c… /121f3e29… pins are not fresh rebuild evidence.

NIS seed:89 retained files10628944 bytes, required export443ef40bff98 has36 objects4091640 bytes; see NIV seed manifests. New export: {ex['path']}, {ex['bytes']} bytes, tree{ex['tree_sha256']}; never delete the owned cache. All libraries resolved by LEAN_PATH pinned per formal receipt. No sibling or session A worktree modified.

Next deliverable remains a complete native full-input/full-result local-record forwarding packet or full SDK producer/write packet. NIV_REMAINING.md records every member's exact missing native facts; no outstanding Lean-only theorem can manufacture them. Kani budget exhaustion does not assert closure. No push. Review NIV_AUDIT.json/NIV_LEDGER_DELTA.json before the next ledger gate.
''')
p=E/'NIV_REMAINING.md';t=p.read_text().replace('are being checked','were checked').replace('are being\nchecked','were checked')
t+='\nFinal stop accounting: all120 native slots and the sole extraction were used. Formal/model-only work and the complete combined audit are finished; remaining formal slots cannot discharge the native realization and caller-domain facts listed member by member above. No timed-out shape is retried. No new row is promoted, and the target remains unestablished.\n';p.write_text(t)
print('NIV final handoff and member-by-member stop accounting written')
