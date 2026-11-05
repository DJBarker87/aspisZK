from pathlib import Path
import json,collections,re,hashlib
E=Path(__file__).resolve().parent

def report(L,resources):
 rows=L['rows'];groups={'b':[r for r in rows if r['function'].startswith('programs/')],'c':[r for r in rows if r['function'].startswith('crates/')]}
 assert len(groups['b'])==53 and len(groups['c'])==546
 intro='# NIU physical row distance\n\nTarget not yet established. Same conservative owner partition as NIR: all599 verifier rows, including CLOSED prerequisites. These are graph/owner distances, not a proof of runtime/ELF identity. The complete original root domains, same-input/Result/effect/frame, P6/source-to-ELF and runtime qualifications remain. No new physical exporter is required under(ao).\n\n| Hypothesis | Existing rows | CLOSED | OPEN | QUALIFIED |\n|---|---:|---:|---:|---:|\n'
 for g,rs in groups.items():
  c=collections.Counter(r['status']for r in rs);intro+=f"| (ao)(3)({g}) | {len(rs)} | {c['CLOSED']} | {c['OPEN']} | {c['QUALIFIED']} |\n"
 for g,rs in groups.items():
  intro+=f'\n## (ao)(3)({g})\n\n| Exact row | Status | Function | Canonical owner |\n|---|---|---|---|\n'
  for r in rs:intro+=f"| {r['row']} | {r['status']} | {r['function']} | {r['owner_module']} |\n"
  intro+='\nRemaining OPEN rows: '+', '.join(r['row']for r in rs if r['status']=='OPEN')+'.\n'
 intro+='''
## (ao)(3)(d): named Pool obligations

The599 verifier rows contain ZERO production Pool-consumer occurrences. Three inherited helper rows remain CLOSED: pair_forest_dispatch.supported_loader, processor.require_transaction_level_invocation_v1 and error.convertPoolError. This is not3/3 production Pool closure. No finite complete deployed-root Pool inventory is available in this basis; the following named obligations remain separate.

| Obligation | Status | Exact missing association |
|---|---|---|
| NIB-P1 | OPEN | SAME CPI invocation, emitted bytes/program-id/register continuity, immediate read, no intervening CPI/set/clear. RuntimeReturnData/ReturnDataClear do not prove the caller. |
| NIB-P2 | OPEN | Actual production validation dictionary, full Result/error and SAME decoded statement/result. |
| NIB-P3 | OPEN | Actual production lane dictionary and SAME source state/carriers. |
| NIB-P4 | OPEN | Complete settlement/withdrawal/mutation/borrow/cleanup frame through actual production continuation. |
| POOL.prefix_to_cpi | OPEN | Production B prefix, reached accounts, exact CPI/meta/payload and live-guard domains. |
| POOL.read_to_settlement | PROVED-conditional model / production OPEN | NIB_ReadToSettlement.read_to_settlement is retained, with P1..P4 producers uninstantiated. |

### Four held CPI/callback sites

All four remain OPEN; NIO supplies local support, zero actual-site certificates. RuntimeEntrypointAdmission-Pool now supplies the SAME initial seven fields, while reached layouts, uniqueness, physical-cell use, CPI frames and source/native argument association remain to prove. No RuntimeCpiReadonlyEntry7 use.

| Actual source owner | Guarded data | Passed indices / remaining scope | Status |
|---|---|---|---|
| pair_forest.rs::process_pair_forest_deposit_with_runtime_v1 | accounts[1], accounts[2] if fresh/same, accounts[3] if rollover | token_start+[1,0,3,2,4], token_start=3 or4; reached case split, actual metas/payload/token-program and SAME-cell separation | OPEN |
| pair_forest.rs::process_pair_forest_terminal_with_verifier_v1 | accounts[2], accounts[3] if genesis/same, accounts[4] if rollover, accounts[cursor] marker | token_start+[1,0,2,3,4], cursor=4 or5, token_start=cursor+7; full reached native/CPI frame | OPEN |
| pair_processor.rs::process_pair_withdrawal_with_verifier_v1 | history selected current/next index<marker_index, accounts[0], accounts[marker_index] | proof_index+1+[1,0,2,3,4], proof_index=marker_index+4; exact native/meta/CPI association | OPEN |
| transition.rs::apply_authorized_append_after_checked_state_v1 | pool, optional current/next pages | All deployed before_persist deposit/withdrawal/no-op instantiations; marker creation, token CPI, validation and write footprints | OPEN |

Source-level direct-site index separation is NIO inspection, not a native certificate; callback separation is not universal. A reached overlap must be reported as a liveness finding, never assumed away.

### Thirteen exclusive-guard owners

Full original-source ScopeRun/native/counter/child/cleanup association remains OPEN for every owner. Reference-only counter scopes and fixed-prefix helper windows are supporting facts. No owner is completed by the combined import.

| Exact exclusive-guard owner | Status |
|---|---|
'''
 nios=(E.parent/'pool-borrow2-20261107/NIO_REMAINING.md').read_text();owners=re.findall(r'^## (programs/aspis-pool/[^\n]+)',nios,re.M);assert len(owners)==13
 for o in owners:intro+=f'| {o} | OPEN |\n'
 intro+='''
RuntimeEntrypointAdmission-Pool: ADDED-LEAD-20261107 under(ap), existing inventory design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md:45. Fields verbatim: valid, freshGuards, noExternalBorrows, liveAccount, counterZero, sharedCellsOnlyEqualKeys, duplicateKeysShareCell. Initial Pool entrypoint relation only; no CPI frame, token-program behavior or success. NIU documents the lead addition and changes no trust inventory/ledger trust row.

RuntimePersistence remains accepted data-only trust. (ao)(3)(a) extraction stays accepted P6/D188/pinning, and(e) queries stays the L154 statement parameter. Owner decision(aj)(a) remains PENDING. Exact next(d) inventory deliverable: an authoritative deployed-root Pool closure with numbered production rows and all21 accessor sites, followed by full original-source scope packets and NIB-P1..P4 production continuation.
'''
 (E/'NIU_PHYSICAL.md').write_text(intro)
 plan=(E.parent/'ledger12-20261107/NIR_PLAN_STATUS.md').read_text().replace('# NIR plan status','# NIU plan status').replace('NIR_PHYSICAL.md','NIU_PHYSICAL.md')
 plan=plan.replace('latest NIK census','NIK census / NIO support').replace('NIO in flight.','NIO support replayed; no production closure.').replace('NIO is in flight and receives no credit here.','NIO supports model/library/counter windows; zero full owners and four actual sites OPEN.').replace('NIQ pair/finish','NIT pair/finish support').replace('NIM canonical forest, NIJ entry adapter owner','NIM canonical forest plus NIS entry adapters').replace('NIH op9','NIH op9 OPEN; twenty terminal candidates admitted')
 plan+='''

## Ledger13 changes and status lines

Gated25 rows: NIS5 + NIH20;407 CLOSED/192 OPEN becomes432 CLOSED/167 OPEN,0 QUALIFIED,599 total. NIH TX1:147 is corrected import only; NIR row stays unchanged. NIT pair/finish, NIL TX2 native slots and NIO borrow support replay without parent promotion. TX1:137/136/op9, TX2:065/129/115, stage1/stage2 and production Pool remain OPEN. SameLaw recognition discharges no security obligation.

K086 RETAINED: infallible shared data_is_empty with a live exclusive guard may panic on the stated valid Rust prestate. This is a liveness/abort finding, not accepted-spend soundness evidence. Production reachability or exclusion remains UNPROVED. NIO's353-event conservative MIR census,21 accessor sites and13 owners do not establish a deployed path. No abort-prefix assumption erases K086.

Owner(aj)(a) PENDING, Pool-inside-game settlement recommendation unchanged; no alternate reporting boundary adopted. (aj)(b) is moot under(ao). NIN-R2/NGP-R2 WITHDRAWN unused exporter candidates; RuntimeCpiReadonlyEntry7 PENDING/unused.

Lead-added this cycle: RuntimeEntrypointAdmission-Pool, ADDED-LEAD-20261107, inventory design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md:45, seven initial-entry fields verbatim, no CPI frame/success. The previous cycle rows in the table above remain. Existing RuntimeReturnData covers nonempty1..1024 bytes; RuntimeMemcmp, RuntimeClockSlotBinding, RuntimeReturnDataClear and RuntimePersistence retain their scopes. NIU adds/removes/changes no trust row. P6/D188 option-A native semantic transport and the two reviewed-transcription entries are reported as reclassification, never premise removal.

Physical distances after admission: (b)36/53 CLOSED,17 OPEN; (c)396/546 CLOSED,150 OPEN. Production(d) has no complete finite numbered inventory; named statuses are explicit in NIU_PHYSICAL. L187 cold release replay and L188 final native extraction/release audit remain. Frozen3, L154,100-bit PER-ATTEMPT soundness/privacy/two transactions unchanged. Target not yet established.
'''
 (E/'NIU_PLAN_STATUS.md').write_text(plan)
 remaining='''# NIU remaining obligations

Target not yet established.40/40 Lean/link/audit scopes used;0 Kani and0 extraction authorized or run. This is not an early stop. The full combined gate admits exactly25 candidates and no other row. No further independent candidate or Lean-only obligation in this ledger-refresh job is unattempted. No unchanged timeout/memory-killed job was rerun; none occurred.

All original complete statements and qualifications are retained in NIU_LEDGER.json.xz. The table names every remaining verifier occurrence. Missing native/caller producers are not replaced by conditional model theorems; this job has zero native budget. Exact upstream source interfaces are inherited from each row's complete obligation, not inferred from this abbreviated inventory.

| Exact row | Function | Remaining member obligation |
|---|---|---|
'''
 byfun={r['function']:r for r in rows}
 for r in rows:
  if r['status']!='OPEN':continue
  deps=[d for d in r['canonical_callees']if d in byfun and byfun[d]['status']=='OPEN']
  reason=('OPEN actual callees: '+', '.join(deps)+'. Then SAME-input native parent Result/effect/frame and caller-domain composition.')if deps else'Complete actual-source native/caller packet and SAME Result/effect/frame/cleanup association to the adopted row; CLOSED callees alone do not supply it.'
  remaining+=f"| {r['row']} | {r['function']} | {reason} |\n"
 remaining+='''
## Named production and release members

TX1 verify_observed137/finish136/op9: NIH terminal children now admitted, but the full actual driver extraction/native cuts, exact frame provenance and complete Result equation remain. Corrected decoder147 is imported, never extra credit.

TX2 native065: NIL retained resume-prefix/tail decomposition and local Merkle facets do not supply complete resume18/Merkle5/canonical7/7/64/query6 source packet. TX1 canonical_scan084 remains an OPEN boundary producer.

TX2 pair129/finish115: NIT model witness/frame/induction chains and ten reviewed typed cuts replay, but actual parent native log stream to SAME witnesses and finish child binding remain unproved. No endpoint-success premise adopted.

Entry/adapters: NIS decode-v2/error/active-at candidates admitted. Snapshot/SDK/native forwarding, auth/stage wrappers and instruction entries still require full reached input/Result/cleanup packets; NIS local source/carrier work is support only. Entry(d) admission and identity remain the actual headline hypotheses under(ao), not an external observer exporter.

Pool: NIB-P1(register/SAME invocation),P2(validation dictionary),P3(lane dictionary),P4(production settlement/mutation/borrow/cleanup),POOL.prefix_to_cpi and production read_to_settlement remain OPEN. Each of the four actual held CPI/callback sites and13 exclusive-guard owners is named separately in NIU_PHYSICAL.md, all OPEN. They need original-source/callee/domain and physical-cell/counter/cleanup packets, exact deployed R/callback instantiations and token-program/meta/payload/CPI frames. RuntimeEntrypointAdmission-Pool supplies only initial seven-field geometry. No RuntimeCpiReadonlyEntry7. K086 production reachability/exclusion remains unproved.

Owner(aj)(a) reporting boundary PENDING. Extraction P6/D188 retained, L154 unchanged parameter; L187 cold release replay and L188 final native/source-to-artifact audit remain. No new security assumption or metric change. Next concrete deliverables: the named source producer packets in their existing jobs, then a new all-slices gate; an authoritative production-Pool inventory is also required for a numerical(d) distance.
'''
 (E/'NIU_REMAINING.md').write_text(remaining)
 out=dict(b={k:collections.Counter(r['status']for r in v)for k,v in groups.items()},Pool=dict(NIB_P1='OPEN',NIB_P2='OPEN',NIB_P3='OPEN',NIB_P4='OPEN',prefix_to_cpi='OPEN',held_sites=4,held_sites_closed=0,exclusive_owners=owners,exclusive_owners_closed=0),finite_production_Pool_distance_available=False)
 (E/'NIU_PHYSICAL.json').write_text(json.dumps(out,indent=1)+'\n')

 (E/'NIU_HANDOFF.md').write_text(f"""# NIU ledger13 and sixth all-slices composition handoff

**Target not yet established. Conditional full gate PASS:432 CLOSED /0 QUALIFIED /167 OPEN of599.** Branch codex/cx-ledger13-20261107; local stage commits, no push. Only NIU-prefixed evidence/modules authored. No shipped source, existing proof, trust inventory, sibling/session-A worktree, account, key or funds operation.

## Exact admission

25 newly composed occurrences: NIS5 (TX2:202, TX1:NGB001, TX2:211,194,196) and NIH20 (TX1:210,211,212,213,221,222,226,264,309,311,312,313,314,315,316,317,318,319,320,325). NIH's corrected TX1:147 is unchanged CLOSED import evidence, zero new credit. No candidate was already CLOSED in NIR. NIT pair/finish, NIL native slots and NIO borrow support load, with zero parent promotion.

NIU_CANDIDATE_REVIEW preserves complete kernel statements, canonical owners and every original obligation clause. NIU_NDT_COMPARISON checks the24 original NDT rows: frozen bodies and all named/inventory/caller clauses unchanged through NIR; TX1:NGB001 uses its later authoritative NIR obligation. NIU_CALL_DOMAIN_CHECK records every candidate callee, CLOSED basis or co-candidate packet and caller derivation. Read-only NIS/NIH validators and NIS import-only retarget check pass.799 inherited row-root owners and complete statement hashes match exactly. No clause or runtime qualification is silently removed.

## Combined gate

NIU_L001 imports NIR+NIS+NIH+NIT+NIL+NIO with AspisR1.RPx_Deployed.deployed. L003 inventories all8182 roots. NFX L008 exits0 on15082 modules,712373 declarations,25327019 references, zero dangling references/incompatible owners/import mismatches;1810 compatible cached replicas disclosed. Raw ax2 covers every one of8182 roots exactly once with standard axioms only. The eight fixtures reproduce exact NIR results in the SAME optimized proof binary. Walker source/object and native C inputs match the canonical predecessor; full driver diffs retained. NIU_AUDIT/SCAN and per-scope receipts are authoritative.

The NHC_DecodeModel.decoder_error standard-raw/empty-summary discrepancy remains under(ab')(3); its actual nonzero audit exit is preserved. L002 retains the missing own root-manifest upload error, repaired before L003. No timeout, memory kill, cap/timeout increase, dropped root or unchanged failed-shape prover replay.

## Physical and plan status

Under(ao)(3), entry/adapters(b):36/53 CLOSED,17 OPEN; native callee forest(c):396/546 CLOSED,150 OPEN. These are owner/graph distances, not runtime/ELF identity. Production Pool(d) has no complete finite numbered inventory: NIB-P1..P4,POOL.prefix_to_cpi, production settlement, all four held CPI/callback sites and13 exclusive-guard owners are named OPEN in NIU_PHYSICAL. Three inherited Pool helper rows remain CLOSED; helper count is not production closure.

K086 remains a liveness/abort finding, production reachability/exclusion unproved. Owner(aj)(a) PENDING. RuntimeEntrypointAdmission-Pool was ADDED-LEAD-20261107 under(ap), existing inventory design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md:45; same seven initial-entry fields, no CPI frame or success. NIU changes no trust row. Previous lead additions are listed in NIU_PLAN_STATUS. RuntimeCpiReadonlyEntry7 PENDING/unused. External exporter predicates stay retired, NIN-R2/NGP-R2 withdrawn. SameLaw recognition discharges no security obligation.

## Resources and restore

40/40 serial scopes:5 Lean (one own-input failure),2 optimized links,33 audits including final pin/export;0 Kani/extraction. All admissions exit0 AND allowed:true;6G high/8G max/swap0/tasks64; Lean-M7000.16G exception unused. Wall sum{resources['wall_seconds']:.6f}s, peakRSS{resources['peak_rss_kib']}KiB, swaps{resources['swaps']}. Exact target/argv/revision/source/dependency/Aeneas pins and printed axioms are retained per receipt. All required8K roots are audited; no new security theorem or premise removal is claimed.

Seed160 files/477821288 bytes copied and hash-checked, NIR retained export first. Most seed bytes are NIO's retained audit binaries; no second corpus/workspace copy. Own CARGO_TARGET_DIR=/home/dombarker/project-offloads/codex-cx-ledger13-20261107/NIU_target, recorded in every receipt; no Cargo run. NIU_L040 pins every selected owner/sidecar and verifies all predecessor hashes, then retains own export under codex-cx-ledger8-cache-20261104/NIU_20261107/NIU_exports_20261107. Prepend that export to NIU_PATHS.json for restoration. Cleanup preserves caches/sources/receipts and removes only verified own rebuildable scratch; NIU_HOST_END records it.

Frozen research crates/programs/Cargo.lock remain byte-identical to4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. No ELF rebuild trigger; default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4, devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299, Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 are inherited only.

Retained: frozen3, L154 parameter, narrowed D188/P6 option-A semantic transport reclassification, SDK/Std/allocator/runtime and source-to-ELF qualifications,100-bit PER-ATTEMPT soundness/privacy/two transactions. Discharged headline hypotheses:none. Native entry/op9/TX2/pair/production Pool association, owner(aj)(a),L187 cold release replay and L188 final audit remain. NIU_REMAINING names all167 OPEN occurrences and named production obligations; next deliverables are their exact source producer packets and a production-Pool inventory. **Target not yet established.**
""")
