from pathlib import Path
import json,lzma,hashlib,re
E=Path(__file__).resolve().parent
attempts=[json.loads(l) for l in (E/'PCC_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(attempts)==70 and len({r['attempt'] for r in attempts})==70
retention=json.loads((E/'PCC_L070-source-retention.json').read_text());pins=json.loads((E/'PCC_L069-source-pin-summary.json').read_text());root=json.loads((E/'PCC_ROOT_MANIFEST.json').read_text())
scan=[json.loads(l) for l in lzma.decompress((E/'PCC_L068/PCC_audit_outputs/PCC_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()]
assert all(not r['dangling'] and r['imports_match'] for r in scan)
metrics={}
for name,rows in [('stage0',attempts[:7]),('stage1',attempts[7:64]),('final_support_gate',attempts[64:])]:
 metrics[name]=dict(scopes=len(rows),wall_seconds=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=sum(int(r['swaps']) for r in rows),failures=[r['attempt'] for r in rows if r['exit_status']!=0])
axioms=json.loads((E/'PCC_L065/receipt.json').read_text())['print_axioms'];texts=[str(x) for x in axioms]
by_theorem={t:next(line for line in texts if "'"+t+"'" in line) for t in root['new_theorems']}
assert not any('sorryAx' in line for line in texts)
(E/'PCC_AXIOMS.json').write_text(json.dumps(dict(new_theorems=by_theorem,combined_receipt='PCC_L065/receipt.json',raw_receipt='PCC_L067/receipt.json',raw_roots=len(root['all_roots']),standard_only=True),indent=1)+'\n')
audit=dict(status='PASS_SUPPORT_ONLY',pool_rows_closed=0,owner_row='POOL:328',owner_status='OPEN',formal_scopes=70,kani_scopes=0,extractions=0,metrics=metrics,final_import='PCC_L065',fixtures='PCC_L066',raw_ax2='PCC_L067',scan='PCC_L068',pins='PCC_L069',retention='PCC_L070',scan_modules=len(scan),scan_declarations=sum(r['declarations'] for r in scan),scan_edges=sum(r['edges'] for r in scan),dangling=0,import_mismatches=0,raw_roots=len(root['all_roots']),new_top_theorems=len(root['new_theorems']),standard_axioms=['propext','Classical.choice','Quot.sound'],closure_pins=pins,binary_same=retention['binary_identical_across_fixtures_raw_scan'],formal_release_result=False)
(E/'PCC_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
(E/'PCC_COSTS.json').write_text(json.dumps(dict(stages=metrics,per_child_native_closure_cost='UNKNOWN: no closed child example in this job',elaboration_is_not_closure=True,total_wall_seconds=sum(r['wall_seconds'] for r in attempts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in attempts),swaps=sum(int(r['swaps']) for r in attempts)),indent=1)+'\n')
summary='; '.join(f"{name}: {m['scopes']} scopes, {m['wall_seconds']:.3f}s payload wall, {m['peak_rss_kib']}KiB peak RSS" for name,m in metrics.items())
feas=f'''# PCC deposit owner feasibility

**Incomplete E1 repair; POOL:328 OPEN; zero Pool rows CLOSED. Target not yet established.** Guard-owner feasibility remains undecided.

* **E1 NOT MET.** Eleven fixed child-reference drafts now replace free reference arguments for the corresponding packets. Full SDK ProgramError, ABI projection, raw-status conversion and tag/constant-map/bind transport compile. Typed native-view, machine-word and initial-state obligations have owners. But the remaining complex/CPI packets and fixed dictionary-free PCC_Owner.spec are absent, the full owner state/trace has not integrated the ABI quotient, and the error-consumer audit is transitive-incomplete. No free Children dictionary is hidden inside a renamed structure.
* **E2 NOT MET.** No complete explicit FreshGenesis/ExistingSamePage/FreshRollover continuation chain or full Result/event/post-state fold. PCA_L050 remains retired.
* **E3 NOT MET.** Nested shared-scope/error/abort components, page windows/counters, ParentLive preservation for page writes, and lane cleanup after page-acquisition Err compile. Cell-ledger validity is explicitly distinguished from all-parent-guards-live. The global fold, every child schedule and CPI SDK/counter/header frames remain unproved.
* **E4 NOT MET.** Neither CPI bridge/control exists. RuntimeCpiAccountView is transcribed with clause1 on metas; token/system semantics and readonly-entry are never assumed. Raw status conversion is modeled exactly rather than assuming identity on every u64.
* **E5 NOT MET.** No child root instantiated. Four direct class-A children remain PCB_ dependencies. PCC_CHILDREN.md lists all25 direct children plus nested357, their exact missing references/domains/association and native work.
* **E6 NOT MET.** No actual-parent native cuts or association to the transcription.
* **E7 MET for SUPPORT only.** Final headline/ledger23/PCA/PCC import, all183 raw roots,66 new top-theorem audits, eight fixtures on the SAME binary and NFX-style scan of17112 modules pass.33705 selected object/sidecar hashes include resolved Aeneas objects;277 predecessor pins and45 support objects remain unchanged. This closes no native or Pool row.

Measured cost: {summary}. Swaps0 throughout. All70/70 formal scopes used;0/60 Kani and0/0 extraction. Admission refusals were waited out; every actual launch had exit0 AND allowed:true and host free>=40GB. Caps6G/8G/swap0/tasks64; Lean-M7000. No timeout, memory kill, cap increase or retired unchanged rerun. Owned elaboration/input errors and their repairs are retained.

Per-child remaining closure cost is UNKNOWN for every child here. There is no new CLOSED child example from which to derive native/owner cost; small reference elaboration times are not such examples. No estimate is extrapolated from compiler/setup failures. NLF support is reused within its domain, not promoted to a parent certificate.

The full formal allowance was consumed during E1/support work and the required gates. Every unspent native member is blocked by the binding E1-before-native and compiled-full-fold prerequisites; PCC_REMAINING.md lists each source member and its further missing facts. Unused Kani allowance is not called exhaustion or evidence of impossibility.

**Verdict:** local functional-reference and small loan/window proofs are feasible under the caps; the complete guard-owner class is not established tractable or intractable. The next deliverable is the missing fixed packets/owner state/spec and transitive error audit, then three explicit mode folds. The100-bit PER-ATTEMPT, privacy and two-transaction targets and frozen release remain unchanged. No shipped edit or ELF rebuild trigger; pins inherited, not reproduced.
'''
assert len(feas.split())<800
(E/'PCC_FEASIBILITY.md').write_text(feas)
p=E/'PCC_HANDOFF.md';s=p.read_text().replace('Budget currently64/70 formal scopes','Budget70/70 formal scopes').replace('E7 stage0 MET for intermediates; final support closure gate pending.','E7 MET for SUPPORT only: final import L065,183 raw roots/66 new theorem audits L067,eight same-binary fixtures L066,NFX-style scan17112 modules L068,and33705 object/sidecar pins L069/retention L070 PASS. Zero Pool row roots.').replace('No timeout/memory kill','No timeout/memory kill');s+='\nFinal metrics and #print axioms: PCC_AUDIT.json,PCC_COSTS.json,PCC_AXIOMS.json and all per-attempt receipts. Final source revision e127ae91579 plus exact dirty source hashes; the final evidence commit contains those bytes. Digest/error slots are op43/op44 in the replayed coherent cohort; op38 remains quantified. Source/gate details are in PCC_CORRESPONDENCE.md.\n';p.write_text(s)
p=E/'PCC_REMAINING.md';s=p.read_text();s+='\nFinal stop accounting:70/70 formal scopes consumed;0/60 Kani and0/0 extraction. All remaining legal work before native is Lean work with no allowance left. Every remaining Kani member is listed above and in PCC_CHILDREN.md and requires the missing fixed E1/full fold first. The six final scopes audited the changed support closure and retained its evidence; they did not substitute for the missing owner proof. No claim that more budget cannot help.\n';p.write_text(s)
(E/'PCC_COHORT.json').write_text(json.dumps(dict(headline='AspisR1.RPx_Deployed.deployed',ledger_receipt='evidence/ledger23-20261110/NLO_COMBINED_IMPORT.lean',compiled_ledger_module='NLS_COMBINED_IMPORT',digest_slot='op43',error_slot='op44',pda_slot='op38 (quantified)',L154='statement parameter',D188='narrowed; no trust removed',RuntimePersistence='TwoTransactionLaw, data only',RuntimeCpiAccountView='ADDED-LEAD-20261110; SUPPORT hypotheses only',RuntimeCpiReadonlyEntry7='PENDING_UNUSED',rows_closed=0),indent=1)+'\n')
(E/'PCC_CLIENT_REPAIRS.md').write_text('''# Owned client changes

Copied/adapted the pilot's owned client for PCC attempt ids,70/60 budgets, ledger23 canonical path order and isolated PCC object/source/tmp directories. Shared reservation/launcher/shim/workspaces are unchanged. Lean declaration timeout60s; audit/inspection timeout180s, no timeout increase or timed-out declaration rerun. Failed elaborations were repaired at the source, never by raising caps. The final audit client additionally pins PCC_COMBINED_IMPORT.olean, strengthening dependency validation. Final binary outputs are isolated under PCC_final_audits/<attempt>; the SAME existing binary is used, and input manifests copied byte-for-byte. Standard walker output filenames are inside that PCC-owned directory. No PCA_ source/object is changed; L069 checks277 initial predecessor pins. No tool infrastructure was built or repaired. PCC_VALIDATION_REPAIR.md records the exact implicit-Init manifest correction.
''')
print(f"Report generated:70 formal scopes,0 Kani,183 raw roots,17112 scan modules,zero Pool promotions; feasibility {len(feas.split())} words")
