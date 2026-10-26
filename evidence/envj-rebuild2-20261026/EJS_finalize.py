"""Final text-only collection. Run once the guarded builder has stopped."""
from pathlib import Path
import subprocess,json,hashlib,collections,re,sys
O=Path(__file__).parent
if '--reuse-collected' not in sys.argv:
 for script in ['EJS_collect.py','EJS_plan.py','EJS_integrity.py']:
  subprocess.run(['python3',str(O/script)],check=True)
rs=[json.loads(l) for l in (O/'EJS_attempts.jsonl').read_text().splitlines()];plan=json.loads((O/'EJS_resume-plan.json').read_text());integ=json.loads((O/'EJS_integrity.json').read_text());summary=json.loads((O/'EJS_summary.json').read_text())
assert len(rs)==800 and plan['next_attempt']==31600 and plan['additional_budget_remaining']==0
assert [r['attempt'] for r in rs]==list(range(30800,31600))
assert all(r['caps']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,lean_M=7000) for r in rs)
newtops=[r for r in rs if r['module']=='R1Z/EJS_Verification'];assert len(newtops)==1 and newtops[0]['validation_exit']==0
source=Path('lean/Rc2_Top.lean').read_bytes();assert source==(O/'EJS_top-before.lean.txt').read_bytes()==(O/'EJS_top-after.lean.txt').read_bytes()
latest={r['key']:r for r in rs};old_reuse=[json.loads(l) for l in (O.parent/'envj-rebuild-20261026/receipts/EJR_reuses.jsonl').read_text().splitlines()];reuses=json.loads((O/'EJS_reuses.json').read_text())
resources=[dict(attempt=r['attempt'],key=r['key'],exit=r['lean_exit'],errors=r['errors']) for r in rs if r['lean_exit'] in (124,137) or any('excessive memory' in e.lower() or 'out of memory' in e.lower() for e in r['errors'])]
report=dict(**summary,cumulative_attempts=1600,additional_budget_used=800,additional_budget_remaining=0,kani_runs=0,attempt_range=[30800,31599],additional_object_reuses=len(reuses)-len(old_reuse),latest_attempted_keys=len(latest),latest_valid_keys=sum(r['validation_exit']==0 for r in latest.values()),resource_failures=resources,original_unattempted_sources=len(plan['unattempted_sources']),profile_unattempted_sources=len(plan['profile_unattempted_sources']),source_integrity=integ,top=dict(target='AspisR1.Rc2_Top.deployed',source_sha256=hashlib.sha256(source).hexdigest(),premises_removed=0,actual_before=[82,171,0],actual_after=[82,171,0],deduplicated_before=[88,184,0],deduplicated_after=[88,184,0],delta=[0,0,0],replay='not run; static identical-source recount'),nonvacuity='Only the no-antecedent Nat successor smoke theorem; no security non-vacuity established',smoke=newtops[0],profiles=dict(provider_success_attempt=31016,formatter_joint_success_attempt=31044,formatter_union_success_attempt=31074),status='Budget exhausted. No further Lean or Kani authorized. S2 OPEN; target not yet established.')
(O/'EJS_final-report.json').write_text(json.dumps(report,indent=2)+'\n')
plan['rule']='800 additional Lean attempts exhausted. Do not run more compiles without a new budget; preserve caches/journals and source drift. Never retry timeout/memory failures unchanged.'
plan['adapter_note']='Canonical builder remains byte-identical but its mirror can overwrite valid reuse aliases; EJS adapter preserves them. Current adapter asserts limit 1600 and IDs below 31600. A future authorized continuation must update both budget and range guards explicitly; never use 35000–39999 or reserved 28000–29999.'
plan['source_integrity_mismatches']=integ['source_mismatches'];plan['object_integrity_mismatches']=integ['latest_success_object_mismatches']+integ['reused_object_mismatches'];(O/'EJS_resume-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
handoff=(O/'EJS_HANDOFF.md').read_text();handoff=handoff.split('## Final budget, integrity and resume')[0]
handoff+='''## Final budget, integrity and resume

'''
handoff+=f"**800/800 additional Lean attempts used, IDs 30800–31599; 1600 cumulative. 0 Kani. Next unused ID: 31600. No further compile is authorized.**\n\n"
handoff+=f"Compiler exit 0: {summary['compiler_passes']}; printed standard-axiom gate not rejected: {summary['validation_passes']}; peak RSS {summary['peak_rss_kib']:,} KiB; total swaps {summary['swaps']}. Resource failures: {len(resources)}. Additional object reuse records: {report['additional_object_reuses']}. These are cache measurements, not premise discharge.\n\n"
handoff+=f"Remaining original resolved source entries unattempted: {report['original_unattempted_sources']}; profile entries unattempted: {report['profile_unattempted_sources']}. EJS_resume-plan.json contains exact source SHA/blob/revision/path records, latest failures and pending dependency names; original 19 selected and 329 historical unresolved hashes are retained. Eleven additional source hashes were resolved by read-only git-blob history traversal and staged for continuation without substituting any original unresolved selection.\n\n"
handoff+=f"Integrity snapshot: {integ['source_entries_checked']} source entries; {integ['latest_success_objects_checked']} latest successful compiled object entries; {integ['reused_objects_checked']} reused object entries. Source mismatches {len(integ['source_mismatches'])}; latest-object mismatches {len(integ['latest_success_object_mismatches'])}; reuse mismatches {len(integ['reused_object_mismatches'])}. Exact paths/hashes are in EJS_integrity.json. Shared-file drift is preserved, not overwritten or adopted.\n\n"
for r in integ['source_mismatches']:handoff+=f"- Source drift `{r['path']}`: expected `{r['expected']}`, observed `{r['actual']}`.\n"
for r in integ['latest_success_object_mismatches']+integ['reused_object_mismatches']:handoff+=f"- Object drift `{r['path']}`: expected `{r['expected']}`, observed `{r['actual']}`.\n"
handoff+='\nThe canonical builder and launcher/environment/driver pins are recorded in EJS_integrity.json. All owned build work is terminal. No frozen manifest, actual-top axioms replay, SBF or release conclusion is claimed. Use the EJS adapter source/manifest selection for a future explicitly budgeted continuation; do not resume the unguarded canonical mirror behavior. Retain the four authorized recovery roots and all EJS profile objects/journals.\n'
(O/'EJS_HANDOFF.md').write_text(handoff)
print(json.dumps({k:report[k] for k in ['additional_budget_used','compiler_passes','validation_passes','next_attempt','peak_rss_kib','swaps','original_unattempted_sources','profile_unattempted_sources']}))
