"""Assemble exact receipts and row residuals after the two reserved audits."""
from pathlib import Path
import json,re,hashlib,subprocess
D=Path(__file__).resolve().parent
T=json.loads((D/'TALLY-d336.json').read_text());records=[]
standard={'propext','Classical.choice','Quot.sound'}
for a in T['used_ids']:
 R=D/'receipts'/f'lean-{a}';p=R/'receipt/receipt.json'
 if not p.is_file():
  assert (R/'refusal.json').exists() or (R/'cooldown-refusal.json').exists() or (R/'barrier.json').exists(),a
  records.append(dict(attempt=a,charged=False,source_snapshot_sha256=hashlib.sha256((R/'source.lean').read_bytes()).hexdigest()))
  continue
 r=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()+(p.parent/'stderr.log').read_text();reports=[]
 for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log):reports.append(dict(declaration=m[1],axioms=[v.strip()for v in m[2].split(',')if v.strip()]))
 for m in re.finditer(r"'([^']+)' does not depend on any axioms",log):reports.append(dict(declaration=m[1],axioms=[]))
 bad=sorted({x for rep in reports for x in rep['axioms'] if x not in standard})
 r.update(complete_axiom_reports=reports,nonstandard_axioms=bad,charged=True,credited=r['exit_status']==0 and not bad)
 assert r['source_sha256']==hashlib.sha256((R/'source.lean').read_bytes()).hexdigest(),a
 assert r['swaps']==0,a
 if r['exit_status']==0:assert not bad,(a,bad)
 records.append(r)
charged=[r for r in records if r['charged']];assert len(charged)==T['lean_attempts']
accepted=[r for r in charged if r['credited']]
required=['PV_B3_Close134','PV_B3_Install222','PV_B3_Install117','PV_B3_Install121','PV_B3_AuditD336','PV_B3_FlatInstallD336','PV_B3_ClosureD336']
latest={m:next(r for r in reversed(accepted)if r['module']==m)for m in required}
assert latest['PV_B3_AuditD336']['attempt']==40597
assert latest['PV_B3_ClosureD336']['attempt']in [40598,40599]
cache=json.loads((D/'d336-cache-verification.json').read_text());assert cache['mismatches']==[]
index=dict(entry_revision='678657d1e6334f1a4e4c327382ad4fb516751588',charged_lean_attempts=len(charged),accepted=len(accepted),rejected=len(charged)-len(accepted),kani=0,ids_used=T['used_ids'],remaining_lean_budget=100-len(charged),records=records,closing_receipts={m:{k:r[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_sha256','lean_source_revision']}for m,r in latest.items()},max_lean_rss_kib=max(r['peak_rss_kib']for r in charged),source_or_runtime_change_under_crates_programs=False)
(D/'d336-receipt-index.json').write_text(json.dumps(index,indent=1)+'\n')
old=json.loads((D/'d324-row-status.json').read_text());rows=[];ops={230:134,239:222,217:117,220:121};theorems={134:'PV_B3_Close134.source',222:'PV_B3_Install222.source',117:'PV_B3_Install117.source',121:'PV_B3_Install121.source'}
for row in old['rows']:
 v=int(row['id'][1:]);r=dict(row)
 if v in ops:
  op=ops[v];r['before']=row['after'];r['after']=dict(classification='P source obligation discharged on selected instance',status='CLOSED source/callback',statement='The selected original ProverRwFull field obeys its exact complete-Result copy/reference law for every original raw input, with no source-law or canonical-input hypothesis.',residual_fields=[],closing_theorem=theorems[op],native_link_evidence_class='script-checked structural argument under ruling (k), with complete-Result extraction proved in Lean; not a native machine theorem',finite_native_validation='d336-native-reuse.json',retained=['actual native execution/RunJoin dictionary installation','D234/V403 and any further mathematical interpretation','deployment E1/E2, client proof-account path, L1/L2/L3 side channels'])
 rows.append(r)
status=dict(source_callback_rows_closed=4,source_callback_rows=['V230','V239','V217','V220'],endpoint_premises_removed=[],premises_added=[],premises_weakened=[],T=['entropy_law','entropy_kernel','observation'],native_link_class='structural argument, never promoted to machine proof; runtime comparisons are finite validation',combined_dictionary='PV_B3_ClosureD336.installed',other_callbacks_preserved=258,target='not yet established',rows=rows)
(D/'d336-row-status.json').write_text(json.dumps(status,indent=2)+'\n')
log=subprocess.check_output(['git','log','--oneline','678657d1e6..HEAD']).decode();(D/'COMMIT-LOG-D336.txt').write_text(log)
print(json.dumps(dict(charged=len(charged),accepted=len(accepted),rejected=len(charged)-len(accepted),source_rows_closed=4,endpoint_premises_removed=0,peak_rss_kib=index['max_lean_rss_kib'])))
