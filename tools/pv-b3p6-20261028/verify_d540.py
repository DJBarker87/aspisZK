"""Verify the changed direct closure once, using exact receipt/source pins."""
from pathlib import Path
import json,hashlib,subprocess,re
D=Path('evidence/pv-b3p6-20261028/resume17');L=D.parent/'lean';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inv=json.loads((D/'D540-final-host-inventory.json').read_text());bad=[]
for n,h in inv['hashes'].items():
 p=D/n
 if not p.exists()or sha(p)!=h:bad.append(n)
assert not bad,bad
assert '0 loaded units listed'in inv['scopes']
assert inv['lean_attempts']==33 and inv['extraction_receipts']==20 and inv['kani_receipts']==18
rows=[]
for ident in [73828,73829,73831,73898]:
 p=D/f'lean-{ident}';r=json.loads((p/'receipt/receipt.json').read_text());assert r['exit_status']==0
 assert sha(p/'source.lean')==r['source_sha256']==sha(L/(r['module']+'.lean'))
 a=r['project_source_authority'];blob=subprocess.check_output(['git','cat-file','blob',a['blob']]);assert hashlib.sha256(blob).hexdigest()==a['sha256']==r['source_sha256']
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']==0 and r['print_axioms']
 log=(p/'receipt/stdout.log').read_text();assert 'sorryAx'not in log
 found=re.findall(r'depends on axioms: \[([^\]]*)\]',log)
 assert found and all(set(s.replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}for s in found)
 rows.append({k:r[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_sha256','lean_source_revision','print_axioms']})
refusal=json.loads((D/'lean-73830/refusal.json').read_text());assert not refusal['scope_started'];assert not (D/'lean-73830/receipt/receipt.json').exists()
t=json.loads((D/'TALLY-resume17.json').read_text());assert t['lean_attempts']==33 and t['next_unused_id']==73832 and 73830 in t['used_ids']
controls=json.loads((D/'STD-CONTROLS-D540.json').read_text());assert len(controls['checks'])==9 and all(r['passed']for r in controls['checks'])
assert controls['resolver_sha256']==sha(Path('tools/pv-b3p6-20261028/std_resolve_d540.py'))
manifest=json.loads((D/'DIRECT-MANIFEST-D537.json').read_text());manifest['modules'].pop('PV_B3P_DirectAudit17227.lean')
for name in ['PV_B3P_DirectLinks540227','PV_B3P_InclusiveGeneral540227','PV_B3P_PreweightedTotal540227','PV_B3P_DirectAudit540227']:manifest['modules'][name+'.lean']=sha(L/(name+'.lean'))
for name,h in manifest['modules'].items():assert sha(L/name)==h
manifest.update(scope='changed focused direct-body import closure only; no full release replay',entry_audit=73898,reason_for_new_audit='new total Links0/1/3, inclusive generalization and total preweighted bridge; previous audit source not rerun',source_revision='per target exact h5 receipt')
(D/'DIRECT-MANIFEST-D540.json').write_text(json.dumps(manifest,indent=2)+'\n')
x=dict(target='V244 / runjoin op227 OPEN; target not yet established',verified_new_host_files=len(inv['hashes']),hash_mismatches=bad,lean=rows,refusal=dict(id=73830,charged=False,permanently_retired=True,replacement_id=73831,cooldown='180 seconds observed; refusal UTC20:45:05; replacement launched after20:48:07'),budget=dict(charged_lean=33,remaining_lean=7,charged_extraction=20,remaining_extraction=10,charged_kani=18,remaining_kani=12,usable_unused_kani_ids=11,remaining_std=0),next=dict(lean=73832,extraction='N73927',kani='K73949',audit=73899),axioms='All five printed audit declarations use only propext/Classical.choice/Quot.sound',audit='PASS73898; changed direct-body closure; no full release replay',std='40 named instantiated blockers,23 intrinsic declaration comparisons,9 adversarial audit controls; no new native scope',key_operations=[],release_source_edits=[],premise_changes=dict(removed=[],added=[],weakened=[]))
(D/'verification-summary-D540.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k]for k in ['verified_new_host_files','hash_mismatches','budget','audit']}))
