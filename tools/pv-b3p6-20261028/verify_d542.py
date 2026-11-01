"""Validate fresh receipts, pins, standard axioms, resource caps and budget."""
from pathlib import Path
import json,hashlib,re,subprocess
D=Path('evidence/pv-b3p6-20261028/resume17');L=D.parent/'lean';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inv=json.loads((D/'D542-final-host-inventory.json').read_text());bad=[]
for name,h in inv['hashes'].items():
 p=D/name.removeprefix('resume17/')
 if not p.exists()or sha(p)!=h:bad.append(name)
assert not bad,bad
assert '0 loaded units listed'in inv['scopes'];assert inv['extraction_receipts']==20 and inv['kani_receipts']==20
lean=[]
for p in sorted(D.glob('lean-738*/receipt/receipt.json')):
 r=json.loads(p.read_text());ident=r['attempt']
 if ident<73832 or ident in [73897,73898]:continue
 assert r['source_sha256']==sha(p.parent.parent/'source.lean')
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']==0
 a=r['project_source_authority'];b=subprocess.check_output(['git','cat-file','blob',a['blob']]);assert hashlib.sha256(b).hexdigest()==a['sha256']==r['source_sha256']
 if r['exit_status']==0:
  log=(p.parent/'stdout.log').read_text();assert 'sorryAx'not in log
  ax=re.findall(r'depends on axioms: \[([^\]]*)\]',log)
  assert (ax or 'does not depend on any axioms' in log) and all(set(s.replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}for s in ax)
  assert sha(L/(r['module']+'.lean'))==r['source_sha256']
 lean.append({k:r[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','lean_source_revision','source_sha256','print_axioms']})
assert any(r['attempt']==73899 and r['exit_status']==0 for r in lean)
kani=[]
for ident in [73949,73950]:
 p=D/f'K{ident}/receipt/receipt.json';r=json.loads(p.read_text());assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 log=(p.parent/'stdout.log').read_text()
 if ident==73949:assert r['exit_status']!=0 and 'VERIFICATION:- FAILED'in log
 if ident==73950 and r['exit_status']==0:assert 'VERIFICATION:- SUCCESSFUL'in log
 kani.append(dict(id='K'+str(ident),**{k:r[k]for k in ['exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']}))
t=json.loads((D/'TALLY-resume17.json').read_text());assert t['lean_attempts']==inv['lean_attempts'];assert len(lean)==t['lean_attempts']-33
struct=json.loads((D/'STD-STRUCTURAL-D542.json').read_text());assert len(struct['items'])==23 and not struct['unargued_ordinary_items']
manifest=json.loads((D/'DIRECT-MANIFEST-D540.json').read_text());manifest['modules'].pop('PV_B3P_DirectAudit540227.lean',None)
for r in lean:
 if r['exit_status']==0:manifest['modules'][r['module']+'.lean']=r['source_sha256']
for n,h in manifest['modules'].items():assert sha(L/n)==h
manifest.update(scope='One changed focused direct-mask and sum import-closure audit; not a full endpoint release replay',entry_audit=73899,source_revision='per-module h5 source receipts',reason_for_new_audit='new mask source wrappers, universal intrinsic specifications and direct mask bridge; sum structural source binding checked separately')
(D/'DIRECT-MANIFEST-D542.json').write_text(json.dumps(manifest,indent=2)+'\n')
out=dict(target='V244 / runjoin op227 OPEN; target not yet established',verified_host_artifacts=len(inv['hashes']),hash_mismatches=bad,lean=lean,kani=kani,budget=dict(charged_lean=t['lean_attempts'],remaining_lean=40-t['lean_attempts'],charged_extraction=20,remaining_extraction=10,charged_kani=20,remaining_kani=10,usable_unused_kani_ids=9,unused_structural_native_scopes=4),next=dict(lean=t['next_unused_id'],audit_ids=[],extraction='N73927 (or documented lower holes after fresh collision scan)',kani='K73951-K73959'),std='23/23 ordinary instantiated blockers structurally argued; five local gates released with k-triple-prime label; no V370 claim discharged',local_body_associations=dict(total=36,bound=6,outstanding=30,direct=4,P6=1,structural=1),premise_changes=dict(removed=[],added=[],weakened=[]),axioms='Only propext, Classical.choice, Quot.sound in successful printed declarations',full_release_replay='Not run: endpoint and whole source-cone obligations remain',resources='One scope at a time;6G/8G/swap0/Tasks64; Lean -M7000; optimized Kani; no cap increases')
(D/'verification-summary-D542.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k]for k in ['verified_host_artifacts','budget','local_body_associations']}))
