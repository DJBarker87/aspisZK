"""Receipt-only final audit; no compiler/solver launch."""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent
lean=[json.loads(p.read_text()) for p in sorted(E.glob('LPq_L*/receipt.json'))]
kani=[json.loads(p.read_text()) for p in sorted(E.glob('LPq_K*/receipt.json'))]
assert len(lean)==80 and len(kani)==1
passings=[r for r in lean if r['exit_status']==0];rejected=[r for r in lean if r['exit_status']!=0]
allowed={'propext','Classical.choice','Quot.sound'}
for r in lean+kani:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},r['attempt']
 ad=json.loads((E/(r['attempt']+'-reservation.json')).read_text());assert ad['allowed'] is True
 for line in r['print_axioms'] if isinstance(r['print_axioms'],list) and r['exit_status']==0 else []:
  m=re.search(r'axioms: \[(.*?)\]',line)
  if m:assert set(m.group(1).split(', '))<=allowed,(r['attempt'],line)
final=lean[-1];assert final['attempt']=='LPq_L081' and final['exit_status']==0
assert len(final['print_axioms'])==79
# Latest accepted source for each current module must match the checked snapshot.
latest={}
for r in passings:
 if r.get('module','').startswith('LPq_'):latest[r['module']]=r
source_checks={}
for p in Path('lean').glob('LPq_*.lean'):
 r=latest[p.stem];s=E/r['attempt']/'sources'/'LPq_generated'/p.name
 match=p.read_bytes()==s.read_bytes();assert match,p
 source_checks[str(p)]=dict(attempt=r['attempt'],sha256=hashlib.sha256(p.read_bytes()).hexdigest(),exact_accepted_source=match)
changed=subprocess.check_output(['git','diff','--name-only','9f3da25fd77489a70d6be7c2c36a46df8d7f681c'],text=True).splitlines()
assert all(n.startswith('lean/LPq_') or n.startswith('evidence/leaf-p6-15-20261027/') for n in changed),changed
out=dict(status='OPEN: final adopted-caller ByteDomain/semantic nominal adapter not installed',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,lean_attempts=80,lean_budget=80,lean_pass=len(passings),lean_rejected=len(rejected),unchanged_dependency_compiles=35,kani_runs=1,kani_budget=30,kani_pass=1,metadata_runs=1,launcher_prelean_failure='LPq_L001_NOT_RUN.json',final_axioms_audit={k:final[k] for k in ['attempt','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']},max_lean_peak_rss_kib=max(int(r['peak_rss_kib']) for r in lean),accepted_current_sources=source_checks,lean_receipts=lean,kani_receipts=kani,source_scope_check=changed,full_frozen_manifest_replay=False,elf_rebuild_trigger=False,headline_premises_removed=0,security_target_established=False)
(E/'LPq_FINAL_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['lean_attempts','lean_pass','lean_rejected','kani_runs','max_lean_peak_rss_kib']}))
