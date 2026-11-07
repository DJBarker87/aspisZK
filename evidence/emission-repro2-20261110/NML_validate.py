"""Audit coverage, scope admission, resource receipts and retained source hashes."""
from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent;O=E.parent/'emission-repro-20261110';sha=lambda b:hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def main():
 p=load(E/'NML_PROVENANCE.json');old=load(O/'NMH_PROVENANCE.json');plan=load(E/'NML_PLAN.json')
 assert len(p['blobs'])==336 and {b['blob'] for b in p['blobs']}=={b['blob'] for b in old['blobs']}
 assert p['target_established'] is False
 assert all(p['budget_used'][k]<=v for k,v in dict(Charon=40,Aeneas=40,Lean=20,Kani=0).items())
 assert sha((E/'NML_NHR_stage.py').read_bytes())==sha((E.parent/'extract-stage-20261106/NHR_stage.py').read_bytes())
 events=[json.loads(l) for l in (E/'NML_ATTEMPTS.jsonl').read_text().splitlines()]
 completed=[]
 for r in plan['runs']:
  ref=E/r['reference_directory'];assert sha((ref/r['source_relative']).read_bytes())==r['reference_sha256'];assert sha((ref/'Cargo.toml').read_bytes())==r['manifest_sha256']
  assert '--release' in r['charon_command']
  for ex in r.get('package_extras',[]):assert sha((ref/ex['relative_path']).read_bytes())==ex['sha256']
 for f in list(E.glob('NML_[ELB][0-9][0-9][0-9]/receipt.json')):
  rc=load(f);a=rc['attempt'];ad=load(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
  assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert rc['timeout']==180
  assert all(k in rc for k in ['command','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms'])
  assert any(e.get('attempt')==a and e.get('kind')=='share_check' and e['observation']['stream_a_count']<2 and e['observation']['free_bytes']>=40_000_000_000 for e in events)
  post=load(f.parent/'NML_POSTCHECK.json');assert not post['source_drift'] and post['lock_sha256']==post['expected_lock_sha256'];assert post['owned_bytes']<30_000_000_000
  for n,h in rc['source_hashes'].items():
   # Host launcher retains the exact source bytes for this attempt, even if an owned controller is later repaired.
   snap=f.parent/'sources'/n
   if snap.exists():assert sha(snap.read_bytes())==h,(a,n)
  if rc['kind']=='lean' and rc['exit_status']==0:
   assert rc['print_axioms'] and isinstance(rc['print_axioms'],list)
   for line in rc['print_axioms']:
    m=re.search(r'depends on axioms: \[(.*?)\]',line)
    assert (m is not None and set(x.strip() for x in m[1].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}) or 'does not depend on any axioms' in line,line
  completed.append(dict(attempt=a,exit=rc['exit_status'],wall_seconds=rc['wall_seconds'],peak_rss_kib=rc['peak_rss_kib'],swaps=rc['swaps'],source_revision=rc['source_revision'],print_axioms=rc['print_axioms']))
 last_refusal={}
 for e in events:
  a=e.get('attempt');obs=e.get('observation',{})
  if a=='NML_E001':continue
  if e.get('kind')=='wait' and obs.get('stream_a_count',0)>=2:last_refusal[a]=obs['time']
  elif e.get('kind')=='share_check':
   if a in last_refusal:assert obs['time']-last_refusal.pop(a)>=180,(a,'short share recheck')
 for f in E.glob('NML_E[0-9][0-9][0-9]/configuration_receipt.json'):
  rc=load(f);scope=rc['scope_attempt'];outer=load(E/scope/'receipt.json');assert rc['limits']==outer['limits'];assert rc['source_revision']==outer['source_revision'];assert outer['exit_status']==0
  assert rc['peak_rss_kib'] is not None and rc['swaps'] is not None and rc['inherited_scope_timeout']==180
  completed.append(dict(attempt=rc['attempt'],scope_attempt=scope,exit=rc['exit_status'],wall_seconds=rc['wall_seconds'],peak_rss_kib=rc['peak_rss_kib'],swaps=rc['swaps'],source_revision=rc['source_revision'],print_axioms=rc['print_axioms']))
 for b in p['blobs']:
  if b.get('run')=='NML_E001':assert b['verdict']!='REPRODUCED_FROM_ARCHIVE'
  if b['verdict']=='REPRODUCED_FROM_ARCHIVE' and b.get('input',{}).get('directory'):assert b['run'] in {r['attempt'] for r in completed}
  if b['verdict']=='DIFFERS_NONSEMANTIC':assert b['classification_evidence'].get('lean_receipt'),b['blob']
 for f in E.rglob('*'):
  if f.is_file():assert f.stat().st_size<=20_000_000,f
 assert not list(E.rglob('__pycache__'))
 base=subprocess.check_output(['git','rev-parse','1e13d368ea9^'],text=True).strip()
 names=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines();assert all(n.startswith('evidence/emission-repro2-20261110/') for n in names)
 result=dict(status='PASS_WITH_PROVENANCE_GAPS_AND_EXCLUDED_ADMISSION_FINDING' if (E/'NML_ADMISSION_FINDING.json').exists() else 'PASS_WITH_PROVENANCE_GAPS',target_established=False,coverage=336,counts=p['counts'],budget_used=p['budget_used'],completed=completed,remaining_CLOSED_impact=p['affected_CLOSED_count'],scope='No native/ledger/trust/security credit; archived-input provenance only',protected_paths_changed=[])
 (E/'NML_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['status','coverage','counts','budget_used','remaining_CLOSED_impact']}))
if __name__=='__main__':main()
