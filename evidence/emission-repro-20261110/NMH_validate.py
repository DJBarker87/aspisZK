#!/usr/bin/env python3
"""Validate packet coverage and receipts without launching a compiler."""
from pathlib import Path
import json,lzma,hashlib,subprocess,collections,sys
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
def load(p):return json.loads(lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else p.read_bytes())
def main():
 provenance=load(E/'NMH_PROVENANCE.json');inv=load(E/'NMH_INVENTORY.json');plan=load(E/'NMH_PLAN.json');pinned=load(E/'NMH_INPUT_PINS.json')
 assert len(inv['blobs'])==336 and {r['blob'] for r in provenance['blobs']}=={r['blob'] for r in inv['blobs']}
 all_members=[h for g in plan['groups'] for h in g['members']];assert len(all_members)==336 and len(set(all_members))==336
 for p,v in pinned['files'].items():assert sha(Path(p).read_bytes())==v['sha256'],p
 assert sha((E/'NMH_NHR_stage.py').read_bytes())==load(E/'NMH_STAGER_PIN.json')['sha256']
 budgets=provenance['budget_used'];assert budgets['Charon']<=30 and budgets['Aeneas']<=30 and budgets['Lean']==0 and budgets['Kani']==0
 completed=[]
 for p in E.glob('NMH_E*/receipt.json'):
  r=load(p);a=r['attempt'];ad=load(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  disk=load(E/(a+'-disk-0.json'));assert disk['free']>=40_000_000_000
  if 'owned_bytes' in disk:assert disk['owned_bytes']<30_000_000_000
  pins=E/(a+'_emitted')/'NHR_PINS.json'
  if pins.exists():
   z=load(pins)
   if 'lock_after' in z:assert z['lock_after']==z['lock_before']
   if z.get('aeneas_exit')==0:
    for name,h in z['outputs'].items():
     f=E/(a+'_emitted')/name
     b=f.read_bytes() if f.exists() else lzma.decompress(f.with_name(f.name+'.xz').read_bytes());assert sha(b)==h,(a,name)
  post=p.parent/'NMH_POSTCHECK.json'
  if post.exists():assert not load(post)['source_drift']
  completed.append(a)
 for r in provenance['blobs']:
  assert r['verdict'] in ['REPRODUCED','DIFFERS','NOT_REPRODUCED']
  if r['verdict']=='REPRODUCED':
   assert r['run'] in completed
   if r['normalization'] is None:assert r['committed_hash']==r['reproduced_hash']
   else:assert r['normalized_hash']==r['committed_hash']
  if r['diff']:
   p=E/r['diff'];assert p.exists();assert sha(lzma.decompress(p.read_bytes()))==p.with_suffix('.sha256').read_text().strip()
 for p in E.rglob('*'):
  if p.is_file():assert p.stat().st_size<=20_000_000,p
 assert not list(E.rglob('__pycache__'))
 changed=subprocess.check_output(['git','diff','--name-only',inv['revision'],'--','crates','programs','Cargo.lock'],text=True);assert not changed,'shipped source changed'
 print(json.dumps(dict(status='PASS_WITH_PROVENANCE_GAPS',blobs=336,verdicts=provenance['counts'],completed_runs=len(completed),budget=budgets,ledger_unchanged=True,target_established=False)))
if __name__=='__main__':main()
