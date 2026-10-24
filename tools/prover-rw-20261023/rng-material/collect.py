"""Collect only this continuation and preserve the cumulative allocation."""
from pathlib import Path
import subprocess,json,hashlib
D=Path(__file__).resolve().parent;R=D.parents[2]
H='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023';remote='dombarker@100.108.41.90:'
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/rng-material';E.mkdir(exist_ok=True)
subprocess.run(['rsync','-a','--exclude=*.olean',remote+H+'/rng-material/',str(E)+'/'],check=True)
listing=subprocess.check_output(['ssh',remote[:-1],f'ls -d {H}/src/receipts/rng-material-*'],text=True).splitlines()
for p in listing:subprocess.run(['rsync','-a',remote+p+'/',str(E/Path(p).name)+'/'],check=True)
subprocess.run(['rsync','-a',remote+H+'/src/reservation-rng-material-*',str(E)+'/'],check=True)
env=json.loads((E.parent/'rng-caller/env-J.json').read_text());J='/home/dombarker/project-offloads/aspis-joint-20261019'
rows=[]
for p in sorted(E.glob('*-receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];assert 11524<=a<=11559
 r['effective_lean_command']=[env['LEAN'],'-j1','-M7000','-DElab.async=false','-R',J+'/sources','-o',J+'/objects/'+r['module']+'.olean',r['source_path']]
 r['effective_lean_path']=J+'/objects:'+env['LEAN_PATH']
 r['revision_assessment']='Continuation parent revision plus immutable WIP source/dependency hashes; source emission uses predecessor private host tree assessed by exact span checks'
 p.write_text(json.dumps(r,indent=2)+'\n');rows.append(r)
prior=json.loads((E.parent/'rng-native/ledger.json').read_text());assert prior['new_used']==24
(E/'ledger.json').write_text(json.dumps(dict(prior_ledger_sha256=hashlib.sha256((E.parent/'rng-native/ledger.json').read_bytes()).hexdigest(),prior_cumulative=184,remaining_at_start=36,continuation_ids=[r['attempt'] for r in rows],continuation_used=len(rows),native_allocation_used=24+len(rows),cumulative_used=184+len(rows),cumulative_ceiling=220,remaining=36-len(rows),kani_used=44,kani_limit=60,kani_remaining=16),indent=2)+'\n')
for p in E.rglob('*.json'):
 if p.stat().st_size>5_000_000:
  p.with_suffix('.json.hash.txt').write_text(json.dumps(dict(path=p.name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))+'\n');p.unlink()
print('Collected',len(rows),'continuation Lean launches')
