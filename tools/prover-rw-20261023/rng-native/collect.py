from pathlib import Path
import subprocess,json,hashlib
D=Path(__file__).resolve().parent;R=D.parents[2]
H='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023';remote='dombarker@100.108.41.90:'
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/rng-native';E.mkdir(exist_ok=True)
subprocess.run(['rsync','-a','--exclude=*.olean',remote+H+'/rng-native/',str(E)+'/'],check=True)
listing=subprocess.check_output(['ssh',remote[:-1],f'ls -d {H}/src/receipts/rng-native-*'],text=True).splitlines()
for p in listing:subprocess.run(['rsync','-a',remote+p+'/',str(E/Path(p).name)+'/'],check=True)
subprocess.run(['rsync','-a',remote+H+'/src/reservation-rng-native-*',str(E)+'/'],check=True)
old=E.parent/'rng-caller';env=json.loads((old/'env-J.json').read_text());J='/home/dombarker/project-offloads/aspis-joint-20261019'
rows=[]
for p in sorted(E.glob('*-receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];assert 11500<=a<=11559
 r['effective_lean_command']=[env['LEAN'],'-j1','-M7000','-DElab.async=false','-R',J+'/sources','-o',J+'/objects/'+r['module']+'.olean',r['source_path']]
 r['effective_lean_path']=J+'/objects:'+env['LEAN_PATH']
 r['revision_assessment']='Parent revision plus immutable work-in-progress source and dependency hashes unless final committed audit is stated'
 p.write_text(json.dumps(r,indent=2)+'\n');rows.append(r)
(E/'ledger.json').write_text(json.dumps(dict(prior_stage3_used=100,prior_owner_caller_used=60,prior_cumulative=160,new_limit=60,new_ids=[r['attempt'] for r in rows],new_used=len(rows),cumulative_used=160+len(rows),cumulative_ceiling=220,kani_used=44,kani_limit=60,kani_new=0),indent=2)+'\n')
for p in E.rglob('*.json'):
 if p.stat().st_size>5_000_000:
  info=dict(path=p.name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
  p.with_suffix('.json.hash.txt').write_text(json.dumps(info)+'\n');p.unlink()
print('Collected',len(rows),'Lean launches')
