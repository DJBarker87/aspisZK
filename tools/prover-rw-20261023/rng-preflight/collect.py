from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[3]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/rng-preflight';E.mkdir(exist_ok=True)
H='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023'
patterns=['11289*','1129*','1130[0-5]*','out-11289*','out-1129*','out-1130[0-5]*','time-11289*','time-1129*','time-1130[0-5]*','sha-11289*','sha-1129*','sha-1130[0-5]*']
subprocess.run(['rsync','-a',*[f'--include={p}' for p in patterns],'--exclude=*',f'dombarker@100.108.41.90:{H}/stage3/',str(E)+'/'],check=True)
for attempt in ['rng-extract-001','rng-extract-002','rng-aeneas-001','rng-runtime-001','rng-kani-001','rng-kani-002']:
 (E/attempt).mkdir(exist_ok=True)
 subprocess.run(['rsync','-a','--exclude=inputs',f'dombarker@100.108.41.90:{H}/src/receipts/{attempt}/',str(E/attempt)+'/'],check=True)
for rel in ['env/J.json']:
 subprocess.run(['scp',f'dombarker@100.108.41.90:/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/{rel}',str(E/'env-J.json')],check=True,capture_output=True)
subprocess.run(['scp',f'dombarker@100.108.41.90:/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',str(E/'run2.py.txt')],check=True,capture_output=True)
rows=[];env=json.loads((E/'env-J.json').read_text());J='/home/dombarker/project-offloads/aspis-joint-20261019'
for p in sorted(E.glob('*-receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];log=(E/f'out-{a}.log').read_text()
 assert 11289<=a<=11305
 r['effective_lean_command']=[env['LEAN'],'-j1','-M7000','-DElab.async=false','-R',J+'/sources','-o',J+'/objects/'+r['module']+'.olean',r['source_path']]
 r['effective_lean_path']=J+'/objects:'+env['LEAN_PATH']
 r['accepted']=r['exit_status']==0 and 'sorryAx' not in log
 rows.append(r)
summary={'schema':'prover-rw-rng-preflight-evidence-v1','base_revision':'71100fccbd960c13cc43ba03fd4aacf39e510b34','actual_lean_launches':len(rows),'lean_used':84+len(rows),'lean_remaining':16-len(rows),'kani_new_launches':2,'kani_used':44,'kani_remaining':16,'unlaunched_ids':[{'id':11292,'reason':'missing Nonzero dependency object; failed before input receipt/launcher'}],'lean_rows':rows,'source_assessment':'Prototype derived from actual H5-aligned local entropy source; no crates/programs modifications. Host native tree is historical and is not asserted H5 coherent. host-run source_revision.txt is a historical workspace label, not identity of this prototype: use exact source_sha256, source-map.json, iteration-binding.json, adaptation.json and local commits. All old artifact/runtime evidence remains historical; no new native identity or whole-prover validation.','artifact_gates':'Not triggered: no native source change. Current required pins f8c0/63ad/121f remain targets, not newly verified.','native_scope':'No native provider or caller installed. E1 unchanged and not newly proved. No whole-owner same-event induction, E1/L1/L2 transport or candidate adoption.'}
(E/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
for p in E.rglob('*'):
 if p.is_file() and p.stat().st_size>5_000_000:raise RuntimeError(('large artifact must be hash+size only',str(p)))
print(json.dumps({k:v for k,v in summary.items() if k in ['actual_lean_launches','lean_used','lean_remaining','kani_new_launches','kani_remaining']}))
