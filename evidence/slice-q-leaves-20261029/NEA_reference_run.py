from pathlib import Path
import subprocess,os,json,time,hashlib,re
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-slice-q-leaves-20261029'
rows=[]
for job in json.loads((E/'NEA_REFERENCE_QUEUE.json').read_text()):
 a=job['attempt'];env=dict(os.environ,NEA_REFERENCE=job['reference'],NEA_EXTRACT_CONFIG=json.dumps({'roots':job['roots'],'namespace':job['namespace']}));env.pop('NEA_ROOT',None);env.pop('NEA_RUST_CFG',None)
 r=subprocess.run(['python3',str(E/'NEA_run.py'),a,'extract',job['member']],env=env)
 if r.returncode:raise SystemExit(r.returncode)
 rc=json.loads((E/a/'receipt.json').read_text());row=dict(job,exit=rc['exit_status'])
 # One read-only transport after the submitted scope is terminal. Never resubmit a process.
 code='from pathlib import Path;import json;b=Path('+repr(B+'/NEA_extracted/'+job['namespace'])+');print(json.dumps({p.name:p.read_text() for p in b.glob("*.lean")}))'
 for retry in range(11):
  get=subprocess.run(['ssh','-o','ControlMaster=no',H,'python3 -'],input=code,capture_output=True,text=True)
  if get.returncode!=255:break
  if retry<10:time.sleep(60)
 assert get.returncode==0,get.stderr
 files=json.loads(get.stdout);row['lean_outputs']={};row['forbidden_declarations']=[]
 for n,s in files.items():
  bad=re.findall(r'^\s*(?:axiom\s+\S+|opaque\s+\S+[^\n]*$)|\bsorry\b|\badmit\b|\bnative_decide\b',s,re.M)
  dest=E/job['namespace']/n;dest.parent.mkdir(parents=True,exist_ok=True)
  if bad:
   row['forbidden_declarations']+=bad;dest=dest.with_suffix('.lean.txt')
  dest.write_text(s);row['lean_outputs'][str(dest.relative_to(E))]=hashlib.sha256(s.encode()).hexdigest()
 rows.append(row);(E/'NEA_REFERENCE_RESULTS.json').write_text(json.dumps(rows,indent=2)+'\n')
 print('REFERENCE-ONLY',json.dumps({'attempt':a,'exit':row['exit'],'member':job['member'],'lean_outputs':len(files),'adopted':False}),flush=True)
 if rc['exit_status'] in [124,137]:
  subprocess.run(['python3',str(E/'NEA_recover_sources.py')],check=True)
