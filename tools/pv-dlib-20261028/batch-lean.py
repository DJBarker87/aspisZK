"""Sequential focused predecessors inside one unchanged capped scope.
Each compiler has a distinct Env-J ID and a full receipt; first error stops.
A refused admission consumes only the first unused ID, and starts no compiler.
"""
from pathlib import Path
from cooldown import check_ready,refuse
import subprocess,json,hashlib,re,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028'
D='/home/dombarker/project-offloads/codex-pv-dlib-20261028';H='dombarker@100.108.41.90'
G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
check_ready();modules=sys.argv[1:];assert modules
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();t=json.loads((E/'TALLY.json').read_text());start=max(t['used_ids'])+1
assert start+len(modules)<=43497 and len(t['lean_charged'])+len(modules)<=100
records=[]
for i,m in enumerate(modules):
 assert m.startswith('R1Z/PV_DL_') and not any(x in m for x in ['Audit','Replay'])
 p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean');s=p.read_bytes();rel=str(p.relative_to(R));assert subprocess.check_output(['git','show','HEAD:'+rel])==s
 n=start+i;meta=dict(attempt=n,module=m,source_path=rel,source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+rel],text=True).strip(),source_sha256=hashlib.sha256(s).hexdigest(),revision=head,source_revision=head,environment_generation='private pinned external overlay with same-authority IR companions',external_manifest_sha256=hashlib.sha256((E/'external-object-manifest.json').read_bytes()).hexdigest(),external_ir_manifest_sha256=hashlib.sha256((E/'external-ir-companions.json').read_bytes()).hexdigest())
 
 if i==0:(E/f'{n}-source.lean.txt').write_bytes(s)
 records.append(dict(meta=meta,path=str(p),imports=re.findall(r'^import (\S+)',s.decode(),re.M)))
t['used_ids'].append(start);(E/'TALLY.json').write_text(json.dumps(t,indent=2)+'\n')
name='lean-batch-'+str(start)
r=subprocess.run(['ssh',H,f'mkdir -p {D}/{name}; python3 {G}/reservation.py {D}/{name}/upload-admission.json > {D}/{name}/upload-reservation.log 2>&1'],capture_output=True,text=True)
a=subprocess.check_output(['ssh',H,f'cat {D}/{name}/upload-admission.json'],text=True);(E/f'{start}-upload-admission.json').write_text(a)
if r.returncode!=0 or json.loads(a).get('allowed') is not True:
 refuse('lean batch upload '+str(start),json.loads(a));sys.exit(78)
for item in records:
 subprocess.run(['scp','-q',item['path'],H+':'+D+'/lean-sources/'+item['meta']['module']+'.lean'],check=True)
old=[]
for n in t['lean_charged']:
 p=E/f'{n}-submission.json'
 if p.exists():old.append(json.loads(p.read_text()))
code=r'''from pathlib import Path
import json,hashlib,subprocess,re,sys
b=Path(DIR);env=json.loads((b/'env-J.json').read_text());roots=[Path(x) for x in env['LEAN_PATH'].split(':')]
for item in RECORDS:
 j=item['meta'];n=j['attempt'];m=j['module'];d=b/('lean-'+str(n));d.mkdir(exist_ok=True)
 p=b/'lean-sources'/(m+'.lean');assert hashlib.sha256(p.read_bytes()).hexdigest()==j['source_sha256']
 deps={}
 for dep in item['imports']:
  q=next((r/(dep.replace('.','/')+'.olean') for r in roots if (r/(dep.replace('.','/')+'.olean')).exists()),None)
  assert q is not None,('missing',dep)
  deps[dep]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest())
 j['imports']=deps;j['deps_fingerprint']=hashlib.sha256(json.dumps(deps).encode()).hexdigest()
 assert not any(o.get('source_sha256')==j['source_sha256'] and o.get('imports')==deps and o.get('environment_generation')==j['environment_generation'] for o in OLD),('unchanged charged candidate',m)
 (d/'submission.json').write_text(json.dumps(j,indent=2)+'\n')
 cmd=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',str(b/'env-J.json'),str(b/'lean-objects'),str(b/'lean-sources'),str(b/'lean-objects'/(m+'.olean')),str(p),'7000']
 with (d/'output.log').open('w') as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(d/'time.log'),*cmd],stdout=out,stderr=subprocess.STDOUT)
 timing=(d/'time.log').read_text();log=(d/'output.log').read_text()
 def field(pattern):
  match=re.search(pattern,timing);return match.group(1).strip() if match else None
 j.update(target=cmd,exit=r.returncode,wall=field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.*)'),peak_rss_kib=field(r'Maximum resident set size \(kbytes\): (.*)'),swap=field(r'Swaps: (.*)'),print_axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log,re.S),limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),expected_phase='sequential focused Lean predecessor; stop on first error',enclosing_scope=NAME)
 (d/'receipt.json').write_text(json.dumps(j,indent=2)+'\n');print(n,m,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
'''.replace('DIR',repr(D)).replace('RECORDS',repr(records)).replace('OLD',repr(old)).replace('NAME',repr(name))
# Use real newlines in files written by the host driver.
p=E/(name+'-runner.py');p.write_text(code)
subprocess.run(['scp','-q',str(p),H+':'+D+'/'+name+'/runner.py'],check=True)
r=subprocess.run([sys.executable,str(R/'tools/pv-dlib-20261028/scope.py'),name,'sequential focused Lean compiles; separate IDs and per-file receipts','python3',D+'/'+name+'/runner.py'])
# Recover every submitted target read-only even on a compiler error; never rerun it to fetch evidence.
fetch='''from pathlib import Path
import json
b=Path(DIR);out={}
for n in IDS:
 d=b/('lean-'+str(n))
 if (d/'receipt.json').exists():out[str(n)]={f:(d/f).read_text() for f in ['receipt.json','submission.json','output.log','time.log']}
print(json.dumps(out))
'''.replace('DIR',repr(D)).replace('IDS',repr([x['meta']['attempt'] for x in records]))
f=subprocess.run(['ssh',H,'python3','-'],input=fetch,text=True,capture_output=True);assert f.returncode==0,f.stderr
collected=json.loads(f.stdout);t=json.loads((E/'TALLY.json').read_text())
for n,files in collected.items():
 d=E/('lean-'+n);d.mkdir(exist_ok=True)
 for file,content in files.items():(d/file).write_text(content)
 (E/(n+'-submission.json')).write_text(files['submission.json'])
 j=json.loads(files['submission.json']);source=subprocess.check_output(['git','show',j['revision']+':'+j['source_path']]);assert hashlib.sha256(source).hexdigest()==j['source_sha256'];(E/(n+'-source.lean.txt')).write_bytes(source)
 if int(n) not in t['used_ids']:t['used_ids'].append(int(n))
 if int(n) not in t['lean_charged']:t['lean_charged'].append(int(n))
 print(n,json.loads(files['receipt.json'])['module'],json.loads(files['receipt.json'])['exit'],flush=True)
(E/'TALLY.json').write_text(json.dumps(t,indent=2)+'\n');sys.exit(r.returncode)
