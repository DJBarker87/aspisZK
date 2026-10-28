"""Private-source invocation of the standing Env-J runner and resource barrier."""
from pathlib import Path
import subprocess,json,hashlib,re,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028'
D='/home/dombarker/project-offloads/codex-pv-dlib-20261028';H='dombarker@100.108.41.90'
n=int(sys.argv[1]);m=sys.argv[2];retry=sys.argv[3] if len(sys.argv)>3 else '';assert 42200<=n<=42299
assert m.startswith('R1Z/PV_DL_');assert n<42297 or any(x in m for x in ['Audit','Replay'])
t=json.loads((E/'TALLY.json').read_text());assert ((n not in t['used_ids']) or (retry and n not in t['lean_charged'])) and len(t['lean_charged'])<100
p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean')
s=p.read_bytes();sha=hashlib.sha256(s).hexdigest()
# Sources are committed before launch, including h5 blob evidence.
blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip()
assert subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))])==s
meta=dict(attempt=n,module=m,source_path=str(p.relative_to(R)),source_blob=blob,source_sha256=sha,revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
code='''import json,pathlib,hashlib
b=pathlib.Path('/home/dombarker/project-offloads');d=b/'codex-pv-dlib-20261028'
e=json.load(open(b/'r1-privacy-build-integration-20261019/env/J.json'))
e['LEAN_PATH']=str(d/'lean-objects')+':'+str(d/'external-objects')+':'+e['LEAN_PATH'];(d/'env-J.json').write_text(json.dumps(e))
(d/'lean-objects/R1Z').mkdir(parents=True,exist_ok=True);(d/'lean-sources/R1Z').mkdir(parents=True,exist_ok=True)
roots=[pathlib.Path(x) for x in e['LEAN_PATH'].split(':')];deps={}
for m in IMPORTS:
 p=next((r/(m.replace('.','/')+'.olean') for r in roots if (r/(m.replace('.','/')+'.olean')).exists()),None)
 assert p is not None,('missing',m)
 deps[m]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
print(json.dumps(deps))
'''.replace('IMPORTS',repr(re.findall(r'^import (\S+)',s.decode(),re.M)))
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stdout+r.stderr
meta['imports']=json.loads(r.stdout);meta['deps_fingerprint']=hashlib.sha256(r.stdout.encode()).hexdigest()

if n not in t['used_ids']:t['used_ids'].append(n)
(E/'TALLY.json').write_text(json.dumps(t,indent=2)+'\n')
(E/f'{n}-source.lean.txt').write_bytes(s);(E/f'{n}-submission.json').write_text(json.dumps(meta,indent=2)+'\n')
# Admission before upload, separate receipt from the scope's second admission.
g='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
r=subprocess.run(['ssh',H,f'mkdir -p {D}/upload-{n}; python3 {g}/reservation.py {D}/upload-{n}/admission.json > {D}/upload-{n}/reservation.log 2>&1'],capture_output=True,text=True)
a=subprocess.check_output(['ssh',H,f'cat {D}/upload-{n}/admission.json'],text=True)
(E/f'{n}-upload-admission.json').write_text(a)
if r.returncode!=0 or json.loads(a).get('allowed') is not True:sys.exit(78)
subprocess.run(['scp','-q',str(p),H+':'+D+'/lean-sources/'+m+'.lean'],check=True)
cmd=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J.json',D+'/lean-objects',D+'/lean-sources',D+'/lean-objects/'+m+'.olean',D+'/lean-sources/'+m+'.lean','7000']
r=subprocess.run([sys.executable,str(R/'tools/pv-dlib-20261028/scope.py'),f'lean-{n}{retry}','focused Lean compilation; source/import fingerprints in submission receipt',*cmd])
receipt=E/f'lean-{n}{retry}/receipt.json'
if receipt.exists():
 j=json.loads(receipt.read_text());j.update(meta);log=(E/f'lean-{n}{retry}/output.log').read_text();j['print_axioms']=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log,re.S)
 receipt.write_text(json.dumps(j,indent=2)+'\n');t=json.loads((E/'TALLY.json').read_text());t['lean_charged'].append(n);(E/'TALLY.json').write_text(json.dumps(t,indent=2)+'\n')
sys.exit(r.returncode)
