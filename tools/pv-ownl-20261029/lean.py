"""Task inputs to standing run2.py; one admitted capped module per attempt."""
from pathlib import Path
import subprocess,json,hashlib,re,sys
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-ownl-20261029'
D='/home/dombarker/project-offloads/codex-pv-ownl-20261029'; H='dombarker@100.108.41.90'
n=int(sys.argv[1]);m=sys.argv[2];assert 65600<=n<=65699
assert n<65697 or any(x in m for x in ['Audit','Replay'])
deps={r['module']:r for r in json.loads((E/'focused-dependencies.json').read_text())['order']}
assert m.startswith('R1Z/PV_OWNL_') or m in deps
assert json.loads((E/'cohort-verification.json').read_text())['ok']
p=R/deps[m]['source_path'] if m in deps else R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean')
b=subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))])
if p.exists():assert p.read_bytes()==b
assert b==subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))])
assert not (E/f'lean-{n}/receipt.json').exists()
meta=dict(attempt=n,module=m,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip(),source_path=str(p.relative_to(R)),source_sha256=hashlib.sha256(b).hexdigest(),imports=re.findall(r'^import (\S+)',b.decode(),re.M),authority='h5 tracked source; inherited W calculus checked against merged candidate; no external rebuild')
# Upload is not a compiler launch. Scope admission and barrier are performed after upload.
r=subprocess.run(['ssh',H,'python3','-'],input="from pathlib import Path\nimport base64\np=Path("+repr(D+'/lean-sources/'+m+'.lean')+");p.parent.mkdir(parents=True,exist_ok=True);Path('/home/dombarker/project-offloads/codex-pv-ownl-20261029/lean-objects/R1Z').mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode("+repr(__import__('base64').b64encode(b).decode())+"))\n",text=True);assert r.returncode==0
meta['dependency_objects']={}
for dep in meta['imports']:
 if True:
  q=subprocess.check_output(['ssh',H,"python3 -c \"import json,pathlib,hashlib; roots=[pathlib.Path("+repr(D+'/lean-objects')+")]+[pathlib.Path(x) for x in json.load(open("+repr(D+'/env-J.json')+"))['LEAN_PATH'].split(':')]; p=next(r/("+repr(dep.replace('.','/')+'.olean')+") for r in roots if (r/("+repr(dep.replace('.','/')+'.olean')+")).exists()); print(hashlib.sha256(p.read_bytes()).hexdigest())\""],text=True).strip()
  meta['dependency_objects'][dep]=q
meta['deps_fingerprint']=hashlib.sha256(json.dumps(meta['dependency_objects'],sort_keys=True).encode()).hexdigest()
(E/f'{n}-submission.json').write_text(json.dumps(meta,indent=2)+'\n')
cmd=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J.json',D+'/lean-objects',D+'/lean-sources',D+'/lean-objects/'+m+'.olean',D+'/lean-sources/'+m+'.lean','7000']
r=subprocess.run([sys.executable,str(R/'tools/pv-ownl-20261029/scope.py'),f'lean-{n}','focused Lean compilation',*cmd])
f=E/f'lean-{n}/receipt.json'
if f.exists():
 j=json.loads(f.read_text());j.update(meta);j['print_axioms']=(f.parent/'output.log').read_text();f.write_text(json.dumps(j,indent=2)+'\n')
sys.exit(r.returncode)
