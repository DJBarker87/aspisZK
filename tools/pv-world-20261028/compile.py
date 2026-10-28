from pathlib import Path
import base64,hashlib,json,subprocess,sys,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-world-20261028'
D='/home/dombarker/project-offloads/codex-pv-world-20261028';H='dombarker@100.108.41.90'
G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
n=int(sys.argv[1]);m=sys.argv[2]
assert 36000<=n<=36199 and m.startswith('R1Z/PV_W_')
assert n<36197 or 'Audit' in m or 'Replay' in m
assert json.loads((E/'external-verification.json').read_text())['ok']
assert json.loads((E/'id-preflight.json').read_text())['unused']
p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean')
b=p.read_bytes();assert b==subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))])
assert not (E/f'lean-{n}/receipt.json').exists()
q=subprocess.run(['ssh',H,f'python3 {G}/reservation.py {D}/upload-{n}.json > {D}/upload-{n}.log 2>&1'],capture_output=True,text=True)
s=subprocess.run(['ssh',H,f'cat {D}/upload-{n}.json'],capture_output=True,text=True)
(E/f'upload-{n}.json').write_text(s.stdout)
assert q.returncode==0 and json.loads(s.stdout)['allowed'] is True,(q.returncode,q.stderr,s.stdout)
code=f'''from pathlib import Path
import base64,hashlib
p=Path({D+'/lean-sources/'+m+'.lean'!r});p.parent.mkdir(parents=True,exist_ok=True)
b=base64.b64decode({base64.b64encode(b).decode()!r});p.write_bytes(b)
assert hashlib.sha256(p.read_bytes()).hexdigest()=={hashlib.sha256(b).hexdigest()!r}
'''
q=subprocess.run(['ssh',H,'python3','-'],input=code,text=True);assert q.returncode==0
meta=dict(id=n,module=m,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_path=str(p.relative_to(R)),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip(),source_sha256=hashlib.sha256(b).hexdigest(),external_manifest_sha256=hashlib.sha256((E/'external-object-manifest.json').read_bytes()).hexdigest(),project_imports=['R1Z.PV_W_Threading'] if 'import R1Z.PV_W_Threading' in b.decode() else [],reused_project_objects=[],deps_fingerprint=hashlib.sha256((E/'external-verification.json').read_bytes()).hexdigest())
deps=re.findall(r'^import (R1Z\.PV_W_\S+)',b.decode(),re.M)
meta['project_imports']=deps
meta['direct_dependency_objects']={}
for dep in deps:
 dp=D+'/lean-objects/'+dep.replace('.','/')+'.olean'
 z=subprocess.check_output(['ssh',H,'sha256sum '+dp],text=True).split()[0]
 sp=R/'docs/research/v8-r0-zk-20261009/lean'/(dep.replace('.','/')+'.lean')
 meta['direct_dependency_objects'][dep]=dict(path=dp,sha256=z,source_sha256=hashlib.sha256(sp.read_bytes()).hexdigest())
meta['deps_fingerprint']=hashlib.sha256(json.dumps(meta['direct_dependency_objects'],sort_keys=True).encode()).hexdigest()
(E/f'{n}-source.json').write_text(json.dumps(meta,indent=2)+'\n')
cmd=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J.json',D+'/lean-objects',D+'/lean-sources',D+'/lean-objects/'+m+'.olean',D+'/lean-sources/'+m+'.lean','7000']
r=subprocess.run([sys.executable,str(R/'tools/pv-world-20261028/scope.py'),f'lean-{n}','compilation of '+m,*cmd])
p=E/f'lean-{n}/receipt.json'
if p.exists():
 j=json.loads(p.read_text());j.update(meta);j['print_axioms']=(p.parent/'output.log').read_text();p.write_text(json.dumps(j,indent=2)+'\n')
sys.exit(r.returncode)
