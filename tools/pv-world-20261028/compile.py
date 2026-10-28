from pathlib import Path
import base64,hashlib,json,subprocess,sys,re,time,datetime
from importlib import import_module
archive_refusal=import_module("archive-refusal").archive
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-world-20261028'
D='/home/dombarker/project-offloads/codex-pv-world-20261028';H='dombarker@100.108.41.90'
G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
n=int(sys.argv[1]);m=sys.argv[2]
# Any admission refusal imposes the full 180-second cooldown before any launch.
for refusal in E.glob('refusal-504*-*.json'):
 a=json.loads(refusal.read_text())
 if a.get('allowed') is False and a.get('utc'):
  deadline=datetime.datetime.fromisoformat(a['utc']).timestamp()+180
  if time.time()<deadline:
   print('Full admission cooldown before retry',deadline-time.time(),flush=True)
   while time.time()<deadline:time.sleep(min(60,deadline-time.time()))

dependencies = {'R1Z/ProverRwFull'+x: 'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFull'+x+'.lean' for x in ['ExternalTypes','Types','ExternalFuns','Funs']}
resolution=json.loads((E/'observation-resolution.json').read_text())['modules'] if (E/'observation-resolution.json').exists() else {}
pin=resolution.get(m.replace('/','.'))
assert 50400<=n<=50499 and (m.startswith(('R1Z/PV_W_','R1Z/PV_FXM_','R1Z/PDict_')) or m in dependencies or pin is not None)
assert n<50497 or 'Audit' in m or 'Replay' in m
assert json.loads((E/'external-verification.json').read_text())['ok']
assert json.loads((E/'d372-id-preflight.json').read_text())['unused']
p=R/pin['path'] if pin else R/dependencies[m] if m in dependencies else R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean')
if pin:
 b=subprocess.check_output(['git','cat-file','blob',pin['blob']]);assert hashlib.sha256(b).hexdigest()==pin['sha256']
else:
 b=p.read_bytes();assert b==subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))])
assert not (E/f'lean-{n}/receipt.json').exists()
q=subprocess.run(['ssh',H,f'python3 {G}/reservation.py {D}/upload-{n}.json > {D}/upload-{n}.log 2>&1'],capture_output=True,text=True)
s=subprocess.run(['ssh',H,f'cat {D}/upload-{n}.json'],capture_output=True,text=True)
upload=json.loads(s.stdout)
(E/f'upload-{n}.json').write_text(json.dumps(dict(sha256=hashlib.sha256(s.stdout.encode()).hexdigest(),host_path=D+f'/upload-{n}.json',**{k:upload.get(k) for k in ['allowed','utc','error','bounded_reserved_bytes','safe_limit_bytes']}),indent=2)+'\n')
if q.returncode!=0 or json.loads(s.stdout).get('allowed') is not True:
 archive_refusal(n)
 print('UNCHARGED UPLOAD REFUSAL',n,q.returncode,json.loads(s.stdout).get('utc'));sys.exit(78)
code=f'''from pathlib import Path
import base64,hashlib
p=Path({D+'/lean-sources/'+m+'.lean'!r});p.parent.mkdir(parents=True,exist_ok=True)
b=base64.b64decode({base64.b64encode(b).decode()!r});p.write_bytes(b)
assert hashlib.sha256(p.read_bytes()).hexdigest()=={hashlib.sha256(b).hexdigest()!r}
# Compilation must never write through a private cache link into a reused directory.
o=Path({D+'/lean-objects/'+m+'.olean'!r});o.parent.mkdir(parents=True,exist_ok=True)
for q in [o,Path(str(o)+'.server'),Path(str(o)+'.private'),o.with_suffix('.ir')]:
 if q.is_symlink():q.unlink()
'''
q=subprocess.run(['ssh',H,'python3','-'],input=code,text=True);assert q.returncode==0
meta=dict(id=n,module=m,source_revision=pin['revision'] if pin else subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_path=str(p.relative_to(R)),source_blob=pin['blob'] if pin else subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip(),source_sha256=hashlib.sha256(b).hexdigest(),external_manifest_sha256=hashlib.sha256((E/'external-object-manifest.json').read_bytes()).hexdigest(),project_imports=['R1Z.PV_W_Threading'] if 'import R1Z.PV_W_Threading' in b.decode() else [],reused_project_objects=[],deps_fingerprint=hashlib.sha256((E/'external-verification.json').read_bytes()).hexdigest())
deps=[d for d in pin['imports'] if d in resolution] if pin else re.findall(r'^import (R1Z\.\S+)',b.decode(),re.M)
meta['project_imports']=deps
meta['direct_dependency_objects']={}
for dep in deps:
 dp=D+'/lean-objects/'+dep.replace('.','/')+'.olean'
 z=subprocess.check_output(['ssh',H,'sha256sum '+dp],text=True).split()[0]
 sp=R/dependencies[dep.replace('.','/')] if dep.replace('.','/') in dependencies else R/'docs/research/v8-r0-zk-20261009/lean'/(dep.replace('.','/')+'.lean')
 meta['direct_dependency_objects'][dep]=dict(path=dp,sha256=z,source_sha256=resolution[dep]['sha256'] if dep in resolution else hashlib.sha256(sp.read_bytes()).hexdigest())
selection=E/'os-cache-selection.json'
meta['transitive_cache_selection_sha256']=hashlib.sha256(selection.read_bytes()).hexdigest() if pin and selection.exists() else None
meta['external_selection_sha256']=hashlib.sha256((E/'private-external-selection.json').read_bytes()).hexdigest() if (E/'private-external-selection.json').exists() else None
meta['deps_fingerprint']=hashlib.sha256(json.dumps(dict(direct=meta['direct_dependency_objects'],transitive=meta['transitive_cache_selection_sha256'],external=meta['external_selection_sha256']),sort_keys=True).encode()).hexdigest()
(E/f'{n}-source.json').write_text(json.dumps(meta,indent=2)+'\n')
cmd=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J.json',D+'/lean-objects',D+'/lean-sources',D+'/lean-objects/'+m+'.olean',D+'/lean-sources/'+m+'.lean','7000']
r=subprocess.run([sys.executable,str(R/'tools/pv-world-20261028/scope.py'),f'lean-{n}','compilation of '+m,*cmd])
if r.returncode==78:archive_refusal(n)
p=E/f'lean-{n}/receipt.json'
if p.exists():
 j=json.loads(p.read_text());j.update(meta);j['print_axioms']=(p.parent/'output.log').read_text();p.write_text(json.dumps(j,indent=2)+'\n')
sys.exit(r.returncode)
