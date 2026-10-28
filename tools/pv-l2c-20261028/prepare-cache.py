"""Copy no shared source. Link a dependency-closed, fingerprinted Stream-B cache privately."""
from pathlib import Path
import json,subprocess,shlex,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028'
r=json.loads((E/'focused-resolution.json').read_text())['resolved']
bad=set(json.loads((E/'rebuild-set.json').read_text()))
cache={x['module']:x for x in json.loads((E/'focused-project-cache-check.json').read_text())}
clean={m:x for m,x in cache.items() if m not in bad}
assert all(x.get('source_match') or x.get('retained_own_cache_source_match') for x in clean.values())
assert all(not any(i in bad for i in r[m]['imports']) for m in clean)
ext={x['module'].replace('/','.'):x['object_sha256'] for x in json.loads((R/'evidence/pv-runjoin20-20261027/external-object-manifest.json').read_text())}
for m,x in clean.items():
 x['source_resolution']=r[m]
 x['complete_direct_fingerprint']={i:(clean[i]['object_sha256'] if i in clean else ext[i]) for i in r[m]['imports']}
code='''import json,sys,pathlib,hashlib
rows=json.load(sys.stdin);H=pathlib.Path('/home/dombarker/project-offloads/codex-pv-l2c-20261028/lean');base=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'));old=json.load(open('/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin24-lean/J.json'));assert all(v==old[k] for k,v in base.items() if k!='LEAN_PATH')
oldroots=[pathlib.Path(x) for x in old['LEAN_PATH'].split(':')];checks=[]
for m,x in rows.items():
 p=pathlib.Path(x['object_path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==x['object_sha256'],m
 if x.get('source_match'):assert hashlib.sha256(pathlib.Path(x['source_path']).read_bytes()).hexdigest()==x['expected_sha256'],m
 for dep,want in x['complete_direct_fingerprint'].items():
  q=next(root/(dep.replace('.','/')+'.olean') for root in oldroots if (root/(dep.replace('.','/')+'.olean')).is_file());assert hashlib.sha256(q.read_bytes()).hexdigest()==want,(m,dep)
 for suffix in ['.olean','.olean.private','.olean.server','.ilean']:
  q=p.with_suffix(suffix) if suffix=='.ilean' else pathlib.Path(str(p)[:-6]+suffix)
  if not q.is_file():continue
  dest=H/'objects'/(m.replace('.','/')+suffix);dest.parent.mkdir(parents=True,exist_ok=True)
  if dest.exists() or dest.is_symlink():assert dest.is_file() and hashlib.sha256(dest.read_bytes()).digest()==hashlib.sha256(q.read_bytes()).digest(),str(dest)
  else:dest.symlink_to(q.resolve())
  checks.append(dict(module=m,suffix=suffix,path=str(dest),retained=str(q.resolve()),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
print(json.dumps(dict(toolchain_match=True,project_modules=len(rows),objects=checks)))
'''
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(clean),text=True,capture_output=True)
assert p.returncode==0,p.stderr
out=json.loads(p.stdout);out['source_and_import_fingerprints']=clean
(E/'private-cache-h6.json').write_text(json.dumps(out,indent=2)+'\n')
print('Private pinned cache:',out['project_modules'],'project modules; no source overwritten; rebuild',len(bad))
