"""Read-only complete final project/external/source fingerprint before cleanup."""
from pathlib import Path
import json,hashlib,lzma,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2f-20261029');old=D.with_name('codex-pv-rdb2e-20261029');env=json.loads((D/'env-J.json').read_text());roots=list(map(Path,env['LEAN_PATH'].split(':')))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def obj(m):return next(r/(m.replace('.','/')+'.olean')for r in roots if(r/(m.replace('.','/')+'.olean')).exists())
def companions(p):return [dict(path=str(q),sha256=sha(q),bytes=q.stat().st_size)for q in [p.with_suffix('.ir'),Path(str(p)+'.server'),Path(str(p)+'.private')]if q.exists()]
cohort=json.loads((D/'r72-cohort.json').read_text());objects={}
for r in cohort['modules']:
 p=obj(r['module']);assert sha(p)==r['object_sha256'],r['module'];objects[r['module']]=dict(module=r['module'],path=str(p),object_sha256=sha(p),source=r['source'],imports=r['imports'],companions=companions(p))
for r in json.loads((D/'successful-sources.json').read_text()):
 m=r['module'].replace('/','.');s=D/'lean-sources'/(m.replace('.','/')+'.lean');p=obj(m);assert sha(s)==r['source_sha256'],m
 imports=re.findall(r'^(?:public )?import (\S+)',s.read_text(),re.M);assert not any(any(part.startswith('XR')for part in imp.split('.'))for imp in imports)
 objects[m]=dict(module=m,path=str(p),object_sha256=sha(p),object_bytes=p.stat().st_size,source=dict(path=r['source_path'],blob=r['source_blob'],sha256=sha(s),revision=r['source_revision']),imports=[dict(module=i,path=str(obj(i)),object_sha256=sha(obj(i)))for i in imports],companions=companions(p))
external=[]
for r in cohort['external']:
 p=obj(r['module']);assert sha(p)==r['actual'];external.append(dict(**r,companions=companions(p)))
registry=[]
for record in [json.loads((old/'source-paths.json').read_text()),json.loads((D/'extra-source-pins.json').read_text())]:
 for r in record:
  p=Path(r['path']);assert sha(p)==r['sha256'];registry.append(r)
project_native=[]
for r in json.loads((old/'native-source-pins.json').read_text()):
 p=D.parent/'codex-pv-fscan-20261028/src'/r['path'];assert sha(p)==r['sha256'];project_native.append(r)
native=json.loads((D/'native-inputs.json').read_text())
native['input_checks']=[]
for r in native['inputs']:
 p=Path(r['path']);actual=sha(p);source=p.suffix=='.rs' or p.name in ['Cargo.toml','Cargo.lock']
 if source:assert actual==r['sha256'],str(p)
 native['input_checks'].append(dict(**r,actual=actual,source_input=source,explanation='frozen source/manifest input' if source else 'scope receipt/log; not a compiler input; output/time logs filled during the run'))
codegen=[]
for p in (D/'target/release/.fingerprint').glob('*/bin-associations.json'):
 r=json.loads(p.read_text());codegen.append(dict(path=str(p),sha256=sha(p),rustflags=r.get('rustflags'),features=r.get('features'),profile=r.get('profile')))
assert codegen
binary=D/'target/release/associations';collisions=[]
for d in D.parent.glob('codex-pv-*'):
 if d!=D:collisions.extend(str(p)for p in d.glob('lean-633[0-9][0-9]'))
sent=D.parent/'r1-privacy-build-integration-20261019/evidence/sent.txt'
if sent.exists():collisions.extend(line for line in sent.read_text().splitlines()if re.search(r'\b633\d\d\b',line))
assert not collisions,collisions
j=dict(environment=env,objects=list(objects.values()),external=external,registry_sources=registry,project_native_sources=project_native,native_inputs=native,codegen=codegen,binary=dict(path=str(binary),sha256=sha(binary),bytes=binary.stat().st_size),collisions=collisions,R72_authority='r72-cohort.json',cohort_unchanged_through_final_replay=True)
raw=json.dumps(j,indent=2).encode();(D/'closure-fingerprint.json.xz').write_bytes(lzma.compress(raw,preset=6));(D/'closure-fingerprint.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');print(json.dumps(dict(objects=len(objects),external=len(external),registry_sources=len(registry),all_hashes_match=True,binary=j['binary'],codegen=codegen)),flush=True)
