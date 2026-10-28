from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-native-prepare5-20261028'
old='/home/dombarker/project-offloads/codex-cx-native-prepare1-20261027/NBA_src'
pins=json.loads(Path('evidence/native-prepare1-20261027/NBA_SOURCE.json').read_text())['source_sha256']
owned={n:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n]).decode() for n in ['Cargo.lock','crates/aspis-core/src/r0_transcript.rs','crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/sampler.rs','crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/r1_wire.rs']}
owned['crates/aspis-r1-cost-probe/src/candidate.rs']+='\n#[cfg(kani)]\nmod NCH_candidate;\n'
owned['crates/aspis-r1-cost-probe/src/lib.rs']='#![cfg_attr(kani, feature(allocator_api))]\n'+owned['crates/aspis-r1-cost-probe/src/lib.rs']
patch=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
assert hashlib.sha256(patch.encode()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
x=dict(pins=pins,owned=owned,B=B,old=old,patch=patch)
code='''from pathlib import Path
import json,hashlib,subprocess,sys
x=json.loads(PAYLOAD);b=Path(x['B']);b.mkdir(exist_ok=True)
with (b/'NCH_SETUP-barrier.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NCH_SETUP-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NCH_SETUP-reservation.json').read_text());assert r.returncode==0 and a['allowed'] is True,(r.returncode,a)
s=b/'NCH_src';s.mkdir(exist_ok=True);old=Path(x['old'])
for n,h in x['pins'].items():
 p=old/n;assert p.is_file(),n
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h,n
 q=s/n;q.parent.mkdir(parents=True,exist_ok=True)
 assert not q.exists() and not q.is_symlink(),str(q)
 if n in x['owned']:q.write_text(x['owned'][n])
 elif p.name=='Cargo.toml':q.write_bytes(p.read_bytes())
 else:q.symlink_to(p)
r=subprocess.run(['git','apply','--unsafe-paths','-'],cwd=s,input=x['patch'],text=True,capture_output=True);assert r.returncode==0,r.stderr
(b/'NCH_tmp').mkdir(exist_ok=True)
pins={str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}
cache=Path('/home/dombarker/project-offloads/codex-cx-prepare-cache-20261028')
objects={str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in cache.rglob('*') if p.is_file()}
print(json.dumps(dict(files=len(pins),source_sha256=pins,shared_source=str(old),cache_imports=objects,reservation=a)))
'''.replace('PAYLOAD',repr(json.dumps(x)))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NCH_SETUP.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr+r.stdout
v=json.loads(r.stdout);(E/'NCH_SOURCE.json').write_text(json.dumps(v,indent=2)+'\n')
print(json.dumps(dict(files=v['files'],cache_objects=len(v['cache_imports']),reservation=v['reservation'])))
