"""Create one linked scratch overlay; immutable source corpus is shared, not copied."""
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-native-prepare2-20261027'
old='/home/dombarker/project-offloads/codex-cx-native-prepare1-20261027/NBA_src'
pins=json.loads(Path('evidence/native-prepare1-20261027/NBA_SOURCE.json').read_text())['source_sha256']
replace=['Cargo.lock','crates/aspis-core/src/r0_transcript.rs','crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/sampler.rs','crates/aspis-r1-cost-probe/src/candidate.rs']
owned={n:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n]).decode() for n in replace}
owned['crates/aspis-r1-cost-probe/src/candidate.rs']+='\n#[cfg(kani)]\nmod NBL_candidate;\n'
x=dict(pins=pins,owned=owned,B=B,old=old)
code='''from pathlib import Path
import json,hashlib
x=json.loads(PAYLOAD);b=Path(x['B']);s=b/'NBL_src';s.mkdir(exist_ok=True);old=Path(x['old'])
for n,h in x['pins'].items():
 p=old/n;assert p.is_file(),n
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h,n
 q=s/n;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists() or q.is_symlink():raise RuntimeError('overlay exists: '+str(q))
 if n in x['owned']:q.write_text(x['owned'][n])
 elif p.name=='Cargo.toml':q.write_bytes(p.read_bytes())
 else:q.symlink_to(p)
for name in ['NBL_tmp']: (b/name).mkdir(exist_ok=True)
pins={str(p.relative_to(s)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,link=p.is_symlink()) for p in s.rglob('*') if p.is_file()}
(b/'NBL_SOURCE.json').write_text(json.dumps(pins,indent=2)+'\\n')
print(json.dumps(dict(files=len(pins),source_sha256={n:v['sha256'] for n,v in pins.items()},linked_overlay=True,owned_files=list(x['owned']),shared_source=str(old))))
'''.replace('PAYLOAD',repr(json.dumps(x)))
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NBL_SETUP.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stderr
v=json.loads(r.stdout);(E/'NBL_SOURCE.json').write_text(json.dumps(v,indent=2)+'\n')
print(json.dumps({k:v[k] for k in ['files','linked_overlay','owned_files','shared_source']}))
