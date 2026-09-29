#!/usr/bin/env python3
"""Execute already-compiled Lean model to export full source replay fixtures."""
import argparse,hashlib,json,os,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--sources',type=Path,required=True)
p.add_argument('--cache',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
assert not a.output.exists();a.output.mkdir()
name='AspisV8R19/SamplerReplay';src=a.sources/(name+'.lean')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
metadata=json.loads((a.cache/'metadata.json').read_text())
record=next(r for r in metadata if r['target_name']==name)
assert record['exit']==0 and record['source_sha256']==sha(src)
retained=Path('/home/dombarker/project-offloads/aspis-pool-single-decode-20260825-a3/AspisFormal')
deps=sorted((retained/'.lake/packages').glob('*/.lake/build/lib/lean'))
env=dict(os.environ,PATH='/home/dombarker/.elan/bin:/usr/bin:/bin',NO_DNA='1',
    LEAN_PATH=':'.join(map(str,[a.cache/'lib',*deps])))
fixture=a.output/'fixtures.txt'
cmd=['/home/dombarker/.elan/bin/lake','env','lean','--run',str(src),str(fixture)]
with(a.output/'export.log').open('w')as f:
    result=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=a.cache/'workspace',env=env,stdout=f,stderr=subprocess.STDOUT)
print((a.output/'export.log').read_text(),flush=True)
out={'base_revision':'a26a468746e9551769ce1d17104050e1fc1bf1fc','command':cmd,'exit':result.returncode,
    'source_sha256':sha(src),'compiled_cache_metadata_sha256':sha(a.cache/'metadata.json')}
if result.returncode==0:
    out.update(fixture_sha256=sha(fixture),fixture_bytes=fixture.stat().st_size,
        fixture_rows=sum(1 for _ in fixture.open()))
(a.output/'metadata.json').write_text(json.dumps(out,indent=2)+'\n')
raise SystemExit(result.returncode)
