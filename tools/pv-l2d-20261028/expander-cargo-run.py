"""Host-side phases, executed inside one admitted capped scope."""
from pathlib import Path
import subprocess,json,time,os,hashlib,sys
H=Path('/home/dombarker/project-offloads/codex-pv-l2d-20261028');P=H/'expander-native';E=H/'evidence';E.mkdir(exist_ok=True)
env=os.environ.copy();env['PATH']='/home/dombarker/.cargo/bin:'+env.get('PATH','');env['CARGO_TARGET_DIR']=str(H/'expander-target');env['RUSTFLAGS']='-C codegen-units=1 -C link-arg=-Wl,--threads=4'
rows=[]
def phase(label,cmd,expected=0):
 start=time.monotonic()
 with (E/(label+'.out')).open('w') as out,(E/(label+'.err')).open('w') as err:r=subprocess.run(cmd,cwd=P,env=env,stdout=out,stderr=err)
 rows.append(dict(phase=label,command=cmd,exit=r.returncode,expected=expected,wall_seconds=time.monotonic()-start));(E/'expander-phases.json').write_text(json.dumps(rows,indent=2))
 if r.returncode!=expected:raise RuntimeError(rows[-1])
cargo='/home/dombarker/.cargo/bin/cargo'
phase('expander-lock',[cargo,'generate-lockfile','--offline'])
phase('expander-metadata',[cargo,'metadata','--offline','--locked','--format-version','1'])
meta=json.loads((E/'expander-metadata.out').read_text());z=next(p for p in meta['packages'] if p['name']=='zeroize');assert z['version']=='1.8.1'
root=Path(z['manifest_path']).parent;checks=json.loads((root/'.cargo-checksum.json').read_text());assert checks['package']=='ced3678a2879b30306d323f4542626697a464a97c0a07c9aebf7ebca65cd4dde'
verified=[dict(path=str(root/p),expected=h,actual=hashlib.sha256((root/p).read_bytes()).hexdigest()) for p,h in checks['files'].items()];assert all(v['expected']==v['actual'] for v in verified)
(E/'zeroize-source-check.json').write_text(json.dumps(dict(version=z['version'],checksum=checks['package'],files=verified,features=next(n['features'] for n in meta['resolve']['nodes'] if n['id']==z['id'])),indent=2))
phase('expander-build',[cargo,'build','--release','--offline','--locked','-j','4'])
binary=H/'expander-target/release/pv-l2d-expander-native'
phase('expander-positive',[str(binary)])
phase('expander-negative',[str(binary),'negative'],101)
print((E/'expander-positive.out').read_text().strip());print(json.dumps(dict(negative_exit=101,source_checked=True,binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),binary_bytes=binary.stat().st_size)))
