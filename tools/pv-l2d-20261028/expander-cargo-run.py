"""Host-side phases, executed inside one admitted capped scope."""
from pathlib import Path
import subprocess,json,time,os,hashlib,sys,tarfile,tomllib
H=Path('/home/dombarker/project-offloads/codex-pv-l2d-20261028');P=H/'expander-native';E=H/'evidence/expander-v3';E.mkdir(parents=True,exist_ok=True)
env=os.environ.copy();env['PATH']='/home/dombarker/.cargo/bin:'+env.get('PATH','');env['CARGO_TARGET_DIR']=str(H/'expander-target');env['RUSTFLAGS']='-C codegen-units=1 -C link-arg=-Wl,--threads=4'
rows=[]
def phase(label,cmd,expected=0):
 start=time.monotonic()
 with (E/(label+'.out')).open('w') as out,(E/(label+'.err')).open('w') as err:r=subprocess.run(cmd,cwd=P,env=env,stdout=out,stderr=err)
 rows.append(dict(phase=label,command=cmd,exit=r.returncode,expected=expected,wall_seconds=time.monotonic()-start));(E/'expander-phases.json').write_text(json.dumps(rows,indent=2))
 if r.returncode!=expected:raise RuntimeError(rows[-1])
cargo='/home/dombarker/.cargo/bin/cargo'
phase('rustc-version',['/home/dombarker/.cargo/bin/rustup','run','1.94.1','rustc','--version','--verbose'])
phase('expander-lock',[cargo,'+1.94.1','generate-lockfile','--offline'])
phase('expander-metadata',[cargo,'+1.94.1','metadata','--offline','--locked','--format-version','1'])
meta=json.loads((E/'expander-metadata.out').read_text());z=next(p for p in meta['packages'] if p['name']=='zeroize');assert z['version']=='1.9.0'
lock=tomllib.loads((P/'Cargo.lock').read_text());pins={(r['name'],r['version']):r['checksum'] for r in lock['package'] if 'checksum' in r};verified=[]
for pkg in meta['packages']:
 if not pkg.get('source',''):continue
 root=Path(pkg['manifest_path']).parent;archive=Path('/home/dombarker/.cargo/registry/cache')/root.parent.name/(pkg['name']+'-'+pkg['version']+'.crate')
 expected=pins[(pkg['name'],pkg['version'])];actual=hashlib.sha256(archive.read_bytes()).hexdigest();assert actual==expected,(archive,actual,expected)
 files=[]
 with tarfile.open(archive) as tar:
  for member in tar.getmembers():
   if not member.isfile():continue
   rel=Path(member.name).relative_to(pkg['name']+'-'+pkg['version']);wanted=hashlib.sha256(tar.extractfile(member).read()).hexdigest();got=hashlib.sha256((root/rel).read_bytes()).hexdigest();assert got==wanted,(root/rel,wanted,got);files.append(dict(path=str(root/rel),sha256=got))
 verified.append(dict(package=pkg['name'],version=pkg['version'],archive=str(archive),checksum=actual,files=files,features=next(n['features'] for n in meta['resolve']['nodes'] if n['id']==pkg['id'])))
(E/'dependency-source-check.json').write_text(json.dumps(verified,indent=2))
phase('expander-build',[cargo,'+1.94.1','build','--release','--offline','--locked','-j','4'])
binary=H/'expander-target/release/pv-l2d-expander-native'
phase('expander-positive',[str(binary)])
phase('expander-negative',[str(binary),'negative'],101)
print((E/'expander-positive.out').read_text().strip());print(json.dumps(dict(negative_exit=101,source_checked=True,binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),binary_bytes=binary.stat().st_size)))
