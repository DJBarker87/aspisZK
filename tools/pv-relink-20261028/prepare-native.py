"""Private pinned Rust copies plus appended access only; never edits shipped files."""
from pathlib import Path
import subprocess,json,hashlib,tarfile,io
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-relink-20261028';D='/home/dombarker/project-offloads/codex-pv-relink-20261028';H='dombarker@100.108.41.90'
files=['native-Cargo.toml','v195.rs','v195-bridge.rs','v195-field-bridge.rs','v233.rs','v233-bridge.rs','run-cargo.sh']
subprocess.run(['python3',str(R/'tools/pv-relink-20261028/upload.py'),'native-prepare',*['tools/pv-relink-20261028/'+x for x in files]],check=True)
# Git archive fixes the source revision; no generated/build tree is transferred.
data=subprocess.check_output(['git','archive','82566acdfb','crates/aspis-core'],cwd=R)
r=subprocess.run(['ssh',H,f'mkdir -p {D}/native/staging; tar xf - -C {D}/native/staging'],input=data,capture_output=True);assert r.returncode==0,r.stderr
code=r'''
from pathlib import Path
import json,hashlib,shutil
D=Path(DIR);N=D/'native';sha=lambda b:hashlib.sha256(b).hexdigest();pins={}
core=N/'staging/crates/aspis-core';dst=N/'core';assert not dst.exists();core.rename(dst)
for p in dst.rglob('*'):
 if p.is_file():pins['core/'+str(p.relative_to(dst))]=dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size)
for p,suffix in [(dst/'src/field/wide_exact.rs','v195-bridge.rs'),(dst/'src/field.rs','v195-field-bridge.rs')]:
 original=p.read_bytes();append=b'\n'+(D/suffix).read_bytes();p.write_bytes(original+append);assert p.read_bytes()[:len(original)]==original
 pins['appended/'+str(p.relative_to(dst))]=dict(original_sha256=sha(original),prefix_size=len(original),suffix_sha256=sha(append),complete_sha256=sha(p.read_bytes()))
registry=Path.home()/'.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/block-buffer-0.10.4';block=N/'block-buffer';shutil.copytree(registry,block)
for p in block.rglob('*'):
 if p.is_file():pins['block-buffer/'+str(p.relative_to(block))]=dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size)
p=block/'src/lib.rs';original=p.read_bytes();append=b'\n'+(D/'v233-bridge.rs').read_bytes();p.write_bytes(original+append);assert p.read_bytes()[:len(original)]==original
pins['appended/block-buffer/src/lib.rs']=dict(original_sha256=sha(original),prefix_size=len(original),suffix_sha256=sha(append),complete_sha256=sha(p.read_bytes()))
for f in ['v195.rs','v233.rs']:shutil.copyfile(D/f,N/f)
shutil.copyfile(D/'native-Cargo.toml',N/'Cargo.toml')
shutil.rmtree(N/'staging')
print(json.dumps(pins))
'''.replace('DIR',repr(D))
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
pins=json.loads(r.stdout)
# Verify all copied core files against the pinned git blob bytes, not names.
for p,x in pins.items():
 if p.startswith('core/'):
  b=subprocess.check_output(['git','show','82566acdfb:crates/aspis-core/'+p[5:]],cwd=R);assert hashlib.sha256(b).hexdigest()==x['sha256'],p
assert pins['block-buffer/src/sealed.rs']['sha256']==hashlib.sha256((E/'block-buffer-sealed.rs.txt').read_bytes()).hexdigest()
(E/'native-source-pins.json').write_text(json.dumps(pins,indent=2)+'\n');print('native source prefixes pinned; appended access only')
