"""Re-run original sha/digest/split fixtures with pinned deployed versions/features."""
from pathlib import Path
import os,sys,json,subprocess,shutil,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2-20261028');suite=sys.argv[1];O=D/('classify-dep-'+suite);O.mkdir(exist_ok=True);V=D/'classification-vendor';P=D/'classification-dep-fixture';P.mkdir(exist_ok=True)
old=Path('/home/dombarker/project-offloads/codex-pv-dlib-20261028');reg=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
pins=[]
for name in ['sha2-0.10.9','digest-0.10.7','block-buffer-0.10.4']:
 for src in (old/'native'/name).rglob('*'):
  rel=src.relative_to(old/'native'/name)
  if not src.is_file() or ('src' not in rel.parts and src.name!='Cargo.toml'):continue
  dst=V/name/rel;dst.parent.mkdir(parents=True,exist_ok=True)
  if not dst.exists():shutil.copy2(src,dst)
  b=dst.read_bytes();orig=reg/name/rel
  if orig.exists():
   raw=orig.read_bytes();assert b.startswith(raw),(name,str(rel),'prefix drift')
   # Expose only appended snapshot constructors; do not set cfg(kani) on deployed bodies.
   suffix=b[len(raw):];new=raw+suffix.replace(b'#[cfg(kani)] ',b'')
   if new!=b:dst.write_bytes(new);b=new
   pins.append(dict(path=str(dst),registry_path=str(orig),registry_sha256=hashlib.sha256(raw).hexdigest(),fixture_sha256=hashlib.sha256(b).hexdigest(),prefix_identical=True,suffix_bytes=len(b)-len(raw)))
if suite=='split':
 lib=V/'block-buffer-0.10.4/src/lib.rs';bridge=(D/'classification-inputs/v233-bridge.rs').read_text();raw=lib.read_text()
 if 'pub fn pv_rl_split' not in raw:lib.write_text(raw+'\n'+bridge)
 source=D/'classification-inputs/v233.rs';test=False
else:
 filename={'sha':'sha-final-native.rs','ct':'ct-final-native.rs'}[suite];source=old/'wrapper-proof'/filename;test=True
 # Only small fixture/support sources; never copy the other worker's compiled outputs.
 for name in [filename,'padding-retained-reference.rs']:
  p=old/'wrapper-proof'/name
  if p.exists():shutil.copy2(p,P/name)
 source=P/filename
manifest='''[package]\nname="pv-fscan-deployed-dep-fixture"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[dependencies]\nsha2="=0.10.9"\ndigest={version="=0.10.7",features=["alloc","const-oid","core-api","mac","oid","std"]}\nblock-buffer="=0.10.4"\ngeneric-array={version="=0.14.7",features=["more_lengths","zeroize"]}\ntypenum={version="=1.20.1",features=["const-generics"]}\ncrypto-common={version="=0.1.7",features=["getrandom","rand_core","std"]}\nsubtle={version="=2.6.1",features=["i128","std"]}\nzeroize={version="=1.9.0",features=["alloc","zeroize_derive"]}\n[patch.crates-io]\n'''
for n in ['sha2-0.10.9','digest-0.10.7','block-buffer-0.10.4']:manifest+=n.rsplit('-',1)[0]+'={path="'+str(V/n)+'"}\n'
manifest+= ('[lib]\n' if test else '[[bin]]\nname="split"\n')+'path="'+str(source)+'"\n[profile.release]\noverflow-checks=false\ndebug-assertions=false\n'
(P/'Cargo.toml').write_text(manifest);(O/'Cargo.toml.txt').write_text(manifest)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'classification-target'),CARGO_BUILD_JOBS='4')
meta=subprocess.run(['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--format-version','1'],env=env,capture_output=True,text=True);(O/'metadata.json').write_text(meta.stdout)
if meta.returncode:print(meta.stderr);sys.exit(meta.returncode)
m=json.loads(meta.stdout);features=[dict(id=p['id'],features=next(n['features'] for n in m['resolve']['nodes'] if n['id']==p['id'])) for p in m['packages']]
cmd=['cargo','test' if test else 'run','--manifest-path',str(P/'Cargo.toml'),'--release','--locked','-j','4']
if test:cmd+=['--lib','--','--nocapture','--test-threads=1']
(O/'inputs.json').write_text(json.dumps(dict(command=cmd,env={k:v for k,v in env.items() if k.startswith(('RUST','CARGO'))},features=features,source_pins=pins,fixture=dict(path=str(source),sha256=hashlib.sha256(source.read_bytes()).hexdigest()),profile='release opt3 debug_assertions=false overflow_checks=false',scope='original finite fixture with original private helper suffixes; all registry body prefixes identical to deployed versions; no deployed ELF/machine proof'),indent=2))
print('expected time: optimized test compilation then '+suite+' finite native differential',flush=True);r=subprocess.run(cmd,env=env);sys.exit(r.returncode)
