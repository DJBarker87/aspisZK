from pathlib import Path
import json,hashlib,os,subprocess,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');B=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');P=D/'digest-fixture';P.mkdir(exist_ok=True)
b=json.load(open(D/'structural-inputs.json'));reg=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f');V=B/'classification-vendor';pins=[]
for name in ['digest-0.10.7','block-buffer-0.10.4','sha2-0.10.9']:
 for p in (V/name/'src').rglob('*.rs'):
  r=reg/name/'src'/p.relative_to(V/name/'src');raw=r.read_bytes();v=p.read_bytes();assert v.startswith(raw),str(p)
  pins.append(dict(path=str(p),deployed_source=str(r),sha256=hashlib.sha256(raw).hexdigest(),snapshot_sha256=hashlib.sha256(v).hexdigest(),prefix_identical=True,suffix_bytes=len(v)-len(raw)))
for name in ['update-native-resume.rs','default-native-resume.rs','default-reference.rs']:(P/name).write_text(b['tools/pv-dlib-20261028/'+name]['text'])
(P/'split.rs').write_text(b['tools/pv-relink-20261028/v233.rs']['text'])
s='''[package]
name="pv-rdcd-digest"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
sha2="=0.10.9"
digest={version="=0.10.7",features=["alloc","const-oid","core-api","mac","oid","std"]}
block-buffer="=0.10.4"
generic-array={version="=0.14.7",features=["more_lengths","zeroize"]}
typenum={version="=1.20.1",features=["const-generics"]}
crypto-common={version="=0.1.7",features=["getrandom","rand_core","std"]}
subtle={version="=2.6.1",features=["i128","std"]}
zeroize={version="=1.9.0",features=["alloc","zeroize_derive"]}
[patch.crates-io]
'''
for name in ['digest-0.10.7','block-buffer-0.10.4','sha2-0.10.9']:s+=name.rsplit('-',1)[0]+'={path="'+str(V/name)+'"}\n'
s+='''[[test]]
name="update"
path="update-native-resume.rs"
[[test]]
name="default"
path="default-native-resume.rs"
[[bin]]
name="split"
path="split.rs"
[profile.release]
overflow-checks=false
debug-assertions=false
'''
(P/'Cargo.toml').write_text(s)
if not (P/'Cargo.lock').exists():shutil.copy2(B/'src/tools/r1-cost-probe/Cargo.lock',P/'Cargo.lock')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'classification-target'))
m=subprocess.run(['cargo','metadata','--offline','--manifest-path',str(P/'Cargo.toml'),'--format-version','1'],env=env,capture_output=True,text=True);assert m.returncode==0,m.stderr;j=json.loads(m.stdout);(P/'metadata.json').write_text(m.stdout)
features=[dict(id=n['id'],features=n['features']) for n in j['resolve']['nodes']]
(P/'inputs.json').write_text(json.dumps(dict(features=features,source_pins=pins,profile=dict(name='release',opt_level=3,debug_assertions=False,overflow_checks=False,panic='unwind'),toolchain='1.94.1',fixtures={n:hashlib.sha256((P/n).read_bytes()).hexdigest() for n in ['update-native-resume.rs','default-native-resume.rs','default-reference.rs','split.rs']},class_='finite validation only',prefix_scope='Read-only deployed source prefixes plus retained original accessor suffixes; no global cfg(kani)'),indent=2)+'\n')
for action,extra in [('test',['--tests','--','--nocapture','--test-threads=1']),('run',['--bin','split'])]:
 cmd=['cargo',action,'--offline','--locked','--manifest-path',str(P/'Cargo.toml'),'--release','-j','4']+extra
 print('COMMAND',cmd,flush=True);r=subprocess.run(cmd,env=env);assert r.returncode==0,r.returncode
