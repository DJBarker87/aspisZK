"""One frozen Pool MIR compilation; staging and graph checks precede rustc."""
from pathlib import Path
import importlib.util,json,hashlib,os,subprocess,sys,lzma
B=Path(__file__).resolve().parent;S=B/'NIK_src';O=B/'NIK_M001_artifacts';O.mkdir(exist_ok=True)
stage=B/'NIK_stage/NHR_stage.py'
spec=importlib.util.spec_from_file_location('NIK_stage',stage);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
m.validate(S,O,'/home/dombarker/.cargo/bin/cargo')
features='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit'
env=dict(os.environ,CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_INCREMENTAL='0',RUSTFLAGS='-C codegen-units=1',CARGO_PROFILE_RELEASE_DEBUG='0')
env.pop('RUSTC_WRAPPER',None)
cmd=['/home/dombarker/.cargo/bin/cargo','+1.94.1','metadata','--manifest-path',str(S/'programs/aspis-pool/Cargo.toml'),'--locked','--offline','--format-version','1','--features',features]
r=subprocess.run(cmd,env=env,capture_output=True,text=True);(O/'pool-metadata.stderr').write_text(r.stderr);assert r.returncode==0
doc=json.loads(next(l for l in r.stdout.splitlines() if l.startswith('{')))
raw=json.dumps(doc).encode();(O/'pool-metadata.json.xz').write_bytes(lzma.compress(raw));(O/'pool-metadata.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
pkgs={p['id']:p for p in doc['packages']}
(O/'features.json').write_text(json.dumps([dict(name=pkgs[n['id']]['name'],version=pkgs[n['id']]['version'],features=n['features']) for n in doc['resolve']['nodes']],indent=1))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before=sha(S/'Cargo.lock')
cmd=['/home/dombarker/.cargo/bin/cargo','+1.94.1','rustc','--manifest-path',str(S/'programs/aspis-pool/Cargo.toml'),'-p','aspis-pool','--locked','--offline','--release','--features',features,'--lib','-j1','--target-dir',str(B/'NIK_mir_target'),'--','--emit=mir','-C','codegen-units=1']
(O/'command.json').write_text(json.dumps(dict(command=cmd,lock_before=before,stager_sha256=sha(stage),expected_time='optimized cold compilation; Pool MIR emission; no proof generation or elimination'),indent=1))
try:r=subprocess.run(cmd,cwd=S,env=env)
finally:
 after=sha(S/'Cargo.lock');(O/'lock-check.json').write_text(json.dumps(dict(before=before,after=after,unchanged=after==before)));assert after==before
if r.returncode==0:
 files=list((B/'NIK_mir_target/release/deps').glob('aspis_pool*.mir'));assert len(files)==1
 raw=files[0].read_bytes();(O/'NIK_pool.mir.xz').write_bytes(lzma.compress(raw));(O/'NIK_pool.mir.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
sys.exit(r.returncode)
