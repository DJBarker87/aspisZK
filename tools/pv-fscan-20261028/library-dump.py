from pathlib import Path
import os,subprocess,json,sys,shutil,hashlib,lzma
D=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');name,tc,profile=sys.argv[1:4];P=D/'library-probe';P.mkdir(exist_ok=True);O=D/name;O.mkdir(exist_ok=True)
manifest='''[package]
name="pv-fscan-libraries"
version="0.0.0"
edition="2021"
[workspace]
[lib]
path="../std-probe.rs"
[dependencies]
sha2="=0.10.9"
digest={version="=0.10.7",features=["alloc","const-oid","core-api","mac","oid","std"]}
block-buffer="=0.10.4"
zeroize={version="=1.8.1",features=["alloc","zeroize_derive"]}
'''
if len(sys.argv)>4:
 manifest=manifest.replace('digest={version="=0.10.7",features=["alloc","const-oid","core-api","mac","oid","std"]}', 'digest="=0.10.7"').replace('zeroize={version="=1.8.1",features=["alloc","zeroize_derive"]}', 'zeroize="=1.8.1"')
(P/'Cargo.toml').write_text(manifest)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN=tc,RUSTC_BOOTSTRAP='1',CARGO_TARGET_DIR=str(D/('library-target-'+tc)),RUSTFLAGS='-Zmir-opt-level=0 --emit=link,mir',CARGO_BUILD_JOBS='4',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0')
meta=['cargo','metadata','--format-version','1','--manifest-path',str(P/'Cargo.toml')];r=subprocess.run(meta,env=env,capture_output=True,text=True);(O/'metadata.json').write_text(r.stdout);(O/'metadata-stderr.log').write_text(r.stderr)
if r.returncode:sys.exit(r.returncode)
cmd=['cargo','build','--manifest-path',str(P/'Cargo.toml'),'-Zbuild-std=std','--target','x86_64-unknown-linux-gnu','-j','4']
if profile=='release':cmd+=['--release']
(O/'command.json').write_text(json.dumps(dict(argv=cmd,env={k:v for k,v in env.items() if k.startswith(('RUST','CARGO'))}),indent=2));r=subprocess.run(cmd,env=env)
if r.returncode:sys.exit(r.returncode)
files=[]
for p in (Path(env['CARGO_TARGET_DIR'])/'x86_64-unknown-linux-gnu'/('debug' if profile=='dev' else profile)/'deps').glob('*.mir'):
 if any(p.name.startswith(x+'-') for x in ['std','core','alloc','sha2','digest','block_buffer','zeroize','pv_fscan_libraries']):
  b=p.read_bytes();(O/p.name).write_bytes(b);files.append(dict(path=p.name,sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
(O/'mir-manifest.json').write_text(json.dumps(files,indent=2));print('dumped libraries',[(x['path'],x['size']) for x in files],flush=True)
