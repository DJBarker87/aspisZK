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
if name.startswith('libraries-client'):
 manifest=manifest.replace('zeroize={version="=1.8.1",features=["alloc","zeroize_derive"]}', 'zeroize={version="=1.9.0",features=["alloc","zeroize_derive"]}')
 manifest+='generic-array={version="=0.14.7",features=["more_lengths","zeroize"]}\ntypenum={version="=1.20.1",features=["const-generics"]}\ncrypto-common={version="=0.1.7",features=["getrandom","rand_core","std"]}\nsubtle={version="=2.6.1",features=["i128","std"]}\n'
if len(sys.argv)>4:
 manifest=manifest.replace('digest={version="=0.10.7",features=["alloc","const-oid","core-api","mac","oid","std"]}', 'digest="=0.10.7"').replace('zeroize={version="=1.8.1",features=["alloc","zeroize_derive"]}', 'zeroize="=1.8.1"')
(P/'Cargo.toml').write_text(manifest)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN=tc,RUSTC_BOOTSTRAP='1',CARGO_TARGET_DIR=str(D/('library-target-'+tc)),RUSTFLAGS='-Zmir-opt-level=0 --emit=link,mir',CARGO_BUILD_JOBS='4',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0')
meta=['cargo','metadata','--format-version','1','--manifest-path',str(P/'Cargo.toml')];r=subprocess.run(meta,env=env,capture_output=True,text=True);(O/'metadata.json').write_text(r.stdout);(O/'metadata-stderr.log').write_text(r.stderr)
if r.returncode:sys.exit(r.returncode)
cmd=['cargo','build','--manifest-path',str(P/'Cargo.toml'),'-Zbuild-std=std','--target','x86_64-unknown-linux-gnu','-j','4','--message-format=json']
if profile=='release':cmd+=['--release']
(O/'Cargo.toml.txt').write_text(manifest)
(O/'command.json').write_text(json.dumps(dict(argv=cmd,env={k:v for k,v in env.items() if k.startswith(('RUST','CARGO'))}),indent=2));r=subprocess.run(cmd,env=env,capture_output=True,text=True);(O/'cargo-artifacts.jsonl').write_text(r.stdout);print(r.stderr[-3000:])
if r.returncode:sys.exit(r.returncode)
files=[]
for line in r.stdout.splitlines():
 try:art=json.loads(line)
 except Exception:continue
 if art.get('reason')!='compiler-artifact':continue
 lib=art['target']['name']
 if lib not in ['std','core','alloc','sha2','digest','block_buffer','zeroize','generic_array','typenum','crypto_common','subtle','pv_fscan_libraries']:continue
 for filename in art.get('filenames',[]):
  fp=Path(filename)
  if fp.suffix!='.rlib':continue
  p=fp.with_name(fp.name.removeprefix('lib')).with_suffix('.mir')
  if not p.exists():continue
  b=p.read_bytes();(O/p.name).write_bytes(b);files.append(dict(path=p.name,package_id=art['package_id'],features=art['features'],sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
(O/'mir-manifest.json').write_text(json.dumps(files,indent=2));print('dumped libraries',[(x['path'],x['size']) for x in files],flush=True)
