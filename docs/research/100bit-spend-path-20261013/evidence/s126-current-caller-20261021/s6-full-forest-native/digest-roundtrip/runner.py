#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess,sys,tomllib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');name,crate,harness=sys.argv[1:4];crate=Path(crate)
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'target'),RUSTFLAGS='-C opt-level=3 -Z mir-opt-level=0 -C overflow-checks=yes -C link-arg=-Wl,--threads=1')
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(name+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
cmd=['cargo','kani','--manifest-path',str(crate/'Cargo.toml'),'--lib','--exact','--harness',harness,'--solver','cadical','--no-assertion-reach-checks','-j','1','-Z','unstable-options','--output-format','terse','--harness-timeout',('180' if 'short' in sys.argv[4:] else '600'),'--cbmc-args','--unwinding-assertions']
if len(sys.argv)>4 and sys.argv[4] in ['codegen','codegen-stubbing','codegen-contracts-stubbing']:
 pos=cmd.index('--cbmc-args');cmd[pos:pos]=['--only-codegen']
if len(sys.argv)>4 and sys.argv[4] in ['contracts','contracts-stubbing','codegen-contracts-stubbing']:
 pos=cmd.index('--cbmc-args');cmd[pos:pos]=['-Z','function-contracts']
if len(sys.argv)>4 and sys.argv[4] in ['stubbing','codegen-stubbing','contracts-stubbing','codegen-contracts-stubbing']:
 pos=cmd.index('--cbmc-args');cmd[pos:pos]=['-Z','stubbing']
if len(sys.argv)>5 and sys.argv[5]=='verbose':cmd.insert(2,'--verbose')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def source_pins(root):
 files={}
 for directory,dirs,names in os.walk(root):
  dirs[:]=[d for d in dirs if d not in ['target','.git','.lake']]
  for n in names:
   p=Path(directory)/n
   if p.suffix in ['.rs','.toml','.lock']:files[str(p.relative_to(root))]=sha(p)
 return files
local_dependencies={}
for package,settings in tomllib.loads((crate/'Cargo.toml').read_text()).get('dependencies',{}).items():
 if not isinstance(settings,dict) or 'path' not in settings:continue
 root=Path(settings['path']);root=root if root.is_absolute() else crate/root
 local_dependencies[package]=dict(root=str(root),files=source_pins(root))
patched={}
for package,settings in tomllib.loads((crate/'Cargo.toml').read_text()).get('patch',{}).get('crates-io',{}).items():
 if 'path' not in settings:continue
 root=Path(settings['path']);root=root if root.is_absolute() else crate/root
 patched[package]=dict(root=str(root),files={str(p.relative_to(root)):sha(p) for p in root.rglob('*') if p.is_file() and (p.suffix in ['.rs','.toml','.json'] or p.name=='Cargo.lock')})
# Capture every active local path dependency, including indirect crates,
# before and after the proof. Metadata runs in its own small capped scope.
metadata_cmd=['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','/usr/bin/env','RUSTFLAGS=','cargo','metadata','--manifest-path',str(crate/'Cargo.toml'),'--offline','--format-version','1']
metadata=json.loads(subprocess.check_output(metadata_cmd,text=True))
all_local={p['name']+'@'+p['manifest_path']:dict(root=str(Path(p['manifest_path']).parent),files=source_pins(Path(p['manifest_path']).parent)) for p in metadata['packages'] if p['source'] is None}
(H/(name+'-all-local-before.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',metadata_command=metadata_cmd,dependencies=all_local),indent=2)+'\n')
(H/(name+'-input.json')).write_text(json.dumps(dict(command=cmd,runner_sha256=sha(Path(__file__)),local_dependency_source_pins=local_dependencies,patched_source_pins=patched,crate_source_pins={str(p.relative_to(crate)):sha(p) for p in (crate/'src').rglob('*.rs')},cargo_lock_sha256=sha(crate/'Cargo.lock') if (crate/'Cargo.lock').is_file() else None,source_sha256=sha(crate/'src/lib.rs'),cargo_sha256=sha(crate/'Cargo.toml'),tool_pins={str(p):sha(p) for p in Path('/home/dombarker/.kani/kani-0.67.0/bin').iterdir() if p.is_file()},env={n:os.environ[n] for n in ['RUSTFLAGS','CARGO_BUILD_JOBS','CARGO_TARGET_DIR','CARGO_NET_OFFLINE']},expected_time='Cached optimized native digest codec compilation; actual eight-limb source loop/reference equality or accepted32-byte roundtrip, no stubs, unwind64.'),indent=2)+'\n')
os.chdir(crate)
status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/name),'Exact native digest codec leaf, MIR0/opt3, no child stubs','--',*cmd])
all_unchanged={n:source_pins(Path(row['root']))==row['files'] for n,row in all_local.items()}
(H/(name+'-all-local-after.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',unchanged=all_unchanged,exit_status=status),indent=2)+'\n')
assert all(all_unchanged.values()),all_unchanged
unchanged={n:source_pins(Path(row['root']))==row['files'] for n,row in local_dependencies.items()}
(H/(name+'-dependency-postcheck.json')).write_text(json.dumps(dict(unchanged=unchanged,exit_status=status,qualification='Exact local-path source inventory pinned before codegen/solver and checked unchanged afterward. Registry crates remain pinned by Cargo.lock/toolchain.'),indent=2)+'\n')
assert all(unchanged.values()),unchanged
raise SystemExit(status)
