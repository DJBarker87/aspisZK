#!/usr/bin/env python3
"""Exact Prefix-into extraction, inside mandatory 6G/8G/swap0 host scope."""
from pathlib import Path
import hashlib,json,os,subprocess,time,sys,signal,shutil,tomllib
root=Path('/home/dombarker/project-offloads/aspis-r1-r18-prefix-20261016')
tool_file=Path(sys.argv[1]);label=sys.argv[2]
tools=json.loads(tool_file.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# The inventory is supplied only after the matching pinned Linux tool build.
assert sha(tool_file)=='b3b5117fb70cda0dfe44968f0e9b2c760dd3f479dfa4b505b41ec7034d489049'
for item in tools['tools'].values():assert sha(Path(item['path']))==item['sha256'],item['path']
for path,digest in tools['rust_runtime_binaries'].items():assert sha(Path(path))==digest,path
charon=Path(tools['tools']['charon']['path']);aeneas=Path(tools['tools']['aeneas']['path'])
out=root/'extraction'/label;out.mkdir(parents=True,exist_ok=False)
(out/'runner.py').write_bytes(Path(__file__).read_bytes());shutil.copy2(tool_file,out/'tool-inventory.json')
shutil.copytree(root/'kit',out/'source');source=out/'source'
pins=json.loads((source/'source-pins.json').read_text())
for f,digest in pins['kit_files'].items():assert sha(source/f)==digest,f
package=tomllib.loads((source/'Cargo.toml').read_text());assert not any('dependencies' in k for k in package)
cg=Path('/sys/fs/cgroup')/next(s.split(':',2)[2] for s in Path('/proc/self/cgroup').read_text().splitlines() if s.startswith('0::')).lstrip('/')
read=lambda k:(cg/k).read_text().strip()
limits={k:read(k) for k in ['memory.high','memory.max','memory.swap.max']}
assert limits=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'},limits
sysroot=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu')
env=dict(os.environ)
for k in ['RUSTC','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','RUSTDOCFLAGS','CARGO_BUILD_TARGET','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(k,None)
extra={'PATH':str(sysroot/'bin')+':/home/dombarker/.cargo/bin:/usr/bin:/bin','LD_LIBRARY_PATH':str(sysroot/'lib'),'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_BUILD_JOBS':'1','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','CARGO_TARGET_DIR':str(root/'extract-target'),'CARGO_NET_OFFLINE':'true','NO_DNA':'1'}
env.update(extra)
(out/'environment.json').write_text(json.dumps(extra,indent=2)+'\n')
(out/'preflight.json').write_text(json.dumps({'cgroup':str(cg),'limits':limits,'events_before':read('memory.events'),'tool_inventory_sha256':sha(tool_file),'runner_sha256':sha(Path(__file__)),'source_pins_sha256':sha(source/'source-pins.json')},indent=2)+'\n')
records=[]
def run(name,command):
 cmd=[str(x) for x in command];start=time.monotonic();peak=0
 with (out/(name+'.log')).open('w') as log:
  p=subprocess.Popen(['/usr/bin/time','-v','-o',str(out/(name+'.time.log')),*cmd],cwd=source,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  while p.poll() is None:
   peak=max(peak,int(read('memory.current')))
   if time.monotonic()-start>180:os.killpg(p.pid,signal.SIGKILL);break
   time.sleep(.1)
  p.wait()
 r={'name':name,'command':cmd,'exit':p.returncode,'wall_seconds':time.monotonic()-start,'sampled_cgroup_bytes':peak,'cgroup_peak_bytes':int(read('memory.peak')),'swap_current_bytes':int(read('memory.swap.current')),'events_after':read('memory.events')}
 records.append(r);(out/'commands.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(r),flush=True)
 if p.returncode:
  print((out/(name+'.log')).read_text()[-6000:],flush=True);raise SystemExit(p.returncode)
try:
 run('charon-version',[charon,'version']);run('aeneas-version',[aeneas,'-version']);run('rustc-version',[sysroot/'bin/rustc','-Vv'])
 run('lock',[sysroot/'bin/cargo','generate-lockfile','--offline'])
 assert len(tomllib.loads((source/'Cargo.lock').read_text())['package'])==1
 run('charon',[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option','--include','core::result::Result','--start-from','crate::r1_wire','--dest-file',out/'PrefixInto.llbc','--','--locked','--offline','--release','--lib','--no-default-features'])
 llbc=json.loads((out/'PrefixInto.llbc').read_text());assert not llbc['has_errors'] and llbc['translated']['ordered_decls']
 run('aeneas',[aeneas,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1PrefixIntoParser','-dest',out/'generated','-subdir','AspisR1PrefixIntoParser','-split-files','-emit-json',out/'PrefixInto.llbc'])
finally:
 (out/'artifact-pins.json').write_text(json.dumps({str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file() and p.name!='artifact-pins.json'},indent=2)+'\n')
