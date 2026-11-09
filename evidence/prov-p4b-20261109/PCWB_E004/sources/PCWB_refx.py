#!/usr/bin/env python3
"""PCWB reference-crate extraction controller (host side, runs inside an admitted capped scope).

Re-extracts a recovered reference or cut crate with the recorded Charon/Aeneas commands.  Differences from the frozen
PCO_extract.py (recorded in PCWB_CLASSIFICATIONS.json): the crate is NOT the frozen cost-probe tree; its files are
uploaded, hash-checked here against the spec, and written to a fresh crate directory.  When spec['frozen_workspace'] is
true the unchanged hash-pinned NHR stager stages frozen 4bb3b3f (so a path dependency ../../crates/aspis-core resolves)
and the crate is placed at spec['crate_dir'] inside that workspace.  Every tool invocation is measured with GNU time.
PCWB_<run>_PINS.json records tool hashes, full commands, source hashes, lock hashes and output hashes.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,subprocess,time,os,importlib.util,shutil,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
run=sys.argv[1];spec=json.loads((E/(run+'_spec.json')).read_text());assert spec['run']==run
rel=next(l.split(':',2)[2].strip().lstrip('/') for l in Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0:'))
cg=Path('/sys/fs/cgroup')/rel
want={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'}
assert {n:(cg/n).read_text().strip() for n in want}==want,'not the admitted capped scope'
out=E/(run+'_emitted');out.mkdir(exist_ok=True)
ws=E/(run+'_ws')
if ws.exists():raise SystemExit('workspace exists: never reuse a workspace')
ws.mkdir()
pins=dict(run=run,spec_id=spec['spec_id'],tools={},commands={},frozen=None)
if spec.get('frozen_workspace'):
 p=E/'NHR_stage.py';loader=importlib.util.spec_from_file_location('PCWB_private_NHR_stage',p);m=importlib.util.module_from_spec(loader);loader.loader.exec_module(m)
 manifest=m.stage(ws)
 pins['frozen']=dict(revision=m.REV,stager_sha256=sha(p.read_bytes()),manifest_sha256=sha((E/'NHR_STAGING_MANIFEST.json').read_bytes()),cargo_lock_sha256=sha((ws/'Cargo.lock').read_bytes()),aspis_core_manifest_sha256=sha((ws/'crates/aspis-core/Cargo.toml').read_bytes()))
crate=ws/spec['crate_dir'];crate.mkdir(parents=True,exist_ok=True)
for relp,info in spec['files'].items():
 data=(E/'PCWB_crate'/relp).read_bytes();assert sha(data)==info['sha256'],('source drift',relp)
 t=crate/relp;t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(data)
sub=lambda s:s.replace('{CRATE}',str(crate)).replace('{OUT}',str(out)).replace('{WS}',str(ws))
env=dict(os.environ);env.update({k:sub(v) for k,v in spec['env'].items()})
for n in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(n,None)
def tool(name,cmd,cwd):
 b=Path(cmd[0]);pins['tools'][b.name]=sha(b.read_bytes())
 if name=='charon':
  d=b.parent/'charon-driver'
  if d.exists():pins['tools']['charon-driver']=sha(d.read_bytes())
 entry=dict(attempt=run,tool=name,command=cmd,started_unix=time.time(),tool_sha256=sha(b.read_bytes()))
 with (E/'PCWB_TOOL_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n');f.flush();os.fsync(f.fileno())
 r=subprocess.run(['/usr/bin/time','-v','-o',str(out/(name+'.time'))]+cmd,cwd=cwd,env=env,stdout=open(out/(name+'.stdout'),'w'),stderr=open(out/(name+'.stderr'),'w'))
 entry.update(exit=r.returncode,wall_seconds=time.time()-entry['started_unix'],time_receipt=str(out/(name+'.time')))
 (out/(name+'_receipt.json')).write_text(json.dumps(entry,indent=2)+'\n')
 pins['commands'][name]=cmd
 return r.returncode
status=0;error=None
try:
 ch=[sub(x) for x in spec['charon_command']];ae=[sub(x) for x in spec['aeneas_command']]
 llbc=out/'repro.llbc'
 status=tool('charon',ch,crate)
 if status==0:
  j=json.loads(llbc.read_text())
  if j.get('has_errors'):status=2;error='llbc has_errors'
 if status==0:status=tool('aeneas',ae,out)
except BaseException as e:status=1;error=repr(e)[:2000]
# outputs
outs={}
for p in sorted((out/'raw').rglob('*')) if (out/'raw').exists() else []:
 if p.is_file():outs[str(p.relative_to(out))]=sha(p.read_bytes())
if llbc.exists():
 pins['llbc_sha256']=sha(llbc.read_bytes());(out/'repro.llbc.sha256').write_text(pins['llbc_sha256']+'\n');
 import lzma;(out/'repro.llbc.xz').write_bytes(lzma.compress(llbc.read_bytes(),preset=6));llbc.unlink()
lk=crate/'Cargo.lock'
pins.update(spec_sha256=sha((E/(run+'_spec.json')).read_bytes()),controller_sha256=sha(Path(__file__).read_bytes()),source_sha256={k:v['sha256'] for k,v in spec['files'].items()},
 crate_lock_sha256_after=sha(lk.read_bytes()) if lk.exists() else None,environment={k:sub(v) for k,v in spec['env'].items()},output_sha256=outs,namespace=spec.get('namespace'),exit=status,error=error)
for c,ver in [('rustc',['rustc','--version']),('cargo',['cargo','--version'])]:
 try:pins[c+'_version']=subprocess.run(ver,env=env,capture_output=True,text=True).stdout.strip()
 except Exception as e:pins[c+'_version']=repr(e)
(out/(run+'_PINS.json')).write_text(json.dumps(pins,indent=2,sort_keys=True)+'\n')
# the raw directory is collected as is; remove the staged workspace copy of the frozen tree is NOT done (own scratch, kept)
print(json.dumps(dict(attempt=run,exit=status,error=error)),flush=True)
sys.exit(status)
