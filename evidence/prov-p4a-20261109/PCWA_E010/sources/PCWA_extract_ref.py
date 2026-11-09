#!/usr/bin/env python3
"""PCWA reference/cut-crate extraction controller (host side, runs inside an admitted capped scope).
Derived from PCO_extract.py (P0) and the reference-crate path of NML_extract.py / NDL_extract.py. Differences, recorded in
PCWA_TOOLS.json: no NHR frozen-stager validation (std-only reference crates need none); the crate directory is rebuilt
from hash-asserted uploaded files; optional frozen-tree staging (spec 'frozen_stage') for isolated crates whose #[path]
modules and aspis-core path dependency live in the frozen tree; every source, lock and tool hash is asserted before and
after the run; Charon and Aeneas run under /usr/bin/time -v; PCWA_<run>_PINS.json records everything."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import importlib.util,json,hashlib,subprocess,time,os,shutil
B=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
spec=json.loads((B/(sys.argv[1]+'_spec.json')).read_text());run=spec['run']
rel=next(l.split(':',2)[2].strip().lstrip('/') for l in Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0:'))
cg=Path('/sys/fs/cgroup')/rel
want=spec['expected_limits']
assert {n:(cg/n).read_text().strip() for n in ('memory.high','memory.max','memory.swap.max','pids.max')}==want,'not the admitted capped scope'
out=B/(run+'_emitted');out.mkdir()
crate=B/(run+'_crate')
assert not crate.exists()
tools={}
for k in ('charon','aeneas'):
    p=Path(spec[k+'_command'][0]);tools[p.name]=sha(p.read_bytes());assert tools[p.name]==spec['tool_sha256'][p.name],('tool drift',p.name)
d=Path(spec['charon_command'][0]).with_name('charon-driver')
if d.exists():tools['charon-driver']=sha(d.read_bytes())
# 1. crate files (hash asserted)
files={}
for relp,info in spec['crate_files'].items():
    data=(B/info['upload']).read_bytes();assert sha(data)==info['sha256'],('upload drift',relp)
    t=crate/relp;t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(data);files[relp]=info['sha256']
# 2. optional frozen staging for isolated crates
stage=spec.get('frozen_stage')
if stage:
    pin=json.loads((B/'PCWA_STAGER_PIN.json').read_text());p=B/'NHR_stage.py';assert sha(p.read_bytes())==pin['sha256'],'stager drift'
    ld=importlib.util.spec_from_file_location('PCWA_private_NHR_stage',p);m=importlib.util.module_from_spec(ld);ld.loader.exec_module(m)
    ws=B/stage['workspace'];m.stage(ws)
    for rl,h in stage['assert_sha256'].items():assert sha((ws/rl).read_bytes())==h,('staged drift',rl)
    for link,target in stage.get('symlinks',{}).items():
        l=B/link
        if not l.exists():l.symlink_to(B/target)
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/spec['target_dir']),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1',**spec.get('env_extra',{}))
log=[]
def measured(tool,cmd,cwd):
    e=dict(attempt=run,tool=tool,command=cmd,cwd=str(cwd),started_unix=time.time(),tool_sha256=sha(Path(cmd[0]).read_bytes()))
    with (B/'PCWA_TOOL_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(e)+'\n');f.flush();os.fsync(f.fileno())
    r=subprocess.run(['/usr/bin/time','-v','-o',str(out/(tool+'.time')),*cmd],cwd=cwd,env=env)
    e.update(exit=r.returncode,wall_seconds=time.time()-e['started_unix'],time_receipt=str(out/(tool+'.time')))
    (out/(tool+'_receipt.json')).write_text(json.dumps(e,indent=2)+'\n');log.append(e);return r.returncode
status=1;error=None;embedded=None
try:
    status=measured('charon',spec['charon_command'],crate if not spec.get('charon_cwd') else B/spec['charon_cwd'])
    llbc=out/'repro.llbc'
    if status==0:
        raw=llbc.read_bytes();doc=json.loads(raw);t=doc.get('translated',doc)
        embedded=[dict(name=f['name'],bytes=len(f['contents']),sha256=sha(f['contents'].encode())) for f in t['files'] if f.get('contents') is not None and 'rustc' not in json.dumps(f['name'])]
        (out/'PCWA_EMBEDDED_SOURCES.json').write_text(json.dumps(dict(llbc_sha256=sha(raw),crate_name=t.get('crate_name'),has_errors=doc.get('has_errors'),files=embedded),indent=1)+'\n')
        assert not doc.get('has_errors'),'Charon reported translation errors'
        status=measured('aeneas',spec['aeneas_command'],B)
except BaseException as ex:
    status=1;error=repr(ex)[:2000]
finally:
    outputs={str(p.relative_to(out)):sha(p.read_bytes()) for p in (out/'raw').rglob('*') if p.is_file()} if (out/'raw').exists() else {}
    after={relp:sha((crate/relp).read_bytes()) for relp in files if (crate/relp).exists()}
    lock=crate/'Cargo.lock'
    pins=dict(run=run,label=spec.get('label'),covers=spec.get('covers'),tools=tools,toolchain='nightly-2026-09-17',charon_command=spec['charon_command'],aeneas_command=spec['aeneas_command'],
      crate_files_sha256=files,crate_files_after_sha256=after,crate_files_unchanged=(after==files),cargo_lock_sha256_after=sha(lock.read_bytes()) if lock.exists() else None,
      controller_sha256=sha(Path(__file__).read_bytes()),spec_sha256=sha((B/(run+'_spec.json')).read_bytes()),
      environment={k:env[k] for k in ('RUSTUP_TOOLCHAIN','CARGO_NET_OFFLINE','CARGO_BUILD_JOBS','RUSTFLAGS','RAYON_NUM_THREADS',*spec.get('env_extra',{}))},
      frozen_stage=stage,embedded_sources=embedded,exit=status,controller_error=error,output_sha256=outputs,original_output_sha256=spec.get('original_outputs'),
      source_provenance=spec.get('source_provenance'))
    (out/('%s_PINS.json'%run)).write_text(json.dumps(pins,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(attempt=run,exit=status,error=error)),flush=True)
sys.exit(status)
