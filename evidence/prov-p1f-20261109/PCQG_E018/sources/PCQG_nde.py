#!/usr/bin/env python3
"""P1f reference-crate extraction controller (runs inside an admitted capped scope).
Rebuilds the historical standalone std-only crate nde_reference (manifest text and source from NDE_extract.py /
the archived NDE_reference.rs; sha256 asserted), runs the original Charon then the rebuilt ORIGINAL Aeneas, with
overflow checks ON (CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true, -C overflow-checks=yes appended to RUSTFLAGS).
The environment otherwise equals NHR_stage.py's (RUSTUP_TOOLCHAIN, RUSTFLAGS -Zthreads=1 ..., jobs 1)."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,subprocess,time,os
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
spec=json.loads((E/(sys.argv[1]+'_spec.json')).read_text());run=spec['run']
assert sha(Path(spec['aeneas_command'][0]).read_bytes())=='959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3','aeneas is not the rebuilt original'
rel=next(l.split(':',2)[2].strip().lstrip('/') for l in Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0:'))
cg=Path('/sys/fs/cgroup')/rel
assert {n:(cg/n).read_text().strip() for n in ('memory.high','memory.max','memory.swap.max','pids.max')}==spec['expected_limits'],'not the admitted capped scope'
src=(E/spec['source_file']).read_bytes();assert sha(src)==spec['reference_sha256'],'source drift'
out=E/(run+'_emitted');out.mkdir(exist_ok=True)
crate=out/'crate';(crate/'src').mkdir(parents=True,exist_ok=True)
manifest='[package]\nname="nde_reference"\nversion="0.1.0"\nedition="2021"\n[workspace]\n'
(crate/'Cargo.toml').write_text(manifest);(crate/'src/lib.rs').write_bytes(src)
assert sha(manifest.encode())==spec['manifest_sha256']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(out/'target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1 -C overflow-checks=yes',RAYON_NUM_THREADS='1',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
res={}
for tool in ('charon','aeneas'):
 cmd=spec[tool+'_command']
 entry=dict(attempt=run,tool=tool,command=cmd,started_unix=time.time(),tool_sha256=sha(Path(cmd[0]).read_bytes()),env_effective={k:env[k] for k in ('RUSTFLAGS','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS','RUSTUP_TOOLCHAIN')})
 with (E/'PCQG_TOOL_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n');f.flush();os.fsync(f.fileno())
 r=subprocess.run(['/usr/bin/time','-v','-o',str(out/(tool+'.time')),*cmd],cwd=(crate if tool=='charon' else out),env=env,capture_output=True,text=True)
 entry.update(exit=r.returncode,wall_seconds=time.time()-entry['started_unix'],stdout_tail=r.stdout[-1500:],stderr_tail=r.stderr[-1500:])
 (out/(tool+'_receipt.json')).write_text(json.dumps(entry,indent=2)+'\n')
 res[tool]=r.returncode
 if r.returncode:break
outs={str(p.relative_to(out)):sha(p.read_bytes()) for p in (out/'raw').rglob('*') if p.is_file()} if (out/'raw').exists() else {}
llbc=out/'repro.llbc'
pins=dict(run=run,spec_id=spec['spec_id'],frozen_validation_note='standalone historical reference crate (not the frozen release source); same source and manifest as P5 emission NML_E012/E006',reference_sha256=spec['reference_sha256'],manifest_sha256=spec['manifest_sha256'],
 tools={Path(spec[k+'_command'][0]).name:sha(Path(spec[k+'_command'][0]).read_bytes()) for k in ('charon','aeneas')},charon_command=spec['charon_command'],aeneas_command=spec['aeneas_command'],
 environment={k:env[k] for k in ('RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','RAYON_NUM_THREADS','RUSTFLAGS','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS')},
 llbc_sha256=sha(llbc.read_bytes()) if llbc.exists() else None,exits=res,output_sha256=outs,p1f=spec.get('p1f'),namespace=spec['namespace'],start_from=spec['start_from'])
(out/(run+'_PINS.json')).write_text(json.dumps(pins,indent=2,sort_keys=True)+'\n')
import shutil
if llbc.exists():(out/'repro.llbc.sha256').write_text(sha(llbc.read_bytes())+'\n');llbc.unlink()
shutil.rmtree(out/'target',ignore_errors=True)
print(json.dumps(dict(attempt=run,exits=res)),flush=True)
sys.exit(max(res.values()) if res else 1)
