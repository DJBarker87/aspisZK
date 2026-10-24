"""One authorized optimized Rust MIR compile; no Kani/extraction/backend invocation."""
from pathlib import Path
import hashlib,json,os,re,runpy,subprocess,time
D=Path(__file__).resolve().parent;O=D/'packet/rust001';O.mkdir(parents=True,exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
R=Path('/home/dombarker/.kani/kani-0.67.0/toolchain')
rustc=R/'bin/rustc'; cargo=Path('/home/dombarker/.cargo/bin/cargo')
cmd=[str(cargo),'rustc','--offline','--locked','--release','-j','1','--manifest-path',str(D/'proof/Cargo.toml'),'--lib','--','--emit=mir']
inputs=[p for p in D.rglob('*') if p.is_file() and not any(x in p.relative_to(D).parts for x in ['packet','target','__pycache__'])]
registry=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
for n in ['libc-0.2.186','cfg-if-1.0.4']:
 inputs.extend(p for p in (registry/n).rglob('*') if p.is_file())
inputs.extend(p for p in R.rglob('*') if p.is_file())
inputs.extend([cargo,Path('/home/dombarker/.cargo/bin/rustup'),Path('/usr/bin/time')])
pins={str(p):sha(p) for p in sorted(set(inputs))}
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTC=str(rustc),RUSTFLAGS='--cfg prover_rw_resume_scalar -Ccodegen-units=1 -Zdump-mir=all -Zdump-mir-exclude-pass-number -Zdump-mir-dir='+str(D/'mir'),CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(D/'target'))
assert json.loads((D/'packet/readonly/diagnostic.json').read_text())['allowed']
pre=dict(schema='ProverRwResumeMIR-compile-v1',command=cmd,source_revision=(D/'revision.txt').read_text().strip(),source_sha256=pins,dependency_fingerprint=hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),expected_phase='one optimized Rust compilation emitting textual MIR for concrete source-role binding; no runtime or arithmetic gate',environment={k:env[k] for k in ['RUSTC','RUSTFLAGS','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR']},compiler_version=subprocess.check_output([str(rustc),'-vV'],text=True),print_axioms='N/A: Rust compile, no Lean declarations',Kani_invocations=0,native_erasure_proved=False)
(O/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
# Serialize outside the allowed London parallel window, before fresh admission.
import datetime,zoneinfo,fcntl
hm=datetime.datetime.now(zoneinfo.ZoneInfo('Europe/London')).strftime('%H%M')
lock=None
if not (hm>='2230' or hm<'1400'):
 lock=open('/tmp/aspis-r0-lean.lock','a');fcntl.flock(lock,fcntl.LOCK_EX)
pre['global_lock']='/tmp/aspis-r0-lean.lock' if lock else 'in-window'
(O/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
t=time.monotonic();before=runpy.run_path(str(D/'reservation.py'))['admission'](requested=2**30)
(O/'admission-before.json').write_text(json.dumps(before,indent=2)+'\n')
if not before['allowed']:
 pre.update(exit_status=78,wall_seconds=time.monotonic()-t,actual_invocations=0,denial='mandatory admission denied; no further launch attempts')
 (O/'receipt.json').write_text(json.dumps(pre,indent=2)+'\n');raise SystemExit(78)
scope=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=768M','-p','MemoryMax=1G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(D/'scope.py'),str(O),*cmd]
with (O/'stdout.log').open('w') as out,(O/'stderr.log').open('w') as err:r=subprocess.run(scope,cwd=D,env=env,stdout=out,stderr=err)
s=(O/'time.log').read_text() if (O/'time.log').exists() else ''
def metric(n):
 m=re.search(re.escape(n)+r':\s*(\d+)',s);return int(m[1]) if m else None
post={p:sha(Path(p)) for p in pins};(O/'postrun.json').write_text(json.dumps(dict(source_sha256=post,unchanged=post==pins),indent=2)+'\n')
pre.update(exit_status=r.returncode,wall_seconds=time.monotonic()-t,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),scope_command=scope,time_log=s,actual_invocations=int((O/'target-started.json').exists()),pins_unchanged=post==pins)
(O/'receipt.json').write_text(json.dumps(pre,indent=2)+'\n')
print(json.dumps({k:pre[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps','actual_invocations']}))
raise SystemExit(r.returncode)
