"""One new bounded Kani contract; admission denial is final for this step."""
from pathlib import Path
import hashlib,json,os,re,runpy,subprocess,time
D=Path(__file__).resolve().parent;O=D/'packet/kani059'
O.mkdir(parents=True,exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cmd=['/usr/bin/timeout','240','/home/dombarker/.cargo/bin/cargo','kani','--manifest-path',str(D/'proof/Cargo.toml'),'--lib','--exact','--harness','ProverRwResumeP6::checks::native_draw_resume_events','--solver','kissat','--output-format','terse','-j','1','-Z','unstable-options','-Z','stubbing','--extra-pointer-checks','--cbmc-args','--unwinding-assertions']
inputs=[p for p in D.rglob('*') if p.is_file() and not any(x in p.relative_to(D).parts for x in ['packet','target','__pycache__'])]
R=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
for n in ['libc-0.2.186','cfg-if-1.0.4']:
 inputs.extend(p for p in (R/n).rglob('*') if p.is_file())
K=Path('/home/dombarker/.kani/kani-0.67.0')
for sub in ['bin','lib','toolchain/bin','toolchain/lib','library']:
 inputs.extend(p for p in (K/sub).rglob('*') if p.is_file())
inputs.extend([K/'rustc-version',K/'rust-toolchain-version'])
inputs.extend(Path(p) for p in ['/usr/bin/time','/usr/bin/timeout','/home/dombarker/.cargo/bin/cargo','/home/dombarker/.cargo/bin/cargo-kani','/home/dombarker/.cargo/bin/rustup'])
pins={str(p):sha(p) for p in sorted(set(inputs))}
pre=dict(schema='ProverRwResumeP6-receipt-v1',attempt=59,command=cmd,target='compact scalar-observer actual prospective native draw/resume normal outcomes and instrumented real Drop observations; universal valid NonZeroI32 errors',source_revision=(D/'revision.txt').read_text().strip(),source_sha256=pins,dependency_fingerprint=hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),expected_phase='optimized compilation, then one symbolic native draw/resume with actual Drop and safe payload snapshots',print_axioms='N/A: Kani, no Lean declarations',semantic_erasure_proved=False,native_world_refinement_proved=False)
(O/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
t=time.monotonic()
before=runpy.run_path(str(D/'reservation.py'))['admission'](requested=4*2**30)
(O/'admission-before.json').write_text(json.dumps(before,indent=2)+'\n')
if not before['allowed']:
 pre.update(exit_status=78,wall_seconds=time.monotonic()-t,peak_rss_kib=None,swaps=None,actual_invocations=0,denial='corrected mandatory admission denied; no further reservations this step')
 (O/'receipt.json').write_text(json.dumps(pre,indent=2)+'\n')
 print(json.dumps({k:v for k,v in pre.items() if k!='source_sha256'}));raise SystemExit(78)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(D/'target'))
scope=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=3G','-p','MemoryMax=4G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(D/'scope.py'),str(O),*cmd]
with (O/'stdout.log').open('w') as out,(O/'stderr.log').open('w') as err:r=subprocess.run(scope,cwd=D,env=env,stdout=out,stderr=err)
s=(O/'time.log').read_text() if (O/'time.log').exists() else ''
def metric(n):
 m=re.search(re.escape(n)+r':\s*(\d+)',s);return int(m[1]) if m else None
post={p:sha(Path(p)) for p in pins}
(O/'postrun.json').write_text(json.dumps(dict(source_sha256=post,unchanged=post==pins),indent=2)+'\n')
pre.update(exit_status=r.returncode,wall_seconds=time.monotonic()-t,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),scope_command=scope,time_log=s,actual_invocations=int((O/'target-started.json').exists()),pins_unchanged=post==pins)
(O/'receipt.json').write_text(json.dumps(pre,indent=2)+'\n')
print(json.dumps({k:pre[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','actual_invocations']}))
raise SystemExit(r.returncode)
