"""Factory-only bounded runner. Unique reservations are charged even on failure."""
from pathlib import Path
import hashlib,json,os,re,runpy,subprocess,sys,time
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
a=int(sys.argv[1]);target=sys.argv[2]
assert 51<=a<=54
assert target in ['zero_nonce','all_outcomes','partial_error']
cmd=['/usr/bin/timeout','240','/home/dombarker/.cargo/bin/cargo','kani','--manifest-path',str(D/'proof/Cargo.toml'),'--lib','--exact','--harness','ProverRwFactoryCleanup::checks::'+target,'--solver','kissat','--output-format','terse','-j','1','-Z','unstable-options','-Z','stubbing','--extra-pointer-checks','--cbmc-args','--unwinding-assertions']
if a>=53 and target=='all_outcomes':
    # Exact source retry loop: at most16 entries; assertion17 checks back-edge
    # completion rather than truncating a feasible trace. All other loops66.
    loop='_RNvMs_NtCsiAUeGDGq3lA_25prover_rw_factory_cleanup22ProverRwFactoryCleanupNtB4_23StateOnlyAttemptSecrets23generate_for_mask_nonce.0'
    cmd+=['--unwindset',loop+':17']
# Read-only admission and input completeness precede charged reservation.
inputs=list((D/'proof').glob('*'))+[D/x for x in ['revision.txt','run.py','scope.py','reservation.py','source-map.json','source.py']]
registry=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
for name in ['zeroize-1.8.1','getrandom-0.3.4','libc-0.2.186','cfg-if-1.0.4']:
 p=registry/name;assert p.is_dir(),p
 inputs+=list(p.rglob('*.rs'))+[p/'Cargo.toml']
inputs += [Path('/home/dombarker/.kani/kani-0.67.0/bin')/x for x in ['kani-driver','kani-compiler','cbmc','goto-instrument','kissat']]
inputs += [Path(x) for x in ['/usr/bin/time','/usr/bin/timeout','/home/dombarker/.cargo/bin/cargo','/home/dombarker/.cargo/bin/rustup']]
assert all(p.is_file() for p in inputs)
pins={str(p):sha(p) for p in inputs}
scanner=runpy.run_path(str(D/'reservation.py'))
before=scanner['admission']();assert before['allowed'],before.get('error',before.get('projected_reserved_bytes'))
E=D/'packet';E.mkdir(exist_ok=True);O=E/f'kani{a:03d}';O.mkdir()
(O/'admission-before.json').write_text(json.dumps(before,indent=2)+'\n')
pre=dict(schema='ProverRwFactoryCleanup-receipt-v1',attempt=a,target=target,command=cmd,source_revision=(D/'revision.txt').read_text().strip(),source_sha256=pins,dependency_fingerprint=hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),print_axioms='N/A: Kani source verification; no Lean declaration',expected_phase='optimized compilation then symbolic concrete factory control/seed verification; actual Drop retained',accepted_artifact=False)
(O/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(D/'target'))
scope=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(D/'scope.py'),str(O),*cmd]
t=time.monotonic()
with (O/'stdout.log').open('w') as out,(O/'stderr.log').open('w') as err:r=subprocess.run(scope,cwd=D,env=env,stdout=out,stderr=err)
s=(O/'time.log').read_text() if (O/'time.log').exists() else ''
def metric(n):
 m=re.search(re.escape(n)+r':\s*(\d+)',s);return int(m[1]) if m else None
pre.update(exit_status=r.returncode,wall_seconds=time.monotonic()-t,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),scope_command=scope,time_log=s)
(O/'receipt.json').write_text(json.dumps(pre,indent=2)+'\n')
print(json.dumps({k:pre[k] for k in ['attempt','target','exit_status','wall_seconds','peak_rss_kib','swaps']}))
raise SystemExit(r.returncode)
