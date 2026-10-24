"""New verified-invariant attempt; immutable inputs and full hierarchical gate."""
from pathlib import Path
import hashlib,json,os,re,runpy,subprocess,sys,time
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
a=int(sys.argv[1]);assert a==57
cmd=['/usr/bin/timeout','240','/home/dombarker/.cargo/bin/cargo','kani','--manifest-path',str(D/'proof-frame/Cargo.toml'),'--lib','--exact','--harness','ProverRwFactoryIterationFrame::checks::all_outcomes','--solver','kissat','--output-format','terse','-j','1','-Z','unstable-options','-Z','stubbing','-Z','loop-contracts','--extra-pointer-checks','--cbmc-args','--unwinding-assertions']
inputs=[p for p in D.rglob('*') if p.is_file() and not any(x in p.parts for x in ['packet','target'])]
registry=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
for name in ['zeroize-1.8.1','getrandom-0.3.4','libc-0.2.186','cfg-if-1.0.4']:
 p=registry/name;assert p.is_dir(),p
 inputs+=list(p.rglob('*.rs'))+[p/'Cargo.toml']
K=Path('/home/dombarker/.kani/kani-0.67.0')
for sub in ['bin','lib','toolchain/bin','toolchain/lib','library']:
 inputs += [p for p in (K/sub).rglob('*') if p.is_file()]
inputs += [K/'rustc-version',K/'rust-toolchain-version']
inputs += [Path(x) for x in ['/usr/bin/time','/usr/bin/timeout','/home/dombarker/.cargo/bin/cargo','/home/dombarker/.cargo/bin/cargo-kani','/home/dombarker/.cargo/bin/rustup']]
pins={str(p):sha(p) for p in sorted(set(inputs))}
meta=json.loads((D/'source-map.json').read_text())
assert sha(D/'production-source.txt')==meta['production_map']['source_sha256']
s=(D/'proof/selected.rs').read_text();assert s.count(meta['annotation'])==1
assert hashlib.sha256(s.replace(meta['annotation'],'').encode()).hexdigest()==meta['erased_selected_sha256']
frame=json.loads((D/'frame-source-map.json').read_text())
f=(D/'proof-frame/selected.rs').read_text()
assert sha(D/'proof-frame/selected.rs')==frame['selected_sha256']
assert f.count(frame['additional_annotation'])==1 and f.count(meta['annotation'])==1
assert hashlib.sha256(f.replace(frame['additional_annotation'],'').replace(meta['annotation'],'').encode()).hexdigest()==frame['erased_selected_sha256']
before=runpy.run_path(str(D/'reservation.py'))['admission']();assert before['allowed'],before
O=D/'packet'/f'kani{a:03d}';O.mkdir(parents=True)
(O/'admission-before.json').write_text(json.dumps(before,indent=2)+'\n')
pre=dict(schema='ProverRwFactoryIteration-receipt-v1',attempt=a,target='actual factory invariant with explicit write set and symbolic coordinate; custom-u16 errors only',command=cmd,source_revision=(D/'frame-revision.txt').read_text().strip(),source_sha256=pins,dependency_fingerprint=hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),print_axioms='N/A: Kani verification, no Lean declaration',expected_phase='optimized compilation then invariant base/step and one symbolic factory iteration, with actual Drop enabled',accepted_artifact=False)
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
