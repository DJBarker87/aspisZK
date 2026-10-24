"""Two charged extraction preflights, no production edits or emitted-Lean edits."""
from pathlib import Path
import hashlib,json,os,re,runpy,subprocess,sys,time
D=Path(__file__).resolve().parent
H=D.parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
a=int(sys.argv[1]);assert a==52
O=D/'packet'/f'extraction{a:03d}';O.mkdir(parents=True)
charon=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
B=H/'native-drop-abi/backend'
binary=B/'candidate-014/main.exe';receipt=B/'ProverRwNativeDropABI-build-014/receipt.json'
assert sha(binary)==json.loads(receipt.read_text())['versioned_binary']['sha256']
llbc=D/'ProverRwFactorySource.llbc'
if a==52:
 cmd=[str(charon),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--precise-drops','--start-from','crate','--opaque','crate::StateOnlyAttemptSecrets::one_draw','--dest-file',str(llbc),'--','--manifest-path',str(D/'preflight/Cargo.toml'),'--offline','--locked','--release','--lib','--jobs','4']
 phase='optimized compilation and precise built-MIR extraction of prospective controller, opaque one_draw; no proof generation'
 flags={'effective_drop_as_no_op':None,'assessment':'Charon precise-drops, no evaluation claim'}
else:
 cmd=[str(binary),'-sequential','-eval-drops','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','ProverRwFactorySource','-dest',str(O/'raw-output'),'-split-files','-emit-json',str(llbc)]
 from drop_flags import assess
 flags=assess(cmd,B/'ProverRwNativeDropABI-build-014/Config.ml.txt',B/'ProverRwNativeDropABI-build-014/Main.ml.txt')
 phase='prospective controller Aeneas translation with real Drop evaluation; existing experimental candidate014, unaccepted'
inputs=[p for p in D.rglob('*') if p.is_file() and not any(x in p.parts for x in ('packet','target'))]
registry=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
for name in ['zeroize-1.8.1','getrandom-0.3.4','libc-0.2.186','cfg-if-1.0.4']:
 p=registry/name;assert p.is_dir();inputs+=list(p.rglob('*.rs'))+[p/'Cargo.toml']
toolchain=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu')
assert toolchain.exists()
inputs += [p for sub in ['bin','lib'] for p in (toolchain/sub).rglob('*') if p.is_file() and p.suffix!='.rlib']
inputs += [charon,binary,receipt,B/'ProverRwNativeDropABI-build-014/Config.ml.txt',B/'ProverRwNativeDropABI-build-014/Main.ml.txt',Path('/usr/bin/time'),Path('/home/dombarker/.cargo/bin/rustup')]
pins={str(p):sha(p) for p in sorted(set(inputs))}
before=runpy.run_path(str(D/'reservation.py'))['admission']()
(O/'admission-before.json').write_text(json.dumps(before,indent=2)+'\n')
pre=dict(schema='ProverRwFactorySource-extraction-v1',attempt=a,target='prospective exact fission controller/helper boundary, not actual production source',command=cmd,source_revision=(D/'revision.txt').read_text().strip(),source_sha256=pins,dependency_fingerprint=hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),print_axioms='N/A: extraction preflight, no Lean theorem',expected_phase=phase,drop_flags=flags,accepted_artifact=False)
(O/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n');assert before['allowed'],{k:v for k,v in before.items() if k not in ('cgroups','docker_visibility','process_visibility')}
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(D/'target'))
scope=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(D/'scope.py'),str(O),*cmd]
t=time.monotonic()
with (O/'stdout.log').open('w') as out,(O/'stderr.log').open('w') as err:r=subprocess.run(scope,cwd=D,env=env,stdout=out,stderr=err)
metrics=(O/'time.log').read_text() if (O/'time.log').exists() else ''
def metric(label):
 m=re.search(re.escape(label)+r':\s*(\d+)',metrics);return int(m[1]) if m else None
pre.update(exit_status=r.returncode,wall_seconds=time.monotonic()-t,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),scope_command=scope,time_log=metrics)
pre['outputs']=[dict(path=str(p),sha256=sha(p),size=p.stat().st_size) for p in ([llbc] if a==52 else list((O/'raw-output').rglob('*'))) if p.is_file()]
pre['postrun_changed_inputs']=[p for p,h in pins.items() if sha(p)!=h]
(O/'receipt.json').write_text(json.dumps(pre,indent=2)+'\n')
print(json.dumps({k:pre[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','postrun_changed_inputs']}))
raise SystemExit(r.returncode)
