"""One fresh precise-drop source observation. NOT accepted Aeneas translation."""
from pathlib import Path
import hashlib,json,os,re,runpy,subprocess,time,tomllib
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
charon=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
cmd=['/usr/bin/python3',str(D/'postrun-host.py')]

# Reuse the same complete input inventory as Kani052, checked before/go.
previous=json.loads((D/'packet/kani054/preflight.json').read_text())
pins=dict(previous['source_sha256'])
lock=str(D/'proof/Cargo.lock')
original=D/'Cargo.lock.precanonical.txt'
assert sha(original)==pins[lock]
def normalized(p):
    x=tomllib.loads(Path(p).read_text());x['package']=sorted(x['package'],key=lambda q:(q['name'],q['version']));return x
assert normalized(original)==normalized(lock)
pins[str(original)]=sha(original);pins[lock]=sha(lock)
for p in pins:assert sha(p)==pins[p],p
for p in [charon,Path(__file__),D/'postrun-host.py',Path('/usr/bin/python3')]:pins[str(p)]=sha(p)
scan=runpy.run_path(str(D/'reservation.py'));before=scan['admission']();assert before['allowed'],before
O=D/'packet/audit002';O.mkdir()
(O/'admission-before.json').write_text(json.dumps(before,indent=2)+'\n')
pre=dict(schema='ProverRwFactoryCleanup-extraction-v1',attempt=2,target='postrun supplemental hashes',command=cmd,source_revision=(D/'revision.txt').read_text().strip(),source_sha256=pins,dependency_fingerprint=hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),print_axioms='N/A: Charon source observation, no Lean emission',expected_phase='read-only postrun binary/artifact hashing; no verification or compilation',accepted_artifact=False)
(O/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(D/'charon-target'),RUSTUP_TOOLCHAIN='nightly-2026-06-01')
scope=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(D/'scope.py'),str(O),*cmd]
t=time.monotonic()
with (O/'stdout.log').open('w') as out,(O/'stderr.log').open('w') as err:r=subprocess.run(scope,cwd=D,env=env,stdout=out,stderr=err)
s=(O/'time.log').read_text() if (O/'time.log').exists() else ''
def metric(n):
 m=re.search(re.escape(n)+r':\s*(\d+)',s);return int(m[1]) if m else None
pre.update(exit_status=r.returncode,wall_seconds=time.monotonic()-t,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),scope_command=scope,time_log=s)
p=D/'ProverRwFactoryCleanup.llbc'
if p.exists():pre['output']=dict(path=str(p),sha256=sha(p),size=p.stat().st_size)
(O/'receipt.json').write_text(json.dumps(pre,indent=2)+'\n')
print(json.dumps({k:pre[k] for k in ['attempt','target','exit_status','wall_seconds','peak_rss_kib','swaps']}))
raise SystemExit(r.returncode)
