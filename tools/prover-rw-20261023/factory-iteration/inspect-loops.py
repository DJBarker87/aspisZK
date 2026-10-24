"""Inspect already-produced055 GOTO after timeout, without rerunning verification."""
from pathlib import Path
import hashlib,json,os,re,runpy,subprocess,time
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
artifacts=list((D/'target/kani/x86_64-unknown-linux-gnu/debug/deps').glob('*all_outcomes.out'));assert len(artifacts)==1
binary=Path('/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument')
cmd=[str(binary),'--show-loops',str(artifacts[0])]
pins={str(p):sha(p) for p in [binary,artifacts[0],Path(__file__),D/'scope.py',D/'reservation.py']}
before=runpy.run_path(str(D/'reservation.py'))['admission']();assert before['allowed'],before
O=D/'packet/inspect001';O.mkdir()
(O/'admission-before.json').write_text(json.dumps(before,indent=2)+'\n')
pre=dict(schema='ProverRwFactoryIteration-inspection-v1',target='read-only055 transformed GOTO loops',command=cmd,source_revision=(D/'cut-revision.txt').read_text().strip(),source_sha256=pins,dependency_fingerprint=hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),print_axioms='N/A: read-only GOTO inspection, no theorem',expected_phase='read-only existing binary inspection; no verification/build')
(O/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
scope=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(D/'scope.py'),str(O),*cmd]
t=time.monotonic()
with (O/'stdout.log').open('w') as out,(O/'stderr.log').open('w') as err:r=subprocess.run(scope,cwd=D,stdout=out,stderr=err)
s=(O/'time.log').read_text() if (O/'time.log').exists() else ''
def metric(n):
 m=re.search(re.escape(n)+r':\s*(\d+)',s);return int(m[1]) if m else None
pre.update(exit_status=r.returncode,wall_seconds=time.monotonic()-t,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),scope_command=scope,time_log=s)
(O/'receipt.json').write_text(json.dumps(pre,indent=2)+'\n')
print(json.dumps({k:pre[k] for k in ['target','exit_status','wall_seconds','peak_rss_kib','swaps']}))
raise SystemExit(r.returncode)
