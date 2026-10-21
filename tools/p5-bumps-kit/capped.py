#!/usr/bin/env python3
"""One immutable Kani attempt; must be inside the required systemd scope."""
import hashlib,json,os,re,subprocess,sys,time
from pathlib import Path
out=Path(sys.argv[1]);assert sys.argv[2]=='--';cmd=sys.argv[3:]
out.mkdir(parents=True,exist_ok=False)
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'},limits
pins=Path('source-pins.json').read_bytes()
inputs={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in Path('.').glob('*.rs')}
rec=dict(schema='p5-kani-attempt-v1',attempt=out.name,module=cmd,source_revision=json.loads(pins)['source_revision'],source_sha256=hashlib.sha256(json.dumps(inputs,sort_keys=True).encode()).hexdigest(),deps_fingerprint=hashlib.sha256(pins).hexdigest(),command=cmd,cwd=os.getcwd(),limits=limits,cgroup=str(cg),inputs=inputs,print_axioms='N/A: Kani proof, no Lean theorem',expected_time='Compile optimized isolated frozen guard slices, then CBMC symbolic address checks; no proof generation or elimination',kani_version=subprocess.check_output([str(Path.home()/'.cargo/bin/cargo-kani'),'--version'],text=True).strip())
start=time.monotonic()
with (out/'stdout.log').open('w') as so,(out/'stderr.log').open('w') as se:
    status=subprocess.run(['/usr/bin/time','-v','-o',str(out/'time.log'),*cmd],stdout=so,stderr=se).returncode
rec.update(exit_status=status,wall_seconds=time.monotonic()-start)
t=(out/'time.log').read_text()
def metric(k):
    m=re.search(re.escape(k)+r':\s*(\d+)',t);return int(m[1]) if m else None
rec.update(peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),cgroup_memory_peak_bytes=int((cg/'memory.peak').read_text()))
log=(out/'stdout.log').read_text();rec['verification_success']='VERIFICATION SUCCESSFUL' in log and 'VERIFICATION FAILED' not in log
rec['errors']=[l for l in (log+(out/'stderr.log').read_text()).splitlines() if any(k in l for k in ['FAILURE','error:','VERIFICATION:-','unwinding assertion','VERIFICATION RESULT'])]
(out/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({k:rec[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','verification_success']}),flush=True)
sys.exit(status)
