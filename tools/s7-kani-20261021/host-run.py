#!/usr/bin/env python3
"""One capped attempt, with immutable command/source/resource receipt."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
R=Path(__file__).resolve().parents[2]; H=R/'receipts'; H.mkdir(exist_ok=True)
name=sys.argv[1];cmd=sys.argv[2:];O=H/name;O.mkdir()
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'},limits
pins={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for base in ['tools/s7-kani-20261021','crates/aspis-core/src','crates/aspis-r1-cost-probe/src'] for p in (R/base).rglob('*') if p.is_file() and 'target' not in p.parts}
start=time.monotonic()
with (O/'stdout.log').open('w') as so,(O/'stderr.log').open('w') as se:
 ret=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*cmd],cwd=R,stdout=so,stderr=se).returncode
log=(O/'time.log').read_text();metric=lambda n:int(re.search(re.escape(n)+r':\s*(\d+)',log)[1]) if re.search(re.escape(n)+r':\s*(\d+)',log) else None
rec={'schema':'focused-extractor-proof-packet-v1','attempt':name,'target':cmd,'source_revision':(R/'source-revision.txt').read_text().strip(),'source_sha256':pins,'deps_fingerprint':hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),'exit_status':ret,'wall_seconds':time.monotonic()-start,'peak_rss_kib':metric('Maximum resident set size (kbytes)'),'swaps':metric('Swaps'),'print_axioms':'N/A: Rust or translation; no Lean theorem checked','cgroup':str(cg),'limits':limits,'expected_work':os.getenv('S7_EXPECTED','compilation then named harness; no elimination'),'errors_log':'stderr.log'}
(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({k:rec[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(ret)
