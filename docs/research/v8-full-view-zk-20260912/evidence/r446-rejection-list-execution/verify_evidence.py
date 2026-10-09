#!/usr/bin/env python3
"""Read-only integrity checks for the prepared R446 compile component."""
from pathlib import Path
import hashlib, json, re
HERE=Path(__file__).resolve().parent
DOCROOT=HERE.parent.parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def req(x,m):
    if not x: raise SystemExit('FAIL: '+m)
manifest=json.loads((HERE/'manifest.json').read_text())
idx={}
for line in (HERE/'SHA256SUMS').read_text().splitlines():
    h,n=line.split('  ',1);idx[n]=h
files={p.relative_to(HERE).as_posix():sha(p) for p in HERE.rglob('*') if p.is_file() and p.name!='SHA256SUMS'}
req(idx==files,'checksum index mismatch')
r=manifest['run_id'];run=HERE/'run';rec=json.loads((run/'receipt.json').read_text());log=(run/'lean.log').read_text()
req(rec['target']==manifest['target'],'target mismatch')
req(rec['source_revision']==manifest['source_revision'],'revision mismatch')
req(rec['source_sha256']==manifest['source_sha256']==sha(run/'source.lean'),'source mismatch')
req(sha(HERE/'source/AspisV8R19/R446RejectionListExecution.lean')==manifest['source_sha256'],'saved source copy mismatch')
req(sha(DOCROOT/'lean'/manifest['target'])==manifest['source_sha256'],'promoted Lean source mismatch')
req(rec['exit_status']==manifest['exit_status']==0 and 'Exit status: 0' in log,'exit status mismatch')
for field,pattern in [('wall_time',r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)'),('peak_rss_kib',r'Maximum resident set size \(kbytes\):\s*(\d+)'),('swaps',r'Swaps:\s*(\d+)')]:
    m=re.search(pattern,log);req(m is not None,'missing raw '+field)
    val=m.group(1) if field=='wall_time' else int(m.group(1))
    req(val==manifest[field]==rec[{'peak_rss_kib':'peak_rss_kib','swaps':'swaps','wall_time':'wall_time'}[field]],field+' mismatch')
req(rec['resources']['MemoryHigh']=='5G' and rec['resources']['MemoryMax']=='7G' and rec['resources']['MemorySwapMax']==0 and rec['resources']['TasksMax']==128 and rec['resources']['lean_flags']=='-j1 -M4500','resource limits mismatch')
reports=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log)
req(reports==rec['complete_print_axioms'],'complete axiom reports differ from receipt')
req(sha(HERE/'runner/run_focus.py')==rec['runner_sha256'],'runner hash mismatch')
for imp,h in manifest['direct_local_import_sha256'].items():
    req(sha(HERE/'source'/f'{imp.replace(".","/")}.lean')==h,imp+' import source mismatch')
print('PASS: R446 source, receipt, GNU time, limits, axioms, runner and direct import verified')
