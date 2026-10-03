#!/usr/bin/env python3
"""Read-only verification for the R448 saved compile component."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent
DOCROOT=HERE.parent.parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def req(ok,msg):
    if not ok: raise SystemExit('FAIL: '+msg)
manifest=json.loads((HERE/'manifest.json').read_text())
expected={}
for line in (HERE/'SHA256SUMS').read_text().splitlines():
    h,r=line.split('  ',1); expected[r]=h
actual={p.relative_to(HERE).as_posix():sha(p) for p in HERE.rglob('*') if p.is_file() and p.name!='SHA256SUMS'}
req(expected==actual,'checksum index mismatch')
run=HERE/'run';rec=json.loads((run/'receipt.json').read_text());log=(run/'lean.log').read_text()
for key in ['target','source_revision','source_sha256','run_id','exit_status','wall_time','peak_rss_kib','swaps','limits','axioms','direct_local_import_sha256']:
    mapping={'run_id':None,'limits':'resources','axioms':'complete_print_axioms','direct_local_import_sha256':'direct_local_import_sha256'}
    if key=='run_id': continue
    receipt_key=mapping.get(key,key)
    val=rec.get(receipt_key)
    if key=='limits':
        expected_limits=manifest[key]
        for k,v in expected_limits.items(): req(val[k]==v,f'receipt resource {k} mismatch')
    elif key=='axioms':
        req(len(val)==1 and "'AspisV8R19.R448RefillSourceLimb.limbRun_refill_scanAt' depends on axioms: [propext, Quot.sound]" in val,f'receipt axioms mismatch')
    else: req(val==manifest[key],f'receipt {key} mismatch')
source=DOCROOT/'lean'/manifest['target']
req(sha(run/'source.lean')==manifest['source_sha256']==sha(source),'R448 source identity mismatch')
req('Exit status: 0' in log,'GNU exit status mismatch')
for k,pat in [('wall_time',r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)'),('peak_rss_kib',r'Maximum resident set size \(kbytes\):\s*(\d+)'),('swaps',r'Swaps:\s*(\d+)')]:
    m=re.search(pat,log);req(m is not None,f'missing GNU {k}')
    v=m.group(1) if k=='wall_time' else int(m.group(1));req(v==manifest[k],f'GNU {k} mismatch')
req(sha(HERE/'runner/run_focus.py')==rec['runner_sha256'],'runner hash mismatch')
imp='AspisV8R19.R444InitialSourceLimb'; dep=DOCROOT/'lean'/f'{imp.replace(".","/")}.lean'; prev=HERE.parent/'r447-source-initial-block-law/source'/f'{imp.replace(".","/")}.lean'
want=manifest['direct_local_import_sha256'][imp]
req(sha(dep)==want and sha(prev)==want,'R444 direct import source/evidence hash mismatch')
req((manifest['exit_status']==0 and manifest['swaps']==0),'manifest status mismatch')
print('PASS: R448 source, run metrics, caps, axioms, runner and linked R444 source verified')
