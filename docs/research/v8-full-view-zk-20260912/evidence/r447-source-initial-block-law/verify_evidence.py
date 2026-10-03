#!/usr/bin/env python3
"""Read-only byte/receipt verification for the R442-R447 evidence bundle."""
from pathlib import Path
import hashlib, json, re
HERE=Path(__file__).resolve().parent
DOCROOT=HERE.parent.parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
    if not ok: raise SystemExit('FAIL: '+msg)

# Exact bundle inventory; the index does not checksum itself.
expected={}
for line in (HERE/'SHA256SUMS').read_text().splitlines():
    h,rel=line.split('  ',1); expected[rel]=h
actual={p.relative_to(HERE).as_posix():sha(p) for p in HERE.rglob('*') if p.is_file() and p.name!='SHA256SUMS'}
require(expected==actual,'SHA256SUMS inventory/content mismatch')
manifest=json.loads((HERE/'manifest.json').read_text())
records={r['run_id']:r for r in manifest['records']}
for rid,row in records.items():
    run=HERE/'runs'/rid
    receipt=json.loads((run/'receipt.json').read_text())
    log=(run/'lean.log').read_text()
    for key in ['target','source_revision','source_sha256','exit_status','wall_time','peak_rss_kib','swaps','resources','complete_print_axioms','runner_sha256','direct_local_import_sha256']:
        require(receipt.get(key)==row.get(key),f'{rid} manifest/receipt {key} mismatch')
    require(sha(run/'source.lean')==receipt['source_sha256'],f'{rid} source snapshot mismatch')
    require('Exit status: '+str(receipt['exit_status']) in log,f'{rid} GNU time status mismatch')
    for key,pat in [
        ('wall_time',r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)'),
        ('peak_rss_kib',r'Maximum resident set size \(kbytes\):\s*(\d+)'),
        ('swaps',r'Swaps:\s*(\d+)')]:
        m=re.search(pat,log); require(m is not None,f'{rid} missing raw {key}')
        value=m.group(1) if key=='wall_time' else int(m.group(1))
        require(value==receipt[key],f'{rid} raw GNU {key} mismatch')
    limits=receipt['resources']
    require(limits['MemoryHigh']=='5G' and limits['MemoryMax']=='7G' and limits['MemorySwapMax']==0 and limits['TasksMax']==128 and limits['lean_flags']=='-j1 -M4500',f'{rid} resource limits mismatch')
    reports=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log)
    require(reports==receipt['complete_print_axioms'],f'{rid} axiom print list/log mismatch')
    for imported,h in receipt['direct_local_import_sha256'].items():
        p=HERE/'source'/f'{imported.replace(".","/")}.lean'
        require(p.is_file() and sha(p)==h,f'{rid} direct import {imported} hash mismatch')
    if row['label'].startswith('rejected-'):
        require(receipt['exit_status']!=0,f'{rid} rejected run not failed')
    elif row['label']=='R444-intermediate-scratch-green':
        require(receipt['exit_status']==0 and 'R444InitialSourceLimb' in receipt['target'],f'{rid} intermediate result mismatch')
    else:
        require(receipt['exit_status']==0,f'{rid} successful result failed')
        if rid in {x['run_id'] for x in manifest['successful_targets']}:
            target=DOCROOT/'lean'/receipt['target']
            evidence_source=HERE/'source'/receipt['target']
            require(target.is_file() and sha(target)==receipt['source_sha256'],f'{rid} promoted target mismatch')
            require(evidence_source.is_file() and sha(evidence_source)==receipt['source_sha256'],f'{rid} evidence source mismatch')
            reports_by_name={}
            for text in reports:
                m=re.fullmatch(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)
                require(m is not None,f'{rid} unexpected axiom-free successful declaration report')
                names=[x.strip() for x in m.group(2).split(',') if x.strip()]
                require(set(names)<=set(manifest['axiom_whitelist']),f'{rid} axiom outside whitelist')
                reports_by_name[m.group(1)]=names
            require(len(reports_by_name)==len(receipt['complete_print_axioms']),f'{rid} missing theorem axiom output')

# The runner is one identical focused runner across these receipts.
runner_hash=sha(HERE/'runner/run_focus.py')
require(all(row['runner_sha256']==runner_hash for row in records.values()),'runner hash mismatch')
print(f"PASS: {len(records)} run triples, source chain, promoted targets, exact raw metrics, limits, and complete axioms verified")
