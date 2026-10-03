#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys
E=Path(__file__).resolve().parent
DOCS=E.parent.parent
ROOT=DOCS.parents[2]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def check(ok,msg):
    if not ok: raise SystemExit('FAIL: '+msg)
manifest=json.loads((E/'manifest.json').read_text())
for rel,line in (('R464/receipt.json','R464'),('R465/receipt.json','R465')):
    rec=json.loads((E/rel).read_text()); run=next(x for x in manifest['runs'] if x['label']==line)
    prefix=E/line
    check(rec['exit_status']==0 and run['exit_status']==0, line+' successful status')
    check(sha(prefix/'source.lean')==rec['source_sha256']==run['source_sha256'], line+' source hash')
    target=DOCS/'lean'/rec['target']
    check(target.is_file() and sha(target)==rec['source_sha256'], line+' promoted target equality')
    check(rec['source_revision']==manifest['source_revision']==run['source_revision'], line+' revision')
    log=(prefix/'log.txt').read_text()
    check(f'Exit status: {rec["exit_status"]}' in log, line+' raw exit')
    check(f'Elapsed (wall clock) time (h:mm:ss or m:ss): {rec["wall_time"]}' in log, line+' raw wall')
    check(f'Maximum resident set size (kbytes): {rec["peak_rss_kib"]}' in log, line+' raw RSS')
    check('Swaps: 0' in log and rec['swaps']==0, line+' raw swap')
    check('MemoryHigh' in manifest['resources'] and manifest['resources']['MemoryHigh']=='5G' and manifest['resources']['MemoryMax']=='7G' and manifest['resources']['MemorySwapMax']==0 and manifest['resources']['TasksMax']==128 and manifest['resources']['lean_flags']=='-j1 -M4500', line+' limits')
    for report in rec['complete_print_axioms']:
        check(report in log, line+' complete axiom output')
    check(len(rec['complete_print_axioms'])==len(run['complete_print_axioms']), line+' axiom report count')
    for a,b in zip(rec['complete_print_axioms'],run['complete_print_axioms']): check(a==b,line+' axiom receipt equality')
    for mod,entry in json.loads((E/'linked-imports.json').read_text())['linked_direct_imports'][line].items():
        p=(E/entry['path']).resolve()
        check(p.is_file() and sha(p)==entry['sha256'], line+' linked import '+mod)
    check(sha(E/'runner/run_focus.py')==manifest['runner_sha256'],line+' runner hash')
# Verify the explicit package checksum list, excluding itself.
for row in (E/'SHA256SUMS').read_text().splitlines():
    digest,rel=row.split('  ',1); p=E/rel
    check(p.is_file() and sha(p)==digest,'checksum '+rel)
print('PASS: R464/R465 source identity, receipts, logs, axioms, limits, dependencies, runner, and checksums')
