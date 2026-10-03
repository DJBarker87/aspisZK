#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent; DOCS=E.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ck(v,m):
 if not v: raise SystemExit('FAIL: '+m)
m=json.loads((E/'manifest.json').read_text())
for line in (E/'SHA256SUMS').read_text().splitlines():
 h,rel=line.split('  ',1); p=E/rel; ck(p.is_file() and sha(p)==h,'checksum '+rel)
for run in m['runs']:
 d=E/run['label']; r=json.loads((d/'receipt.json').read_text()); log=(d/'log.txt').read_text()
 ck(r['target']==run['target'] and r['source_revision']==m['source_revision'],'target/revision '+run['label'])
 ck(sha(d/'source.lean')==r['source_sha256']==run['source_sha256'],'source '+run['label'])
 if run['label'].startswith('successful'): ck(r['source_sha256']==m['source_sha256'],'successful source sha '+run['label'])
 ck(r['exit_status']==run['exit_status'] and r['wall_time']==run['wall_time'] and r['peak_rss_kib']==run['peak_rss_kib'] and r['swaps']==0==run['swaps'],'metrics '+run['label'])
 ck(f'Exit status: {r["exit_status"]}' in log and f'Elapsed (wall clock) time (h:mm:ss or m:ss): {r["wall_time"]}' in log and f'Maximum resident set size (kbytes): {r["peak_rss_kib"]}' in log and 'Swaps: 0' in log,'raw GNU time '+run['label'])
 ck((d/'command.txt').read_text().strip() in log,'command '+run['label'])
 rr=r['resources']; ck(rr['MemoryHigh']=='5G' and rr['MemoryMax']=='7G' and rr['MemorySwapMax']==0 and rr['TasksMax']==128 and rr['lean_flags']=='-j1 -M4500','resource caps '+run['label'])
 for ax in r['complete_print_axioms']: ck(ax in log,'complete axiom output '+run['label'])
 ck(r['complete_print_axioms']==run['complete_print_axioms'],'axiom manifest '+run['label'])
 ck(sha(d/'receipt.json')==run['receipt_sha256'] and sha(d/'log.txt')==run['log_sha256'],'receipt/log hashes '+run['label'])
 ck(run['exit_status']==(0 if run['label'].startswith('successful') else 1),'success/failure classification '+run['label'])
canonical=DOCS/'lean/AspisV8R19/R468R137ObservedQ22Entry.lean'
ck(canonical.is_file() and sha(canonical)==m['source_sha256'],'canonical source')
ck(sha(E/'runner/run_focus.py')==m['runner_sha256'],'runner')
for mod,item in json.loads((E/'linked-imports.json').read_text())['direct_imports'].items():
 p=(E/item['path']).resolve(); ck(p.is_file() and sha(p)==item['sha256']==m['direct_import_sha256'][mod],'import '+mod)
print('PASS: R468 both successes, four failures, source, receipts, logs, commands, axioms, limits, imports, runner and checksums')
