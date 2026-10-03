#!/usr/bin/env python3
from pathlib import Path
import hashlib, json
E=Path(__file__).resolve().parent; DOCS=E.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def check(v,m):
 if not v: raise SystemExit('FAIL: '+m)
manifest=json.loads((E/'manifest.json').read_text())
for row in (E/'SHA256SUMS').read_text().splitlines():
 h,rel=row.split('  ',1); p=E/rel; check(p.is_file() and sha(p)==h,'checksum '+rel)
labels=['successful']+[f'failed-{i}' for i in range(1,7)]
for label in labels:
 d=E/label; rec=json.loads((d/'receipt.json').read_text()); log=(d/'log.txt').read_text()
 check(rec['target']=='AspisV8R19/R467R137ObservedSqueeze.lean',label+' target')
 check(sha(d/'source.lean')==rec['source_sha256'],label+' source hash')
 check(f'Exit status: {rec["exit_status"]}' in log,label+' exit')
 check(f'Elapsed (wall clock) time (h:mm:ss or m:ss): {rec["wall_time"]}' in log,label+' wall')
 check(f'Maximum resident set size (kbytes): {rec["peak_rss_kib"]}' in log,label+' RSS')
 check('Swaps: 0' in log and rec['swaps']==0,label+' swap')
 check((d/'command.txt').read_text().strip() in log,label+' command')
 r=rec['resources']; check(r['MemoryHigh']=='5G' and r['MemoryMax']=='7G' and r['MemorySwapMax']==0 and r['TasksMax']==128 and r['lean_flags']=='-j1 -M4500',label+' limits')
 for ax in rec.get('complete_print_axioms',[]): check(ax in log,label+' full axiom output')
s=json.loads((E/'successful/receipt.json').read_text()); target=DOCS/'lean'/s['target']
check(target.is_file() and sha(target)==s['source_sha256'],'canonical source identity')
check(s['exit_status']==0 and s['source_revision']==manifest['source_revision'],'successful receipt')
check(s['complete_print_axioms']==manifest['successful_complete_print_axioms'],'successful full axioms')
check(sha(E/'runner/run_focus.py')==manifest['runner_sha256'],'runner hash')
for mod,item in json.loads((E/'linked-imports.json').read_text())['direct_imports'].items():
 p=(E/item['path']).resolve(); check(p.is_file() and sha(p)==item['sha256']==manifest['direct_import_sha256'][mod],'direct import '+mod)
for i in range(1,7):
 rec=json.loads((E/f'failed-{i}'/'receipt.json').read_text()); check(rec['exit_status']==1,f'failed-{i} status')
 check(any('sorryAx' in ax for ax in rec['complete_print_axioms']),f'failed-{i} history classification')
print('PASS: R467 success and six failed attempts; source, logs, receipts, commands, axioms, imports, runner, checksums')
