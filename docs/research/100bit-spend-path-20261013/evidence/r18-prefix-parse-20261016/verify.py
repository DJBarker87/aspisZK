#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
b=Path(__file__).resolve().parent;root=b.parents[4];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for suffix in 'abcdefghi':
 a='parse-'+suffix;d=b/'runs'/a;r=json.loads((d/'receipt.json').read_text())
 assert r['exit_status']==(0 if suffix=='i' else 1)
 assert r['source_sha256']==sha(d/'source.lean')
 assert r['runner_sha256']==sha(d/'runner.py')
 assert r['input_manifest_sha256']==sha(b/('input-manifest-'+a+'.json'))
 assert r['limits']=={'memory.max':'8589934592','memory.high':'6442450944','memory.swap.max':'0'}
 assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
 assert '-j1' in r['command'] and '-M0' in r['command'] and not r['dependency_rebuild']
d=b/'runs/parse-i'
assert (root/'docs/research/100bit-spend-path-20261013/lean/ExtractedPrefixParse.lean').read_bytes()==(d/'source.lean').read_bytes()
log=(d/'lean.log').read_text();matches=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
assert len(matches)==3
for _,axioms in matches:assert set(a.strip() for a in axioms.split(',')) <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in log and 'error:' not in log
for line in (b/'SHA256SUMS').read_text().splitlines():
 h,p=line.split('  ',1);assert sha(b/p)==h,p
print('PASS:8 retained failures, full Prefix source,3 standard-only reports, exact focused receipts')
