#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
b=Path(__file__).resolve().parent;root=b.parents[4];base=root/'docs/research/100bit-spend-path-20261013'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a='header-bytes-a';d=b/'runs'/a;r=json.loads((d/'receipt.json').read_text())
assert r['exit_status']==0
assert r['source_sha256']==sha(d/'source.lean')
assert (base/'lean/ExtractedPrefixHeaderBytes.lean').read_bytes()==(d/'source.lean').read_bytes()
assert r['runner_sha256']==sha(d/'runner.py')
assert r['input_manifest_sha256']==sha(b/('input-manifest-'+a+'.json'))
assert r['limits']=={'memory.max':'8589934592','memory.high':'6442450944','memory.swap.max':'0'}
assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
assert r['memory_events_before']==r['memory_events_after']
assert '-j1' in r['command'] and '-M0' in r['command'] and not r['dependency_rebuild']
assert r['runtime_sha256'] and '4.32.0' in r['lean_version']
log=(d/'lean.log').read_text();reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
assert len(reports)==2
for _,ax in reports:assert set(x.strip() for x in ax.split(',')) <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in log and 'error:' not in log and '_native.' not in log
for line in (b/'SHA256SUMS').read_text().splitlines():
 h,p=line.split('  ',1);assert sha(b/p)==h,p
print('PASS: exact header source, two standard-only audits, runtime/resource/artifact pins')
