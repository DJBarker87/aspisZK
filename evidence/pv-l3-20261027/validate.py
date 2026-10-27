#!/usr/bin/env python3
"""Check evidence references and source identity; not a constant-time verifier."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
def read(p):return json.loads((E/p).read_text())
pins=read('source-pins.json'); comparison=read('audit-source-comparison-20261027.json')
assert comparison['differences']==[] and comparison['files']==len(pins['sha256'])
for p,sha in pins['sha256'].items():assert hashlib.sha256((R/p).read_bytes()).hexdigest()==sha,p
identity=read('disassembly/identity.json');retained=read('disassembly/retained-binary.json');findings=read('findings.json')
assert identity['sha256']==retained['sha256']==findings['binary_sha256']
assert identity['bytes']==retained['bytes']
asm=(E/'disassembly/selected-disassembly.txt').read_text()
for f in findings['findings']:
 a=f['address'][2:];m=re.search(r'^\s*'+a+r':\s+(.*)$',asm,re.M)
 assert m and m[1]==f['instruction'],f['id']
 assert (R/f['source']).read_text().splitlines()[f['line']-1]==f['source_text'],f['id']
rows=read('disassembly/inventory.json');calls=read('disassembly/call-sites.json')
assert len(rows)==identity['symbols'] and len(calls)==identity['calls']
assert sum(r['instruction_count'] for r in rows)==identity['instructions']
for c in calls:assert any(r['symbol']==c['callee'] and r['start']==c['callee_start'] for r in rows)
for kind in ['build','extract']:
 d=read('receipts/'+kind+'/receipt.json')
 assert d['exit_status']==0 and d['swaps']==d['cgroup_swap_peak_bytes']==0
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert d['cgroup_memory_peak_bytes']<8589934592
assert subprocess.run(['git','diff','--exit-code',pins['revision'],'--','crates','programs','Cargo.toml','Cargo.lock','.cargo'],cwd=R,capture_output=True).returncode==0
out=dict(status='PASS evidence consistency only',source_revision=pins['revision'],source_files=len(pins['sha256']),findings=len(findings['findings']),selected_symbols=len(rows),resolved_incoming_sites=len(calls),shipping_identity_established=False,V373='candidate findings; deployed OPEN',Lean_attempts=0,Kani_attempts=0,print_axioms='N/A: no Lean declarations',source_changes=False)
(E/'validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
