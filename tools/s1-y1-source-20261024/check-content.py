#!/usr/bin/env python3
"""Check the compositional content packet; do not rerun unchanged targets."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(Path(__file__).with_name('check.py'))],check=True)
m=json.loads((E/'s1-values-content-targets.json').read_text())
for n,a in m['targets'].items():
 r=json.loads((E/a/'receipt.json').read_text());p=S/(n+'.lean')
 assert r['target']==n and r['exit_status']==0 and r['source_sha256']==sha(p)
 assert r['print_axioms'] and all('sorryAx' not in s for s in r['print_axioms'])
 assert r['swaps']==0 and r['peak_rss_bytes']<4400*1024**2
 assert '-j1' in r['command'] and '-M4400' in r['command']
 for forbidden in ['sorry','native_decide','bv_decide','set_option maxHeartbeats','set_option maxRecDepth','axiom ']:assert forbidden not in p.read_text(),(n,forbidden)
W=E/'s1-y1-source/native-v6';r=json.loads((W/'shipped_claims_all_bytes-receipt/receipt.json').read_text());b=json.loads((W/'source-binding.json').read_text())
assert r['exit_status']==0 and r['swaps']==0 and r['limits']['memory.swap.max']=='0'
assert r['limits']['memory.max']=='8589934592'
assert '0 of 251 failed' in (W/'shipped_claims_all_bytes-receipt/stdout.log').read_text()
assert 'VERIFICATION:- SUCCESSFUL' in (W/'shipped_claims_all_bytes-receipt/stdout.log').read_text()
for f,h in b['files'].items():assert sha(W/f)==h,f
assert b['function']==json.loads((E/'s1-y1-source/native-v5/source-binding.json').read_text())['function']
assert (W/'src/proofs.rs').read_bytes()==Path(__file__).with_name('proofs-v6.rs').read_bytes()
assert not any(json.loads((W/'terminal-process-review.json').read_text()).values())
print(f"Checked {len(m['targets'])} content/caller targets and unchanged native 1856/3712 byte-formula gate; whole frozen caller/SDK transport remains open")
