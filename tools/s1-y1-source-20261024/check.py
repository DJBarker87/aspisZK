#!/usr/bin/env python3
"""Validate source-only focused receipts, not replay or frozen-source closure."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(Path(__file__).with_name('adapt-owned.py')),'--check'],check=True)
m=json.loads((E/'s1-values-owned-targets.json').read_text())
for n,a in m['targets'].items():
 p=S/(n+'.lean');r=json.loads((E/a/'receipt.json').read_text())
 assert r['target']==n and r['exit_status']==0 and r['source_sha256']==sha(p),(n,r)
 assert r['print_axioms'] and all('sorryAx' not in x for x in r['print_axioms']),n
 assert r['swaps']==0 and r['peak_rss_bytes']<4400*1024**2,n
 assert '-j1' in r['command'] and '-M4400' in r['command'],n
 for forbidden in ['sorry','native_decide','bv_decide','set_option maxHeartbeats','set_option maxRecDepth','axiom ']:
  assert forbidden not in p.read_text(),(n,forbidden)
W=E/'s1-y1-source/native-v5';binding=json.loads((W/'source-binding.json').read_text())
assert binding['reference_source']==Path(__file__).with_name('owned-v3.rs').read_text()
for file,expected in binding['files'].items():assert sha(W/file)==expected,file
for name in ['shipped_y1_vec_owned_equivalent','shipped_row14_vec_owned_equivalent','shipped_polynomial_vec_owned_equivalent']:
 p=W/(name+'-receipt');r=json.loads((p/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
 assert 'VERIFICATION:- SUCCESSFUL' in (p/'stdout.log').read_text()
 assert r['limits']['memory.swap.max']=='0' and r['limits']['memory.max']=='8589934592'
r=json.loads((W/'shipped_claims_vec_owned_equivalent-receipt/receipt.json').read_text())
assert r['exit_status']!=0 # Historical timeout, deliberately not accepted evidence.
assert sha(W/'src/lib.rs')==sha(E/'s1-y1-source/owned-extraction-v3/src/lib.rs')
for side in ['charon','aeneas']:
 r=json.loads((E/'s1-y1-source/owned-extraction-v3'/(side+'-receipt')/'receipt.json').read_text())
 assert r['exit_status']==0 and r['swaps']==0
for p in (E/'s1-y1-source').rglob('*'):
 if p.is_file():assert p.suffix in ['.json','.log','.rs','.toml','.txt'] or p.name=='Cargo.lock',str(p)
print(f"Checked {len(m['targets'])} current Lean targets, complete reference extraction and three native equivalence gates; no release closure claimed")
