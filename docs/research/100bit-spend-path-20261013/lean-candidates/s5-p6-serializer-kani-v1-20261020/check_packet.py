from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for line in (D/'SHA256SUMS').read_text().splitlines():
 h,n=line.split('  ',1);assert sha(D/n)==h,n
m=json.loads((D/'manifest.json').read_text());b=json.loads((D/m['source_binding']).read_text())
assert sha(D/'src/lib.rs')==b['generated_source_sha256']
assert sha(D/m['lean_model_reference'])==m['lean_model_sha256']==b['lean_model']['sha256']
for n in m['native_receipts']:
 r=json.loads((D/n).read_text());assert r['exit_status']==0 and r['swaps']==0 and r['watchdog_abort'] is None and r['source_sha256']==b['generated_source_sha256']
a=json.loads((D/m['kani_admission']).read_text());assert not a['allowed'] and a['not_started']
assert not m['kani_proof_claim'] and not m['new_lean_proof_claim'] and m['modules']==[]
assert not any(f.suffix in ['.olean','.ilean','.ir','.o','.exe','.a','.so','.llbc','.pyc'] for f in D.rglob('*') if f.is_file())
print('PASS: exact pins and native receipts; Kani NOT RUN, no universal or Lean proof claimed')
