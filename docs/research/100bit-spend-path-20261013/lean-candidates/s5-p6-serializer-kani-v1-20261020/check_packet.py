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
a=json.loads((D/m['kani_admission']).read_text());assert a['allowed'] and not a['not_started']
k=m['kani_selected_result'];rc=json.loads((D/k['receipt']).read_text());pf=json.loads((D/k['preflight']).read_text());log=(D/k['log']).read_text()
assert rc['exit_status']==0 and rc['swaps']==0 and rc['scope_swap_peak_bytes']==0 and rc['watchdog_abort'] is None
assert rc['source_sha256']==pf['source_sha256']==b['generated_source_sha256']
assert pf['limits']['memory.swap.max']=='0' and int(pf['limits']['memory.max'])==2*2**30
assert pf['environment']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3' and pf['environment']['CARGO_PROFILE_TEST_OPT_LEVEL']=='3'
assert pf['command'][pf['command'].index('--output-format')+1]=='regular'
assert '--unwinding-assertions' in pf['command'] and not any(t.startswith('--no-') for t in pf['command'])
assert '0 of 188 failed (5 unreachable)' in log and '1 successfully verified harnesses, 0 failures' in log
assert sha(D/m['constant_carrier_binding'])==m['constant_carrier_binding_sha256']
c=json.loads((D/m['constant_carrier_binding']).read_text());assert c['frozen_carrier_equal'] and c['generated_source_sha256']==b['generated_source_sha256']
assert m['kani_proof_claim'] and not m['new_lean_proof_claim'] and m['modules']==[]
assert not any(f.suffix in ['.olean','.ilean','.ir','.o','.exe','.a','.so','.llbc','.pyc'] for f in D.rglob('*') if f.is_file())
print('PASS: exact source pins, native controls and scoped Kani symbolic success; no new Lean or full-runtime proof claimed')
