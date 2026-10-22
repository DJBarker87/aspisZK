"""Inspect retained v7 evidence without running a prover."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 's126-current-caller-20261021/sdk-live-out'
TRACE = BASE / 'receipts/sdk-live-out-shared-bridge-counterexample-v7/stdout.log'
SOURCE = BASE / 'sources/sdk-live-out-shared-v7/src/lib.rs'
rows = json.loads(TRACE.read_text())
result = next(row['result'][0] for row in rows if 'result' in row)
assert result['property'] == 'proofs::actual_sdk_out_bridge.assertion.10'
assert result['status'] == 'FAILURE'
trace = result['trace']
def assignment(lhs, data, function=None):
    return next(step for step in trace if step.get('lhs') == lhs
                and step.get('value', {}).get('data') == data
                and (function is None or step.get('sourceLocation', {}).get('function') == function))
checks = [assignment('initial', '0'), assignment('before', '0'),
          assignment('now', '1'), assignment('var_22', '562949953421336ul'),
          assignment('var_21', 'TRUE'), assignment('var_29', '562949953421328ul'),
          assignment('var_0', 'TRUE', 'sdk_out::{closure#1}::{closure#0}'),
          assignment('borrow', '0', "<std::cell::BorrowRef<'_> as std::ops::Drop>::drop"),
          assignment('var_5.1', 'FALSE', "<std::cell::BorrowRef<'_> as std::ops::Drop>::drop"),
          assignment('var_102', '1')]
source = SOURCE.read_text()
assert '#[kani::stub_verified(sdk_out)]' in source
assert 'out.cast::<[u8;std::mem::size_of::<Reply' in source
full = (BASE / 'receipts/sdk-live-out-shared-bridge-v7/stdout.log').read_text()
assert '2 of 830 failed' in full and 'attempt to subtract with overflow' in full
assert 'assertion failed: unsafe{(*counter).get()} == initial' in full
print(json.dumps({'status': 'retained trace reconciled', 'new_proof': False,
                  'trace_sha256': hashlib.sha256(TRACE.read_bytes()).hexdigest(),
                  'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                  'witness': [{'lhs': s['lhs'], 'value': s['value']['data'],
                               'source': s['sourceLocation']} for s in checks]}, indent=2))
