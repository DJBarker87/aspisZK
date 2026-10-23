#!/usr/bin/env python3
"""Finite specification diagnostic; NOT native equivalence or a Kani proof."""
import hashlib
import json
from pathlib import Path
import subprocess
import time

started = time.monotonic()
root = Path(__file__).resolve().parents[2]
source = root / 'programs/r1-cost-probe/src/r1_pool_adapter.rs'
text = source.read_text()
body = text.split('fn stage1(', 1)[1].split('fn stage2(', 1)[0]
anchors = [
    'let mut checkpoint_data = checkpoint_account.try_borrow_mut_data()?;',
    'let public_data = public_account.try_borrow_data()?;',
    'let statement = decode_public_statement_box(&public_data)?;',
    'let proof_data = proof_account.try_borrow_data()?;',
    'checkpoint_data.copy_from_slice(&checkpoint);',
]
positions = [body.index(a) for a in anchors]
assert positions == sorted(positions)

# Follow S2TrustedSdkBorrow.run's shared guard admission/drop rules.
# max=3 is a finite illustration; same equations hold for MAX with MAX-1.
def shared(counter, maximum):
    return counter + 1 if 0 <= counter < maximum else None

maximum = 3
initial = maximum - 1
first = shared(initial, maximum)
old_second = shared(first, maximum)
after_drop = first - 1
new_second = shared(after_drop, maximum)
assert old_second is None and new_second == maximum
assert after_drop == initial
result = {
    'schema': 'adapter-rw-design-diagnostic-v1',
    'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
    'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'scope': 'source-order anchors plus finite abstract shared-counter schedule only',
    'native_execution': False,
    'source_anchors_in_order': anchors,
    'counter_witness': {'maximum': maximum, 'initial': initial, 'overlapping_second': old_second,
                        'immediate_drop_second': new_second},
    'old_pins': {
        'default': '40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0',
        'devnet': '12cb0bc2f8ff3993643638080a3786fdcd941910e5e4dd65ae2937a99290c28f',
        'pool': '121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'},
    'new_pins': None,
    'lean_attempts': 0, 'kani_runs': 0, 'required14_discharged': [],
    'exit': 0, 'wall_seconds': time.monotonic() - started,
    'peak_rss': None, 'swap': None,
    'metrics_note': 'tiny local Python inspection; no build/proof/release gate',
    'axioms': 'not applicable; no theorem compiled',
}
print(json.dumps(result, indent=2))
