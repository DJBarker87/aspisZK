#!/usr/bin/env python3
"""Export only source/text inspection evidence; never export the input LLBC."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import time

R = Path(__file__).resolve().parents[2]
D = Path(__file__).resolve().parent
B = R/'docs/research/100bit-spend-path-20261013'
O = B/'evidence/s126-current-caller-20261021/s6-allocation-backbone-v1'
O.mkdir()
command = [sys.executable, str(D/'inspect.py'), sys.argv[1], '--output', str(O/'inventory.json')]
start = time.monotonic()
with (O/'stdout.log').open('w') as out, (O/'time.log').open('w') as err:
    result = subprocess.run(['/usr/bin/time', '-l', *command], cwd=R, stdout=out, stderr=err)
elapsed = time.monotonic()-start
assert result.returncode == 0
timing = (O/'time.log').read_text()
metric = lambda name: int(re.search(r'(\d+)\s+'+name, timing)[1])
report = json.loads((O/'inventory.json').read_text())
for name, pin in report['release_source_pins'].items():
    value = subprocess.check_output(['git', 'show', report['release_revision']+':'+name], cwd=R)
    assert hashlib.sha256(value).hexdigest() == pin['sha256']
    destination = O/'reviewed-source'/name
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(value)
(O/'receipt.json').write_text(json.dumps({
    'schema': 'focused-extractor-proof-packet-v1', 'target': 'pinned source allocation backbone inspection',
    'classification': 'source-inspection-only', 'command': command,
    'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip(),
    'exit_status': result.returncode, 'wall_seconds': elapsed,
    'peak_rss_bytes': metric('maximum resident set size'), 'swaps': metric('swaps'),
    'python_executable': sys.executable,
    'python_sha256': hashlib.sha256(Path(sys.executable).read_bytes()).hexdigest(),
    'inspector_sha256': hashlib.sha256((D/'inspect.py').read_bytes()).hexdigest(),
    'print_axioms': 'N/A: source inspection, no Lean compilation or proof claim',
    'native_allocation_bound_proved': False, 'enclosing_premises_removed': 0,
}, indent=2)+'\n')
print(json.dumps({'conditional_box_bound': report['conditional_raw_decoder_box_bound'],
                  'reachable_functions': len(report['reachable_functions']),
                  'exact_source_matches': len(report['exact_source_text_matches']),
                  'macro_functions_without_source_text': len(report['no_source_text_functions'])}))
