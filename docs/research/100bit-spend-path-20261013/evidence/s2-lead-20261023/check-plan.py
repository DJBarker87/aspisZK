"""Check S2 planning inventory against the existing Lean interface; no replay."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
LEAN = ROOT / 'docs/research/100bit-spend-path-20261013/lean/S2LeadInterface.lean'
PLAN = ROOT / 'docs/research/100bit-spend-path-20261013/design/S2-LEAD-PLAN-20261023.md'
text = LEAN.read_text().split('structure S2CallerFacts', 1)[1].split('/-- The SDK packet', 1)[0]
fields = re.findall(r'^  (\w+) :', text, re.M)
expected = ['proofBytes', 'publicBytes', 'proofSuffix', 'proofLength', 'checkpointBytes',
            'checkpointLength', 'nodeViews', 'y1Input', 'observerNone', 'reachedPrefix',
            'callOrder', 'accountFrame', 'writtenMetadata', 'oracle']
assert fields == expected, fields
plan = PLAN.read_text()
assert all('| `' + f + '` |' in plan for f in fields)
trust = ['account_data_cell', 'cell_payload', 'cell_counter', 'shared_ok', 'shared_err',
         'exclusive_ok', 'exclusive_err', 'shared_deref', 'exclusive_deref', 'guard_move',
         'shared_drop', 'exclusive_drop', 'error_move_drop', 'borrow_frame', 'guard_liveness']
assert all('| `' + f + '` |' in plan for f in trust)
assert 'No B field, stub or assumption is adopted' in plan
assert 'D157 expressly excludes interior mutability and unsafe' in plan
assert all('`' + name + '`' in plan for name in ['decoded', 'validated', 'encoded', 'firstReturned'])
assert ',+actual' not in plan
print(json.dumps({'status': 'planning inventory reconciled; no proof of obligations',
                  'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                  'required14': fields, 'proposed_trust_fields': trust,
                  'trust_adopted': False, 'prover_launched': False,
                  'plan_sha256': hashlib.sha256(PLAN.read_bytes()).hexdigest(),
                  'interface_sha256': hashlib.sha256(LEAN.read_bytes()).hexdigest()}, indent=2))
