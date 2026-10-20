#!/usr/bin/env python3
"""Read-only audit of this additive focused proof packet; never invokes Lean."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
ROOT = PACKET.parents[2]
MODULES = ['R9TwoTransactionExperiment', 'R9QueryScanTransport',
           'R9C3Transport', 'R9SourceLogHandoff', 'R9RejectingScanTransport']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

manifest = json.loads((HERE / 'manifest.json').read_text())
summary = []
for module in MODULES:
    accepted = [a for a in manifest['attempts']
                if a['module'] == module and a['exit'] == 0 and a['final_current']]
    assert len(accepted) == 1, (module, accepted)
    receipt = accepted[0]
    source = PACKET / 'lean' / (module + '.lean')
    text = source.read_text()
    assert sha(source) == receipt['source_sha256'], module
    assert not re.search(r'\b(sorry|admit|native_decide|axiom|maxRecDepth|maxHeartbeats)\b', text), module
    theorems = re.findall(r'^theorem (\w+)', text, re.M)
    audits = re.findall(r'^#print axioms (\w+)', text, re.M)
    assert set(theorems) == set(audits), (module, theorems, audits)
    assert len(receipt['axioms']) == len(audits), module
    for ax in receipt['axioms']:
        match = re.search(r'depends on axioms: \[(.*?)\]', ax, re.S)
        names = {n.strip() for n in match[1].split(',')} if match else set()
        assert names <= ALLOWED, (module, names)
    attempt = HERE / (module + '-' + str(receipt['attempt']))
    assert sha(attempt / 'source.lean.txt') == sha(source)
    assert json.loads((attempt / 'receipt.json').read_text()) == receipt
    assert receipt['swaps'] == 0
    for dep in receipt['direct_imports']:
        assert sha(dep['path']) == dep['sha256'], dep
    summary.append({k: receipt[k] for k in
                    ['module', 'attempt', 'exit', 'wall_seconds', 'peak_rss_bytes', 'swaps']})
    summary[-1]['theorem_audits'] = len(audits)
# All changes from the assigned base must be additive and confined to this packet.
changes = subprocess.check_output(['git', 'diff', '--name-status', '6302ea9d3'], cwd=ROOT, text=True)
allowed_prefixes = [str((PACKET / 'lean' / module).relative_to(ROOT)) for module in MODULES]
allowed_prefixes += [str(HERE.relative_to(ROOT)),
                     str((PACKET / 'design/R9-TRANSPORT-20261021.md').relative_to(ROOT))]
for line in changes.splitlines():
    status, path = line.split('\t', 1)
    assert status == 'A' and any(path.startswith(p) for p in allowed_prefixes), line
print(json.dumps({'status': 'pass', 'scope': 'focused receipts; not a coherent release replay',
                  'targets': summary, 'theorem_audits': sum(a['theorem_audits'] for a in summary)}, indent=2))
