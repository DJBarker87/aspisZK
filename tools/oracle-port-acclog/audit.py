#!/usr/bin/env python3
"""Read-only proof-packet audit; never compiles or writes cached objects."""
from pathlib import Path
import difflib
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT / 'docs/research/100bit-spend-path-20261013'
HERE = PACKET / 'evidence/acclog-draft-20261021'
BASE = '4275d12a7'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def signature(s):
    a = s.index('theorem final_soundness\n')
    return s[a:s.index(' := by', a)] + '\n'

manifest = json.loads((HERE / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
latest = {r['module']: r for r in manifest['attempts'] if r['final_current']}
modules = sorted((PACKET / 'lean').glob('OraclePortAccLog*.lean'))
axiom_reports = 0
theorems = 0
for source in modules:
    module = source.stem
    receipt = latest[module]
    assert receipt['exit'] == 0 and not receipt['errors'], module
    assert receipt['source_sha256'] == sha(source), module
    for key in ['module', 'attempt', 'argv', 'source_revision', 'source_sha256',
                'direct_imports', 'deps_fingerprint', 'wall_seconds', 'peak_rss_bytes', 'swaps', 'axioms']:
        assert key in receipt, (module, key)
    assert '-M4400' in receipt['argv'] and '-j1' in receipt['argv']
    assert '-DElab.async=false' in receipt['argv']
    assert receipt['swaps'] == 0
    log = (ROOT / receipt['log']).read_text()
    assert receipt['axioms'], module
    for report in receipt['axioms']:
        assert report in log
        if 'depends on axioms:' in report:
            axioms = set(re.findall(r'\[([\s\S]*?)\]', report)[0].replace('\n', '').replace(' ', '').split(','))
            assert axioms <= ALLOWED, (module, axioms)
        axiom_reports += 1
    clean = re.sub(r'/-[\s\S]*?-/', '', source.read_text())
    clean = re.sub(r'--[^\n]*', '', clean)
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b', clean), module
    for name in re.findall(r'^theorem\s+(\w+)', clean, re.M):
        assert re.search(r'^#print axioms\s+' + name + r'\s*$', clean, re.M), (module, name)
        assert any("." + name + "'" in a for a in receipt['axioms']), (module, name)
        theorems += 1
    for dep in receipt['direct_imports']:
        obj = Path(dep['path'])
        assert obj.exists() and sha(obj) == dep['sha256'], (module, dep['module'])
    assert sha(Path(receipt['argv'][receipt['argv'].index('-o') + 1])) == receipt['object_sha256']

before = signature((PACKET / 'lean/OraclePortShortCircuitHeadline.lean').read_text())
after = signature((PACKET / 'lean/OraclePortAccLogHeadline.lean').read_text())
assert after == before.replace('OuterExecutionJoin D rust', 'AcceptedRunJoin D rust')
assert before == (HERE / 'headline-before.lean.txt').read_text()
assert after == (HERE / 'headline-after.lean.txt').read_text()
assert (HERE / 'headline-signature.diff').read_text() == ''.join(difflib.unified_diff(
    before.splitlines(True), after.splitlines(True),
    fromfile='OraclePortHeadlineDVsc.final_soundness', tofile='OraclePortHeadlineAccLog.final_soundness'))

changes = subprocess.check_output(['git', 'diff', '--name-status', BASE], cwd=ROOT, text=True).splitlines()
for line in changes:
    status, path = line.split('\t')
    assert status == 'A', line
    assert path.startswith(('docs/research/100bit-spend-path-20261013/lean/OraclePortAccLog',
                            'docs/research/100bit-spend-path-20261013/evidence/acclog-draft-20261021/',
                            'tools/oracle-port-acclog/')) or path == 'docs/research/100bit-spend-path-20261013/design/ACCLOG-DRAFT-20261021.md', line

pins = {}
inputs = ['AGENTS.md', 'docs/research/100bit-spend-path-20261013/design/REFINE-JOIN-DRAFT-20261021.md',
          'docs/research/100bit-spend-path-20261013/design/C3-BIN-20261021.md']
inputs += ['docs/research/100bit-spend-path-20261013/lean/' + m + '.lean' for m in [
    'R1FinalSoundnessBinPerQueryR19', 'OraclePortShortCircuitHeadline', 'OraclePortRuntimeBindingC7',
    'OraclePortStoredExperimentC4', 'OraclePortInnerOrderFrozen', 'OraclePortBatchDraft',
    'BinMerkleTable', 'BinMerkleLeafRecovery', 'RawCutRecordedWordsExecutableBin']]
for source in modules + [ROOT / p for p in inputs]:
    pins[str(source.relative_to(ROOT))] = {'sha256': sha(source), 'size': source.stat().st_size}
(HERE / 'source-pins.json').write_text(json.dumps(pins, indent=2) + '\n')
result = {
    'status': 'pass', 'base': BASE,
    'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'scope': 'additive focused draft; no coherent frozen release replay claimed',
    'modules': len(modules), 'new_theorems': theorems, 'current_axiom_reports': axiom_reports,
    'attempts': len(manifest['attempts']),
    'successes': sum(r['exit'] == 0 for r in manifest['attempts']),
    'failed_attempts': sum(r['exit'] != 0 for r in manifest['attempts']),
    'peak_rss_bytes': max(r['peak_rss_bytes'] for r in manifest['attempts']),
    'swaps': sum(r['swaps'] for r in manifest['attempts']),
    'signature': 'only OuterExecutionJoin D rust replaced by AcceptedRunJoin D rust',
    'actual_frozen_join': 'not proved; accepted raw-slot logs differ',
}
(HERE / 'audit-result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
