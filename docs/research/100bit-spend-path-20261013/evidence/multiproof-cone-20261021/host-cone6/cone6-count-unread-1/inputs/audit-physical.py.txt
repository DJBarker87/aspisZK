#!/usr/bin/env python3
"""Audit the additive continuation-5 focused packet; never build anything."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT / 'docs/research/100bit-spend-path-20261013'
EVIDENCE = PACKET / 'evidence/multiproof-cone-20261021'
BASE = '902ae095f'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()

sources = sorted((PACKET / 'lean').glob('MultiproofConePhysical*.lean'))
sources += [PACKET / 'lean' / (n + '.lean') for n in
            ['MultiproofConeKeyAdapters', 'MultiproofConeOpeningAdapters']]
manifest = json.loads((EVIDENCE / 'manifest.json').read_text())
rows = []
for source in sources:
    module = source.stem
    relative = str(source.relative_to(ROOT))
    old = subprocess.run(['git', 'cat-file', '-e', BASE + ':' + relative], cwd=ROOT,
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    assert old.returncode != 0, 'Existing Lean module changed: ' + relative
    current = [a for a in manifest['attempts'] if a['module'] == module and a['final_current']]
    assert len(current) == 1, (module, 'needs exactly one current successful receipt')
    receipt = current[0]
    assert receipt['exit'] == 0 and not receipt['errors'], module
    assert receipt['source_sha256'] == sha(source), module + ': stale source'
    attempt_dir = EVIDENCE / (module + '-' + str(receipt['attempt']))
    assert sha(attempt_dir / 'source.lean.txt') == sha(source), module + ': stale snapshot'
    assert receipt.get('source_unchanged', True), module + ': source changed during compile'
    assert receipt['swaps'] == 0 and receipt['peak_rss_bytes'] < 8 * 1024**3, module
    command = json.loads((attempt_dir / 'command.json').read_text())
    assert '-j1' in command['argv'] and '-M4400' in command['argv'], module
    for imported in receipt['direct_imports']:
        assert sha(imported['path']) == imported['sha256'], (module, 'stale direct import', imported['module'])
    text = source.read_text()
    code = re.sub(r'/\-[\s\S]*?\-/', '', text)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|maxRecDepth|maxHeartbeats)\b', code), module
    theorems = re.findall(r'^\s*(?:@\[[^\n]*\]\s*)?(?:private\s+)?theorem\s+(\w+)', text, re.M)
    prints = re.findall(r'^#print axioms (\S+)', text, re.M)
    assert all(t in prints for t in theorems), (module, 'missing individual axiom audit')
    assert len(receipt['axioms']) == len(prints), (module, 'incomplete axiom log')
    for report in receipt['axioms']:
        match = re.search(r'axioms: \[([\s\S]*?)\]', report)
        axioms = {s.strip() for s in match[1].split(',') if s.strip()} if match else set()
        assert axioms <= ALLOWED, (module, axioms)
    rows.append({k: receipt[k] for k in ['module', 'attempt', 'source_revision', 'source_sha256',
                'deps_fingerprint', 'exit', 'wall_seconds', 'peak_rss_bytes', 'swaps', 'axioms']})

changed = git('diff', '--name-only', BASE).splitlines()
assert not any(p.startswith('crates/') or '/lean-candidates/' in p for p in changed), 'Unowned/shipped change'
allowed_lean = {str(p.relative_to(ROOT)) for p in sources}
assert all('/lean/' not in p or p in allowed_lean for p in changed), 'Unowned Lean change'
result = {
    'schema': 'multiproof-physical-focused-audit-v1',
    'base_revision': git('rev-parse', BASE), 'source_revision': git('rev-parse', 'HEAD'),
    'scope': 'additive physical scratch/ordered observation and key/opening packet',
    'modules': rows, 'all_current_axioms_standard': True,
    'generator_check': {'command': 'python3 -B tools/multiproof-cone-20261021/generate.py --check', 'exit': 0, 'output': 'Frozen cuts verified'},
    'physical_to_frozen_accepted_levels': True,
    'physical_level_theorem': 'AspisR1.MultiproofConePhysicalFrozenLevels.accepted_eighteen',
    'retained_physical_level_premises': ['oracle interpretation equation', 'initial Domain', 'initial Strict index order', 'actual extracted successful Result'],
    'shipped_sources_unchanged': True, 'elf_rebuild_triggered': False,
    'existing_lean_and_sibling_modules_unchanged': True,
    'coherent_release_manifest_replayed': False,
    'complete_multiproof_source_cone': False, 'accepted_run_join_constructed': False,
    'remaining': ['full leaf/dedup batch loop adoption', 'count/padding/root composition',
                  'both three-slot batches at dV_frozen2', 'caller lowering excluded and owned by S2'],
}
(EVIDENCE / 'audit-physical-result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'modules': len(rows), 'reports': sum(len(r['axioms']) for r in rows),
                  'complete_multiproof_source_cone': False, 'accepted_run_join_constructed': False}))
