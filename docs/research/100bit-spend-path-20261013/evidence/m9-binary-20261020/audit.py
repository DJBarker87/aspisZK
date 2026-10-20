#!/usr/bin/env python3
"""Audit accepted focused receipts without repeating any Lean invocation."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
ROOT = PACKET.parents[2]
BASE = '6bb2b9cb1f2517b51763ed09b16b8716d3226caa'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


manifest = HERE / 'manifest.json'
data = json.loads(manifest.read_text())
saved = {(a['module'], a['attempt']): a for a in data['attempts']}
# Preserve the one failed receipt lost when two lock-waiting drivers read the
# manifest before either completed. No Lean rerun; original logs are retained.
for folder in sorted(HERE.glob('Bin*-*')):
    if not (folder / 'time.log').exists():
        raise RuntimeError('Unfinished compile: ' + str(folder))
    command = json.loads((folder / 'command.json').read_text())
    key = command['module'], command['attempt']
    if (folder / 'receipt.json').exists():
        saved[key] = json.loads((folder / 'receipt.json').read_text())
    elif key not in saved:
        timing = (folder / 'time.log').read_text()
        log = (folder / 'lean.log').read_text()
        assert 'error' in log, 'Only failed missing receipts may be reconstructed'
        command.update(exit=1,
                       wall_seconds=float(re.search(r'([\d.]+) real', timing)[1]),
                       peak_rss_bytes=int(re.search(r'(\d+)\s+maximum resident set size', timing)[1]),
                       swaps=int(re.search(r'(\d+)\s+swaps', timing)[1]),
                       axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)", log),
                       log=str((folder / 'lean.log').relative_to(ROOT)),
                       time=str((folder / 'time.log').relative_to(ROOT)),
                       final_current=False,
                       reconstruction='Original command/log/time; wall rounded by /usr/bin/time -l')
        saved[key] = command
data['attempts'] = sorted(saved.values(), key=lambda a: (a['module'], a['attempt']))
modules = sorted(p.stem for p in (PACKET / 'lean').glob('Bin*.lean')
                 if not subprocess.run(['git', 'cat-file', '-e',
                     BASE + ':' + str(p.relative_to(ROOT))], capture_output=True).returncode == 0)
assert len(modules) == 7, modules
final = []
for module in modules:
    source = PACKET / 'lean' / (module + '.lean')
    candidates = [a for a in data['attempts'] if a['module'] == module]
    assert candidates, module
    current = max(candidates, key=lambda a: a['attempt'])
    assert current['exit'] == 0, current
    assert current['source_sha256'] == sha(source), module
    assert current['swaps'] == 0, module
    for a in candidates:
        a['final_current'] = a is current
        folder = HERE / (module + '-' + str(a['attempt']))
        assert a['source_sha256'] == sha(folder / 'source.lean.txt')
    for dep in current['direct_imports']:
        assert sha(dep['path']) == dep['sha256'], dep
    obj = Path('/tmp/codex-cx-m9-binary-20261020-objects') / (module + '.olean')
    assert sha(obj) == current['object_sha256']
    reports = current['axioms']
    assert len(reports) == len(re.findall(r'^#print axioms ', source.read_text(), re.M)), module
    for report in reports:
        if 'depends on axioms:' in report:
            names = set(re.findall(r'\b[A-Za-z_][\w.]*\b', report.split('[', 1)[1]))
            assert names <= ALLOWED, report
    code = re.sub(r'/\-.*?\-/', '', source.read_text(), flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b', code), module
    assert not re.search(r'\b(norm_num|decide)\b', code.replace('by decide', '').replace('by norm_num', '')) or module == 'BinFullPublicSelection'
    final.append({k: current[k] for k in ['module', 'attempt', 'source_sha256',
                 'exit', 'wall_seconds', 'peak_rss_bytes', 'swaps', 'object_sha256', 'object_size']})
changed = subprocess.check_output(['git', 'diff', BASE, '--name-status'], text=True)
assert all(line.startswith('A\t') for line in changed.splitlines()), changed
data['accepted_attempts'] = {a['module']: a['attempt'] for a in final}
data['status'] = 'seven additive model modules checked; deployed completion and coherent release replay remain open'
manifest.write_text(json.dumps(data, indent=2) + '\n')
result = {'base_revision': BASE, 'audit_revision': subprocess.check_output(
          ['git', 'rev-parse', 'HEAD'], text=True).strip(),
          'all_existing_tracked_files_unchanged': True,
          'source_and_direct_import_hashes_match': True,
          'standard_axioms_only': True,
          'accepted_audit_lines': sum(len(a['axioms']) for a in data['attempts'] if a['final_current']),
          'accepted': final,
          'preflight_superseded': 'Cancelled while waiting for lock; no compiler ran',
          'release_scope': 'Focused cached-object evidence, not coherent frozen-manifest replay'}
(HERE / 'audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
