#!/usr/bin/env python3
"""Check the sole premise deletion, exact proof reuse, and focused receipt."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
ROOT = PACKET.parents[2]
BASE = '400d0cd42683d8aec6b5864a651d7dba74c4fd85'
MODULE = 'R1FinalSoundnessBinPerQueryR18'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def signature(code):
    start = code.index('theorem final_soundness')
    return code[start:code.index(' := by', start)]


old = (PACKET / 'lean/R1FinalSoundnessBinPerQueryRow31.lean').read_text()
per = (PACKET / 'lean/R1FinalSoundnessBinPerQuery.lean').read_text()
source = PACKET / 'lean' / (MODULE + '.lean')
new = source.read_text()
before, after = signature(old), signature(new)
start = before.index('    /- R18:')
end = before.index('    /- R19', start)
assert after == before[:start] + before[end:]
assert 'h_R18' not in new
assert re.findall(r'^abbrev .+$', old, re.M) == re.findall(r'^abbrev .+$', new, re.M)
row_body = old.split(' := by\n', 1)[1].split(
    '  exact R1FinalSoundnessBinPerQuery.final_soundness')[0]
per_body = per.split(' := by\n', 1)[1].split('/-- No larger initial')[0].rstrip()
assert 'h_R18' not in per_body
assert new.split(' := by\n', 1)[1].split('\n\n#print axioms')[0] == (
    row_body + per_body.replace('h_R4_row31 H ha', 'hrow31 H ha'))
report = (PACKET / 'design/R18-TAG-20261021.md').read_text()
assert before in report and after in report
diff = ''.join(difflib.unified_diff(
    (before + '\n').splitlines(True), (after + '\n').splitlines(True),
    fromfile='R1FinalSoundnessBinPerQueryRow31.final_soundness',
    tofile=MODULE + '.final_soundness'))
(HERE / 'signature.diff').write_text(diff)

manifest = json.loads((HERE / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
assert len(manifest['attempts']) == 1
a = manifest['attempts'][0]
folder = HERE / (MODULE + '-1')
assert a['module'] == MODULE and a['attempt'] == 1
assert a['exit'] == 0 and a['swaps'] == 0 and a['final_current']
assert a['errors'] == []
assert a['source_sha256'] == sha(source) == sha(folder / 'source.lean.txt')
assert a == json.loads((folder / 'receipt.json').read_text())
assert all(a[k] == v for k, v in json.loads((folder / 'command.json').read_text()).items())
assert a['deps_fingerprint'] == hashlib.sha256(
    json.dumps(a['direct_imports'], sort_keys=True).encode()).hexdigest()
for dep in a['direct_imports']:
    assert dep['sha256'] == sha(dep['path'])
    candidates = [Path(p) / (dep['module'].replace('.', '/') + '.olean')
                  for p in a['lean_path'].split(':')]
    assert next(str(p) for p in candidates if p.exists()) == dep['path']
obj = Path('/tmp/codex-cx-r18-tag-20261021-objects') / (MODULE + '.olean')
assert a['object_sha256'] == sha(obj) and a['object_size'] == obj.stat().st_size
assert a['argv'][1:4] == ['-j1', '-M4400', '-DElab.async=false']
assert a['lean_path'].split(':')[0] == str(obj.parent)
assert re.findall(r'^theorem (\w+)', new, re.M) == ['final_soundness']
assert re.findall(r'^#print axioms (\w+)', new, re.M) == ['final_soundness']
assert len(a['axioms']) == 1
assert MODULE + ".final_soundness'" in a['axioms'][0]
assert set(re.findall(r'[\w.]+', a['axioms'][0].split('[', 1)[1])) <= ALLOWED
assert a['axioms'][0] in (folder / 'lean.log').read_text()
for field in ['argv', 'source_revision', 'source_sha256', 'exit',
              'wall_seconds', 'peak_rss_bytes', 'swaps', 'axioms']:
    assert field in a
stripped = re.sub(r'/\-.*?\-/', '', new, flags=re.S)
stripped = re.sub(r'--[^\n]*', '', stripped)
assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b', stripped)
inspection = json.loads((HERE / 'inspection.json').read_text())
for entry in inspection['files']:
    assert entry['sha256'] == sha(ROOT / entry['path'])
changes = subprocess.check_output(
    ['git', 'diff', BASE, '--name-status'], cwd=ROOT, text=True).splitlines()
assert all(line.startswith('A\t') for line in changes), changes
assert len(subprocess.check_output(
    ['git', 'diff', BASE, '--', str(PACKET / 'lean')], cwd=ROOT, text=True)) > 0
result = {
    'status': 'PASS', 'base': BASE,
    'audit_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'scope': 'Focused cached-object proof evidence; coherent frozen release replay remains separate',
    'endpoint_only_removes_h_R18': True,
    'new_or_replacement_endpoint_premises': [],
    'same_abbreviations_and_complete_conclusion': True,
    'proof_reuses_row31_derivation_and_per_query_body': True,
    'existing_tracked_files_unchanged': True,
    'standard_axioms_only': True,
    'accepted': {k: a[k] for k in ['module', 'attempt', 'source_revision',
        'source_sha256', 'deps_fingerprint', 'exit', 'wall_seconds',
        'peak_rss_bytes', 'swaps', 'axioms', 'errors']},
}
(HERE / 'audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
