"""Collect focused receipts; --check validates the final packet without replaying Lean."""
import hashlib
import json
import re
import sys
from pathlib import Path

EV = Path(__file__).resolve().parents[1]
WT = EV
while not (WT / '.git').exists():
    WT = WT.parent
manifest = json.loads((EV / 'manifest.json').read_text())
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
check = '--check' in sys.argv
receipts = []
for entry in manifest['modules']:
    src = WT / entry['source']
    sha = hashlib.sha256(src.read_bytes()).hexdigest()
    path = EV / entry['module'] / 'receipt.json'
    theorems = re.findall(r'^\s*(?:private )?theorem\s+(\w+)', src.read_text(), re.M)
    entry['theorems'] = theorems
    entry['source_sha256'] = sha
    if not path.exists():
        entry['status'] = 'pending_compile'
        if check:
            raise AssertionError(f'missing receipt: {src}')
        continue
    rec = json.loads(path.read_text())
    green = rec['exit_status'] == 0 and rec['source_sha256'] == sha
    if green:
        names = [re.search(r"'([^']+)'", a).group(1).split('.')[-1] for a in rec['axioms']]
        assert sorted(names) == sorted(theorems), (entry['module'], names, theorems)
        for a in rec['axioms']:
            deps = re.search(r'\[([^\]]*)\]', a)
            assert not deps or set(deps.group(1).replace('\n', '').replace(' ', '').split(',')) <= allowed, a
        assert not rec['errors']
        obj = Path(rec['command'][rec['command'].index('-o') + 1])
        assert hashlib.sha256(obj.read_bytes()).hexdigest() == rec['object_sha256']
        assert obj.stat().st_size == rec['object_size_bytes']
        for dep in rec['direct_imports']:
            obj = Path(dep['object_path'])
            assert hashlib.sha256(obj.read_bytes()).hexdigest() == dep['object_sha256'], dep
        assert rec['wall_seconds'] is not None and rec['peak_rss_bytes'] is not None
        assert rec['process_swap_count'] == 0
    elif check:
        raise AssertionError(f'stale or failed receipt: {src}')
    entry['status'] = 'compiled' if green else 'failed_or_stale'
    entry['receipt'] = str(path.relative_to(EV))
    for key in ['exit_status', 'wall_seconds', 'peak_rss_bytes', 'process_swap_count', 'axioms']:
        entry[key] = rec[key]
    receipts.append(str(path.relative_to(EV)))
manifest['compiled_modules'] = sum(e['status'] == 'compiled' for e in manifest['modules'])
manifest['receipts'] = receipts
manifest['source_revision_parent'] = 'd217103e1d4e249e738321716e107b25529d2618'
manifest['status'] = 'verified_model_with_documented_obstruction' if manifest['compiled_modules'] == len(manifest['modules']) else 'verification_in_progress'
manifest['obstructions'] = [s for s in manifest['obstructions'] if 'memory' not in s]
manifest['historical_memory_preflight'] = manifest.pop('memory_preflight', manifest.get('historical_memory_preflight'))
manifest['release_evidence'] = False
manifest['model_verification_complete'] = manifest['compiled_modules'] == len(manifest['modules'])
manifest['release_evidence_note'] = 'No end-to-end source/release claim; model verification is complete when all focused receipts are current.'
manifest['scope'] = 'Model-level proofs; source extraction/refinement and universal tag separation are not claimed.'
manifest['failed_attempt_receipts'] = sorted(str(p.relative_to(EV)) for p in EV.glob('*/attempt-*/receipt.json'))
if not check:
    (EV / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(f"{manifest['compiled_modules']}/{len(manifest['modules'])} modules current; {sum(len(e['theorems']) for e in manifest['modules'])} theorems; {len(manifest['failed_attempt_receipts'])} preserved failed attempts")
