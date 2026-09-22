#!/usr/bin/env python3
"""Collect existing public pilot receipts; no builds, wallet files or replay."""
import argparse, hashlib, json, shutil
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--helper', type=Path, required=True)
p.add_argument('--native', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
assert not a.output.exists()
a.output.mkdir()
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def copy(src, relative):
    dest = a.output / relative
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dest)

report = {'base_git_commit': '6f00e7f6c893c3a81bc37526e32d563434d303c8',
          'scope': 'ordinary+image arithmetic ONLY', 'complete_aspis_verifier': False,
          'source_refinement_proved': False, 'fiat_shamir_soundness_proved': False,
          'basis_profile_changed': False, 'stages': {}}
for mode, stage in [('helper', a.helper), ('native', a.native)]:
    m = json.loads((stage / 'r18-stage.json').read_text())
    for name, expected in m['files'].items():
        assert sha(stage / name) == expected, name
    elf = stage / 'sbf-primary/aspis_v8_performance_sbf.so'
    record = {'path': str(stage), 'source_pins_checked': len(m['files']),
              'source_manifest_sha256': sha(stage / 'r18-stage.json'),
              'elf_sha256': sha(elf), 'worlds': {}}
    for name in ['r17-stage.json', 'r17-sbf-probe.json', 'r18-stage.json', 'r21-stage.json', 'sbf-build.log']:
        copy(stage / name, Path(mode) / name)
    assert 'Exit status: 0' in (stage / 'sbf-build.log').read_text()
    for world in range(2):
        svm = stage / f'svm-world{world}'
        metadata = json.loads((svm / 'metadata.json').read_text())
        assert metadata['mode'] == mode and metadata['elf_sha256'] == sha(elf)
        assert sha(Path(metadata['wire'])) == metadata['wire_sha256']
        rows = [json.loads(s) for s in (svm / 'svm.jsonl').read_text().splitlines()]
        assert len(rows) == (20 if mode == 'helper' else 4)
        assert all(r['heap_bytes'] == 262144 and not r['complete_aspis_verifier'] for r in rows)
        honest = [r for r in rows if r['case'] == 'honest']
        assert len(honest) == 2 and {r['cu_limit'] for r in honest} == {1000000,100000000}
        high = next(r for r in honest if r['cu_limit'] == 100000000)
        low = next(r for r in honest if r['cu_limit'] == 1000000)
        assert high['accepted'] and not high['resource_failure']
        assert low['accepted'] if mode == 'native' else (not low['accepted'] and low['resource_failure'] and not low['checked_rejection'])
        negatives = [r for r in rows if r['case'] != 'honest']
        assert all(not r['accepted'] for r in negatives)
        assert all(r['checked_rejection'] and not r['resource_failure'] for r in negatives if r['cu_limit'] == 100000000)
        record['worlds'][str(world)] = {'diagnostic_complete_cu': high['cu'],
            'one_million_cap_accepted': low['accepted'],
            'negative_checked_rejections': sum(r['checked_rejection'] for r in negatives),
            'negative_resource_failures': sum(r['resource_failure'] for r in negatives),
            'negative_cases': len(negatives)}
        for name in ['svm.jsonl', 'time.txt', 'metadata.json']:
            copy(svm / name, Path(mode) / f'svm-world{world}' / name)
        if mode == 'helper':
            host = stage / f'host-world{world}'
            log = (host / 'pilot.log').read_text()
            assert 'R21_SOURCE_DIFF cases=160' in log and 'tampered_message_fields=1926' in log and 'Exit status: 0' in log
            for name in ['compile.log', 'pilot.log', 'metadata.json', 'context.bin', 'generated/helper.bin']:
                copy(host / name, Path(mode) / f'host-world{world}' / name)
    report['stages'][mode] = record
report['ratios'] = [report['stages']['helper']['worlds'][str(w)]['diagnostic_complete_cu'] / report['stages']['native']['worlds'][str(w)]['diagnostic_complete_cu'] for w in range(2)]
assert all(r > 1 for r in report['ratios'])
report['decision'] = 'REJECT this pilot; stop expansion; retain R20 unchanged'
report['execution_scopes'] = {'build_host': 'NUC via Tailscale',
    'build_launch_limits': {'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128},
    'svm_launch_limits': {'MemoryHigh':'2G','MemoryMax':'3G','MemorySwapMax':0,'TasksMax':128},
    'note': 'Limits recorded from launch commands; per-command RSS/time/swaps are in raw logs.'}
(a.output / 'pilot-receipt.json').write_text(json.dumps(report, indent=2) + '\n')
manifest = {str(f.relative_to(a.output)): sha(f) for f in sorted(a.output.rglob('*')) if f.is_file()}
(a.output / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(report, indent=2))
