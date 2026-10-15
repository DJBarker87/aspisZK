"""Validate the new focused-check evidence without executing Lean."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[5]
EVIDENCE = ROOT / 'docs/research/100bit-spend-path-20261013/evidence'
BASE = '136b746805f3438507732622c9b4e50f36bf49f9'

def sha(data):
    return hashlib.sha256(data).hexdigest()

report = {'base': BASE, 'scope': 'Read-only byte/receipt audit; no Lean replay.', 'bundles': []}
for name in ['lean-public-base-projection-20261015', 'lean-public-byte-codec-20261015',
             'lean-public-byte-lengths-20261015', 'lean-semantic-prefix-codec-20261015',
             'lean-typed-prefix-parser-20261015', 'lean-j1-r2-requested-check-20261015']:
    folder = EVIDENCE / name
    checked = set()
    for line in (folder / 'SHA256SUMS').read_text().splitlines():
        expected, relative = line.split('  ', 1)
        assert sha((folder / relative).read_bytes()) == expected, (name, relative)
        checked.add(relative)
    actual = {str(p.relative_to(folder)) for p in folder.rglob('*')
              if p.is_file() and p.name != 'SHA256SUMS'}
    assert actual == checked, (name, actual ^ checked)
    manifest = json.loads((folder / 'source-manifest.json').read_text())
    objects = {}
    for archive in folder.rglob('*.tar.gz'):
        with tarfile.open(archive) as stream:
            for member in stream.getmembers():
                if member.isfile():
                    objects[member.name] = stream.extractfile(member).read()
    targets = manifest.get('targets', [dict(manifest, module=manifest.get('target'))])
    results = []
    for target in targets:
        module = target['module']
        data = (ROOT / target['repository_source']).read_bytes()
        assert sha(data) == target['source_sha256']
        assert data == (folder / 'sources' / (module + '.lean')).read_bytes()
        assert sha(objects[module.replace('.', '/') + '.olean']) == target['object_sha256']
        label = target['green_attempt']
        receipt = json.loads((folder / 'attempts' / (label + '.json')).read_text())
        assert receipt['exit_status'] == 0 and not receipt['killed_for_memory']
        assert receipt['source_sha256'] == sha(data)
        assert data == (folder / 'attempts' / (label + '.source.lean')).read_bytes()
        log = (folder / 'attempts' / (label + '.log')).read_text()
        assert 'sorryAx' not in log and 'error:' not in log and 'error(' not in log
        axes = {n: [x.strip() for x in a.split(',') if x.strip()]
                for n, a in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)}
        assert all(set(a) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in axes.values())
        if 'axiom_reports' in target:
            assert axes == target['axiom_reports']
        rss = int(re.search(r'(\d+)  maximum resident set size', log).group(1))
        wall = float(re.search(r'([\d.]+) real', log).group(1))
        swaps = int(re.search(r'(\d+)  swaps', log).group(1))
        assert rss == target['max_rss_bytes'] and swaps == target['swap_operations'] == 0
        assert wall == target.get('elapsed_wall_seconds_time', target.get('elapsed_wall_clock_seconds'))
        assert receipt['peak_aggregate_rss_kib_sampled'] == target['peak_aggregate_rss_kib_sampled']
        assert receipt['peak_aggregate_rss_kib_sampled'] < 7 * 1024 * 1024
        if name == 'lean-j1-r2-requested-check-20261015':
            original = subprocess.check_output(['git', 'show', BASE + ':' + target['repository_source']], cwd=ROOT)
            assert data == original
        results.append({'module': module, 'source_sha256': sha(data), 'exit_status': 0,
                        'axiom_reports': len(axes), 'wall_seconds': wall, 'max_rss_bytes': rss})
    for module, pin in manifest.get('direct_imports', {}).items():
        assert sha((folder / pin['source']).read_bytes()) == pin['source_sha256']
        assert sha(objects[module.replace('.', '/') + '.olean']) == pin['object_sha256']
    report['bundles'].append({'name': name, 'checksum_members': len(checked), 'targets': results})

Path(__file__).with_name('focused-evidence-audit.json').write_text(json.dumps(report, indent=2) + '\n')
print('PASS:', sum(len(b['targets']) for b in report['bundles']), 'targets;',
      sum(t['axiom_reports'] for b in report['bundles'] for t in b['targets']), 'axiom reports')
