import hashlib
import json
import pathlib
import re
import tarfile

BASE = pathlib.Path('/private/tmp')
NAMES = ['aspis-r1-mask-rawposeidon-callback-bridge-20261016',
         'aspis-r1-mask-extension-evidence-20261016']
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def filehash(path):
    return digest(path.read_bytes())

result = {'schema': 'aspis-terminal-row-bridges-root-audit.v1', 'bundles': [],
          'scope': 'Independent checksum, source/receipt/output, raw axiom log, resource receipt, and represented dependency-edge review. This is not a new Lean replay or a complete source/security theorem.'}
all_objects = {}
all_sources = {}
green = []
for name in NAMES:
    root = BASE / name
    count = 0
    for line in (root / 'SHA256SUMS').read_text().splitlines():
        expected, rel = line.split('  ', 1)
        assert not pathlib.Path(rel).is_absolute() and '..' not in pathlib.Path(rel).parts
        assert filehash(root / rel) == expected, (name, rel)
        count += 1
    manifest = json.loads((root / 'manifest.json').read_text())
    with tarfile.open(root / 'objects.tar.gz') as archive:
        objects = {m.name: digest(archive.extractfile(m).read()) for m in archive if m.isfile()}
    for key, value in objects.items():
        assert key not in all_objects or all_objects[key] == value, key
        all_objects[key] = value
    attempts = manifest.get('attempts', manifest.get('targets'))
    report = {'bundle': name, 'manifest_sha256': filehash(root / 'manifest.json'),
              'checksums_sha256': filehash(root / 'SHA256SUMS'),
              'checksum_entries_checked': count, 'attempts': len(attempts),
              'object_members_checked': len(objects), 'successful_targets': []}
    for entry in attempts:
        rp = root / entry.get('receipt_path', entry.get('attempt_dir', '') + '/receipt.json')
        receipt = json.loads(rp.read_text())
        source = root / entry.get('snapshot_path', entry.get('snapshot', ''))
        assert filehash(source) == receipt['source_sha256'] == entry['source_sha256']
        assert receipt['target'] == entry['target']
        if receipt['exit_status'] != 0:
            assert receipt['output_sha256'] is None
            continue
        target = receipt['target']
        obj = 'objects/' + target.replace('.', '/') + '.olean'
        assert objects[obj] == entry['output_sha256'] == receipt['output_sha256']
        all_sources[target] = receipt['source_sha256']
        log = (rp.parent / 'lean.log').read_text()
        assert 'Lean (version 4.32.0,' in log
        assert 'error:' not in log and 'sorryAx' not in log
        parsed = [{'declaration': m.group(1), 'axioms': [x.strip() for x in m.group(2).split(',') if x.strip()]}
                  for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log)]
        parsed += [{'declaration': m.group(1), 'axioms': []}
                   for m in re.finditer(r"'([^']+)' does not depend on any axioms", log)]
        declared = entry.get('axioms', entry.get('axiom_reports'))
        assert parsed == declared, (target, parsed, declared)
        assert len(parsed) == entry['axiom_report_count']
        assert all(set(row['axioms']) <= STANDARD for row in parsed)
        assert receipt['process_swaps'] == entry['process_swaps'] == 0
        assert receipt['max_rss_kib'] == entry['max_rss_kib']
        timing = (rp.parent / 'time.log').read_text()
        assert int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', timing).group(1)) == receipt['max_rss_kib']
        assert int(re.search(r'\bSwaps: (\d+)', timing).group(1)) == 0
        assert int(re.search(r'Exit status: (\d+)', timing).group(1)) == 0
        assert re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)', timing).group(1) == receipt['elapsed_wall_clock']
        assert receipt['max_rss_kib'] < 6 * 1024 * 1024
        assert entry['cgroup'] == {'MemoryHigh': '4G', 'MemoryMax': '6G', 'MemorySwapMax': '0', 'TasksMax': 128}
        row = {'target': target, 'attempt': receipt['attempt'], 'exit_status': 0,
               'source_base_revision': receipt['source_base_revision'],
               'source_sha256': receipt['source_sha256'], 'output_sha256': receipt['output_sha256'],
               'receipt_sha256': filehash(rp), 'raw_axiom_reports': parsed,
               'wall_time': receipt['elapsed_wall_clock'], 'max_rss_kib': receipt['max_rss_kib'],
               'process_swaps': receipt['process_swaps']}
        report['successful_targets'].append(row)
        green.append((receipt, row))
    result['bundles'].append(report)

edges = []
for receipt, row in green:
    for imp in receipt['direct_imports']:
        obj = 'objects/' + imp['module'].replace('.', '/') + '.olean'
        checked = obj in all_objects
        if checked:
            assert imp['object_sha256'] == all_objects[obj]
        source_checked = imp['module'] in all_sources
        if source_checked:
            assert imp['source_sha256'] == all_sources[imp['module']]
        edges.append({'target': receipt['target'], 'import': imp['module'],
                      'object_matches_archived_output': checked, 'source_matches_successful_snapshot': source_checked})
result['represented_dependency_edges'] = edges
result['successful_targets'] = len(green)
result['successful_axiom_reports'] = sum(len(row['raw_axiom_reports']) for _, row in green)
result['max_successful_rss_kib'] = max(row['max_rss_kib'] for _, row in green)
result['failed_attempts_retained'] = sum(b['attempts'] - len(b['successful_targets']) for b in result['bundles'])
assert result['successful_targets'] == 7
assert result['successful_axiom_reports'] == 15
assert result['failed_attempts_retained'] == 18
out = BASE / 'terminal-row-bridges-root-audit-20261016.json'
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ['successful_targets', 'successful_axiom_reports', 'max_successful_rss_kib', 'failed_attempts_retained']}))
print(str(out), filehash(out))
