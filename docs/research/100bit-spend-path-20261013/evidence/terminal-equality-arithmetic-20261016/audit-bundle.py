"""Audit retained evidence without replaying Lean. Usage: script BUNDLE_DIR."""
import hashlib
import json
import pathlib
import re
import sys
import tarfile

root = pathlib.Path(sys.argv[1])
sha = lambda data: hashlib.sha256(data).hexdigest()
filehash = lambda path: sha(path.read_bytes())
standard = {'propext', 'Classical.choice', 'Quot.sound'}
manifest = json.loads((root / 'manifest.json').read_text())
checksums = (root / 'SHA256SUMS').read_text().splitlines()
for line in checksums:
    expected, rel = line.split('  ', 1)
    assert not pathlib.Path(rel).is_absolute() and '..' not in pathlib.Path(rel).parts
    assert filehash(root / rel) == expected, rel
with tarfile.open(root / 'objects.tar.gz') as archive:
    objects = {m.name: sha(archive.extractfile(m).read()) for m in archive if m.isfile()}
for rel, digest in objects.items():
    assert filehash(root / rel) == digest

def reports(log):
    result = [{'declaration': m.group(1), 'axioms': [x.strip() for x in m.group(2).split(',') if x.strip()]}
              for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log)]
    result += [{'declaration': m.group(1), 'axioms': []}
               for m in re.finditer(r"'([^']+)' does not depend on any axioms", log)]
    return result

selected = []
attempts = []
edges = []
for entry in manifest['attempts']:
    directory = root / entry['attempt_dir']
    receipt_path = directory / 'receipt.json'
    receipt = json.loads(receipt_path.read_text())
    target = receipt['target']
    source = directory / 'sources' / (target.replace('.', '/') + '.lean')
    assert filehash(source) == receipt['source_sha256'] == entry['source_sha256']
    for key in ['target', 'attempt', 'exit_status', 'output_sha256', 'max_rss_kib', 'process_swaps', 'source_base_revision']:
        assert entry[key] == receipt[key], (target, key)
    assert receipt['cgroup'] == {'MemoryHigh': '4G', 'MemoryMax': '6G', 'MemorySwapMax': '0', 'TasksMax': 128}
    assert receipt['reservation']['total_reserved_bytes'] <= receipt['reservation']['host_safe_limit_bytes']
    log = (directory / 'lean.log').read_text()
    assert 'Lean (version 4.32.0,' in log
    assert reports(log) == receipt['axiom_reports'] == entry['axiom_reports']
    timing = (directory / 'time.log').read_text()
    assert int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', timing).group(1)) == receipt['max_rss_kib']
    assert int(re.search(r'\bSwaps: (\d+)', timing).group(1)) == receipt['process_swaps'] == 0
    assert re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)', timing).group(1) == receipt['elapsed_wall_clock']
    row = {k: receipt[k] for k in ['target', 'attempt', 'exit_status', 'source_base_revision', 'source_sha256', 'output_sha256', 'max_rss_kib', 'process_swaps', 'elapsed_wall_clock']}
    row['receipt_sha256'] = filehash(receipt_path)
    attempts.append(row)
    if receipt['exit_status'] != 0:
        assert receipt['output_sha256'] is None
        continue
    assert int(re.search(r'Exit status: (\d+)', timing).group(1)) == 0
    assert 'error:' not in log and 'sorryAx' not in log
    assert all(set(report['axioms']) <= standard for report in reports(log))
    assert objects['objects/' + target.replace('.', '/') + '.olean'] == receipt['output_sha256']
    rec = manifest['targets'][target]
    if rec['selected_attempt'] != receipt['attempt']:
        continue
    assert rec['source_sha256'] == filehash(root / 'sources' / (target + '.lean')) == receipt['source_sha256']
    assert rec['output_sha256'] == receipt['output_sha256']
    assert rec['axiom_reports'] == reports(log)
    row['raw_axiom_reports'] = reports(log)
    selected.append(row)
    for imp in receipt['direct_imports']:
        obj = 'objects/' + imp['module'].replace('.', '/') + '.olean'
        represented = obj in objects
        if represented:
            assert objects[obj] == imp['object_sha256']
        known = imp['module'] in manifest['targets']
        if known:
            assert imp['source_sha256'] == manifest['targets'][imp['module']]['source_sha256']
        edges.append({'target': target, 'import': imp['module'], 'object_sha256': imp['object_sha256'],
                      'archived_object_matches': represented, 'selected_source_matches': known})

# Reconcile the null source fields in new SemDecision import receipts using
# the original, already published successful receipt, never by rewriting it.
prior = root / 'provenance/semdecision-prior-success'
receipt = json.loads((prior / 'receipt.json').read_text())
assert receipt['exit_status'] == 0
assert receipt['source_sha256'] == filehash(prior / 'sources/R0P/SemDecision.lean')
assert receipt['output_sha256'] == objects['objects/R0P/SemDecision.olean']
assert reports((prior / 'lean.log').read_text()) == receipt['axiom_reports']
assert all(set(r['axioms']) <= standard for r in receipt['axiom_reports'])
for edge in edges:
    if edge['import'] == 'R0P.SemDecision':
        assert edge['object_sha256'] == receipt['output_sha256']
        edge['source_reconciled_by_prior_success'] = receipt['source_sha256']

# Exact G function/type declaration blocks: ignore only surrounding whitespace.
origin = root / 'provenance/generated-origin/AspisR1SelectedMaskProbe'
funs = (origin / 'Funs.lean').read_text()
types = (origin / 'Types.lean').read_text()
assert filehash(origin / 'Funs.lean') == manifest['source_identity']['generated_origin_funs_sha256']
assert filehash(origin / 'Types.lean') == manifest['source_identity']['generated_origin_types_sha256']
source_identity = []
slice_source = (root / 'sources/EqualityValueSlice.lean').read_text()
for block in re.split(r'(?m)(?=^/--)', slice_source)[1:]:
    block = block.split('\nend AspisR1SelectedMaskProbe')[0].strip()
    header = block.split('-/')[0] + '-/'
    src = funs if header in funs else types
    assert header in src
    original = src[src.index(header):].split('\n/--', 1)[0].split('\nend AspisR1SelectedMaskProbe')[0].strip()
    assert original == block, header
    source_identity.append({'header': header, 'exact_trimmed_block_sha256': sha(block.encode())})
assert len(source_identity) == 5

# Historical reuse is exact declaration text, with fresh import/namespace framing.
reuse = json.loads((root / 'provenance/terminal-horner-core-source-slice-manifest.json').read_text())
old = (root / 'provenance/SourceMixing-original.lean').read_text()
core = (root / 'sources/TerminalHornerCore.lean').read_text()
assert sha(old.encode()) == reuse['source_sha256']
for rec in reuse['blocks']:
    start = re.search(r'(?m)^(?:def|theorem) ' + rec['name'] + r'\b', core).start()
    rest = core[start:]
    block = re.split(r'\n\n(?=def |theorem |#print)', rest, maxsplit=1)[0]
    assert (block + '\n\n') in old and sha((block + '\n\n').encode()) == rec['block_sha256'], rec['name']
assert not any(e['import'] == 'AspisV8R17.SourceMixing' for e in edges)

assert len(selected) == 7
assert sum(len(r['raw_axiom_reports']) for r in selected) == 13
assert len(attempts) == 31
result = {'schema': 'aspis-equality-terminal-root-review.v1',
          'scope': 'Evidence integrity, exact source slices, selected raw axiom logs, resource receipts, represented import edges and historical source reuse. Not a new Lean replay or full protocol theorem.',
          'manifest_sha256': filehash(root / 'manifest.json'),
          'checksums_sha256': filehash(root / 'SHA256SUMS'),
          'checksum_entries': len(checksums), 'archived_objects': len(objects),
          'selected_targets': selected, 'all_attempts': attempts,
          'selected_axiom_reports': 13, 'failed_attempts_retained': sum(r['exit_status'] != 0 for r in attempts),
          'represented_dependency_edges': edges, 'exact_generated_blocks': source_identity,
          'historical_horner_reuse': reuse,
          'semdecision_prior_success': manifest['dependency_reconciliation']['R0P.SemDecision']}
print(json.dumps(result, indent=2))
