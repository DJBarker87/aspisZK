"""Independent focused proof evidence audit. Usage: SCRIPT BUNDLE REPO"""
from pathlib import Path
import hashlib
import json
import re
import sys
import tarfile

bundle, repo = map(Path, sys.argv[1:])
sha = lambda data: hashlib.sha256(data).hexdigest()
fh = lambda path: sha(path.read_bytes())
standard = {'propext', 'Classical.choice', 'Quot.sound'}
m = json.loads((bundle/'manifest.json').read_text())
entries = (bundle/'SHA256SUMS').read_text().splitlines()
for row in entries:
    expected, rel = row.split('  ', 1)
    assert not Path(rel).is_absolute() and '..' not in Path(rel).parts
    assert fh(bundle/rel) == expected, rel
for key in ['environment', 'runner', 'executor']:
    assert fh(bundle/m[key+'_path']) == m[key+'_sha256']

def axiom_reports(log):
    result = []
    for x in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",log):
        result.append({'declaration':x.group(1),'axioms':[a.strip() for a in (x.group(2) or '').split(',') if a.strip()]})
    return result

# Previously reviewed source/output pairs; no unchanged proof replay.
prior_paths = [
    'mask-provenance-reconciliation-20261016/mask432-queue-final-audit-20261016.json',
    'mask-final-bridges-row-model-20261016/root-review.json',
    'terminal-row-callbacks-20261016/root-review.json',
    'terminal-equality-arithmetic-20261016/root-review.json',
    'current-mask-power-basis-20261016/independent-audit.json',
    'current-mask-lean432-20261016/manifest.json',
    'current-mask-loop-basis-20261016/manifest.json',
    'terminal-selected-composition-20261016/root-review.json',
]
evidence = repo/'docs/research/100bit-spend-path-20261013/evidence'
ledger = {}
def collect(obj, origin):
    if isinstance(obj, dict):
        name = obj.get('target', obj.get('module'))
        source = obj.get('source_sha256')
        output = obj.get('output_sha256', obj.get('object_sha256', obj.get('output_sha256_receipt')))
        if obj.get('output_sha256_receipt'):
            assert obj.get('exit_status') == 0 and obj.get('object_matches_receipt') is True
            assert output == obj.get('archived_object_sha256')
        is_success = obj.get('exit_status') == 0 or (origin.startswith('mask-provenance-reconciliation-') and 'order' in obj and obj.get('sorryAx_declarations') == [])
        if name and source and output and is_success:
            ledger[(name, output)] = {'source_sha256': source, 'evidence': origin}
        for value in obj.values(): collect(value, origin)
    elif isinstance(obj, list):
        for value in obj: collect(value, origin)
for path in prior_paths:
    collect(json.loads((evidence/path).read_text()), path)

objects = {row['object_path']: row['object_sha256'] for row in m['targets'].values()}
for path, digest in objects.items(): assert fh(bundle/path) == digest
with tarfile.open(bundle/'attempts-and-target-objects.tar.gz') as t:
    archived = {x.name: sha(t.extractfile(x).read()) for x in t if x.isfile()}
for path, digest in objects.items():
    matches = [value for name, value in archived.items() if name == path or name.endswith('/'+path)]
    assert matches == [digest], path

selected = []
failures = []
receipts = []
for entry in m['attempts']:
    rp = bundle/entry['receipt_path']
    r = json.loads(rp.read_text())
    assert fh(bundle/entry['source_snapshot']) == r['source_sha256'] == entry['source_sha256']
    assert r['exit_status'] == entry['exit_status']
    assert r['cgroup'] == {'MemoryHigh': '4G', 'MemoryMax': '6G', 'MemorySwapMax': '0', 'TasksMax': 128}
    assert r['reservation']['total_reserved_bytes'] <= r['reservation']['host_safe_limit_bytes']
    log = (rp.parent/'lean.log').read_text()
    assert 'Lean (version 4.32.0,' in log
    reports = axiom_reports(log)
    assert reports == r['axiom_reports'] == entry['axiom_reports']
    assert reports == json.loads((bundle/entry['axiom_report_path']).read_text())
    assert r['direct_imports'] == json.loads((bundle/entry['direct_import_pin_path']).read_text())
    timing = (rp.parent/'time.log').read_text()
    assert int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', timing).group(1)) == r['max_rss_kib']
    assert int(re.search(r'\bSwaps: (\d+)', timing).group(1)) == r['process_swaps'] == 0
    assert re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)', timing).group(1) == r['elapsed_wall_clock']
    row = {k:r[k] for k in ['target','attempt','source_base_revision','source_sha256','output_sha256','exit_status','elapsed_wall_clock','max_rss_kib','process_swaps']}
    row['receipt_sha256'] = fh(rp)
    if r['exit_status'] != 0:
        assert r['output_sha256'] is None
        failures.append(row)
        continue
    assert 'sorryAx' not in log and 'error:' not in log
    assert all(set(x['axioms']) <= standard for x in reports)
    assert int(re.search(r'Exit status: (\d+)', timing).group(1)) == 0
    target = m['targets'][r['target']]
    assert r['attempt'] == target['attempt']
    assert r['output_sha256'] == target['object_sha256'] == objects['objects/'+r['target']+'.olean']
    assert r['source_sha256'] == target['source_sha256'] == fh(bundle/target['source_snapshot'])
    assert reports == target['axiom_reports'] and len(reports) == target['axiom_report_count']
    ledger[(r['target'],r['output_sha256'])] = {'source_sha256':r['source_sha256'],'evidence':entry['receipt_path']}
    row['source_snapshot'] = entry['source_snapshot']
    row['raw_axiom_reports'] = reports
    selected.append(row)
    receipts.append(r)

edges = []
for r in receipts:
    for imp in r['direct_imports']:
        prior = ledger.get((imp['module'], imp['object_sha256']))
        if prior and imp['source_sha256']:
            assert prior['source_sha256'] == imp['source_sha256']
        library = imp['module'].startswith(('Aeneas.', 'Mathlib.'))
        assert prior or library, ('unreconciled custom import',r['target'],imp)
        edges.append({'target':r['target'],'import':imp['module'],
                      'object_sha256':imp['object_sha256'],'source_bound_success':prior,
                      'pinned_library_dependency':library})

# Exact generated source slices, including trait dictionaries. Source comments
# and declaration text must match; only surrounding whitespace is stripped.
origins = {'G':bundle/'provenance/generated-G'}
blocks = []
source = (bundle/m['targets']['Qm31PackBase4Slice']['source_snapshot']).read_text()
originals = [(origins['G']/name).read_text() for name in ['Funs.lean','Types.lean']]
for block in re.split(r'(?m)(?=^/--)',source)[1:]:
    block = block.split('\nend AspisR1SelectedMaskProbe')[0].strip()
    assert any(block in text for text in originals), block[:180]
    blocks.append({'target':'Qm31PackBase4Slice','origin':'G','exact_trimmed_block_sha256':sha(block.encode())})
assert len(blocks)==3
reconciliation=json.loads((bundle/'provenance/qm-pack-slice/reconciliation.json').read_text())
assert reconciliation['compiled_green_source_sha256']==sha(source.encode())
for span in reconciliation['declaration_spans']:
    origin=(origins['G']/(span['source_file']+'.lean')).read_bytes()
    raw=origin[slice(*span['byte_range'])]
    assert sha(raw)==span['sha256']
    assert raw.strip() in source.encode()
for item in m['preflight_only']:
    directory=bundle/item['directory']
    assert not (directory/'receipt.json').exists()
    assert sorted(str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file())==sorted(item['files'])
assert len(selected) == m['green_target_count'] == len(m['targets'])
assert len(failures) == m['failed_attempt_count']
print(json.dumps({'schema':'aspis-packer-row-exact-root-audit.v1',
    'scope':'Source/receipt/object, raw axiom/resource records, prior custom dependency reconciliation and exact source-slice audit. No new Lean replay or end-to-end verifier theorem.',
    'manifest_sha256':fh(bundle/'manifest.json'),'checksums_sha256':fh(bundle/'SHA256SUMS'),
    'checksum_entries':len(entries),'selected_target_count':len(selected),
    'selected_axiom_reports':sum(len(x['raw_axiom_reports']) for x in selected),
    'selected_targets':selected,'failed_attempts_retained':failures,'preflight_only':m['preflight_only'],
    'custom_dependency_evidence_pins':{path:fh(evidence/path) for path in prior_paths},
    'direct_import_edges':edges,'exact_generated_blocks':blocks,
    'generated_origin_pins':{origin:{name:fh(path/name) for name in ['Funs.lean','Types.lean']} for origin,path in origins.items()}},indent=2))
