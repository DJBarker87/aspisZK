from pathlib import Path
import importlib.util, json, shutil, sys
from datetime import datetime, timezone

sampler = Path('/home/dombarker/project-offloads/aspis-r1-r18-sampler-20261016')
work = sampler / 'correct'
base = Path(sys.argv[1])
origins = [sampler/'models', sampler/'proofs', sampler/'pass', sampler/'digits',
    Path('/home/dombarker/project-offloads/aspis-r1-r18-sampler-carrier-20261016'),
    Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/extracted')]
origins.extend(Path(p) for p in sys.argv[2:])
spec = importlib.util.spec_from_file_location('runner', work/'runner.py')
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
data, _ = r.verify_snapshot(base)
manifests = {p: json.loads((p/'sources/SOURCE-MANIFEST.json').read_text()) for p in origins}
records = []

def visit(name):
    if name in data['modules']:
        return
    hits = [p for p, m in manifests.items() if name in m['modules']]
    assert len(hits) == 1, (name, hits)
    p = hits[0]; item = manifests[p]['modules'][name]
    source = p/'sources'/item['stage_as']
    assert r.sha(source) == item['source_sha256']
    deps = r.imports(source, implicit_init=True)
    for dep in deps:
        visit(dep)
    rp = p/'successful-targets'/(name+'.json')
    receipt = json.loads(rp.read_text())
    assert receipt['exit_status'] == 0 and receipt['axioms']['passed'], name
    assert receipt['key']['source_sha256'] == r.sha(source)
    assert receipt['key']['runtime'] == data['runtime_files']
    assert receipt['key']['options'] == ['-j1', '-M0']
    objects = r.object_pins(p/'objects', name, data['olean_header_seal'])
    assert objects == receipt['objects'], name
    keys = r.external_keys(data)
    expected = {}
    for dep in deps:
        if dep in manifests[p]['modules']:
            dr = json.loads((p/'successful-targets'/(dep+'.json')).read_text())
            expected[dep] = {'receipt_key': r.digest(dr['key']),
                'objects': r.object_pins(p/'objects', dep, data['olean_header_seal'])}
        else:
            expected[dep] = {'objects': data['modules'][dep]['objects'], 'closure_key': keys[dep]}
    assert receipt['key']['imports'] == expected, name
    rootname = 'correct_checked_'+str(origins.index(p))
    data['modules'][name] = {'root': rootname,
        'source': str(source), 'source_sha256': r.sha(source), 'imports': deps,
        'objects': objects, 'build_receipt': {'path': str(rp), 'sha256': r.sha(rp)}}
    records.append({'module': name, 'source_sha256': r.sha(source),
        'receipt': str(rp), 'receipt_sha256': r.sha(rp),
        'receipt_key_sha256': r.digest(receipt['key']), 'objects': objects})

for name in ['R1SourceSamplerByteRank', 'ExtractedQM31SamplerDigits', 'ExtractedQM31SamplerCarrier']:
    visit(name)
(work/'input-manifests').mkdir(exist_ok=True)
for i, p in enumerate(origins):
    data['roots'].insert(0, {'name': 'correct_checked_'+str(i), 'source': str(p/'sources'), 'objects': str(p/'objects')})
    frozen = work/'input-manifests'/(str(i)+'.json')
    shutil.copyfile(p/'sources/SOURCE-MANIFEST.json', frozen)
    data['provenance_files'][str(frozen)] = r.sha(frozen)
data['provenance_files'][str(base)] = r.sha(base)
data['scope'] = 'Exact source/runtime/import/object receipt extension for final emitted sampler correspondence. Retains the base snapshot mixed-axiom metadata; final theorem-specific audits must be standard-only. No replay or cache relocation.'
data['captured_utc'] = datetime.now(timezone.utc).isoformat()
r.dump(work/'external-inputs-correct.json', data)
r.dump(work/'import-source-audit.json', records)
name = 'ExtractedQM31SamplerCorrect'; source = work/'sources'/(name+'.lean')
item = {'source': 'docs/research/100bit-spend-path-20261013/lean/'+name+'.lean',
        'source_sha256': r.sha(source), 'source_revision': '670b7e149f94004baa5b138bdc2db28f3bc646bd exact extraction plus owned proofs',
        'imports': r.imports(source), 'stage_as': name+'.lean', 'role': 'Actual sampler byte-rank/current-QM correspondence', 'axiom_requests': 7}
r.dump(work/'sources/SOURCE-MANIFEST.json', {'format': 2, 'modules': {name: item}, 'topological_order': [name], 'groups': {}})
r.staged(work)
print(json.dumps({'extension_count': len(records), 'snapshot_sha256': r.sha(work/'external-inputs-correct.json'), 'source_sha256': r.sha(source)}, indent=2))
