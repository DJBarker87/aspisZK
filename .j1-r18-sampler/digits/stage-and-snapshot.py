from pathlib import Path
import hashlib, importlib.util, json, shutil
from datetime import datetime, timezone

base_root = Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/extracted')
sampler = Path('/home/dombarker/project-offloads/aspis-r1-r18-sampler-20261016')
work = sampler / 'digits'
origins = [sampler/'models', sampler/'proofs', sampler/'pass',
           Path('/home/dombarker/project-offloads/aspis-r1-r18-sampler-carrier-20261016')]
spec = importlib.util.spec_from_file_location('runner', work/'runner.py')
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
base = base_root/'external-inputs-002.json'
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
    data['modules'][name] = {'root': 'checked_'+str(origins.index(p)),
        'source': str(source), 'source_sha256': r.sha(source), 'imports': deps,
        'objects': objects, 'build_receipt': {'path': str(rp), 'sha256': r.sha(rp)}}
    records.append({'module': name, 'source_sha256': r.sha(source),
        'receipt': str(rp), 'receipt_sha256': r.sha(rp),
        'receipt_key_sha256': r.digest(receipt['key']), 'objects': objects})

for name in ['R1SamplerRepeatedPass', 'ExtractedQM31SamplerDivision', 'ExtractedQM31SamplerBytes']:
    visit(name)
(work/'input-manifests').mkdir(exist_ok=True)
for i, p in enumerate(origins):
    data['roots'].insert(0, {'name': 'checked_'+str(i), 'source': str(p/'sources'), 'objects': str(p/'objects')})
    frozen = work/'input-manifests'/(str(i)+'.json')
    shutil.copyfile(p/'sources/SOURCE-MANIFEST.json', frozen)
    data['provenance_files'][str(frozen)] = r.sha(frozen)
data['provenance_files'][str(base)] = r.sha(base)
data['scope'] = 'Read-only exact source/runtime/import/object receipt extension for the four-pass sampler proof; no replay or cache relocation.'
data['captured_utc'] = datetime.now(timezone.utc).isoformat()
r.dump(work/'external-inputs-digits.json', data)
r.dump(work/'import-source-audit.json', records)
name = 'ExtractedQM31SamplerDigits'; source = work/'sources'/(name+'.lean')
item = {'source': 'docs/research/100bit-spend-path-20261013/lean/'+name+'.lean',
        'source_sha256': r.sha(source), 'source_revision': '670b7e149f94004baa5b138bdc2db28f3bc646bd extraction plus owned proofs',
        'imports': r.imports(source), 'stage_as': name+'.lean', 'role': 'Actual four-pass source loop composition', 'axiom_requests': 4}
r.dump(work/'sources/SOURCE-MANIFEST.json', {'format': 2, 'modules': {name: item}, 'topological_order': [name], 'groups': {}})
r.staged(work)
print(json.dumps({'extension_count': len(records), 'snapshot_sha256': r.sha(work/'external-inputs-digits.json'), 'source_sha256': r.sha(source)}, indent=2))
