from pathlib import Path
import hashlib, importlib.util, json, shutil
from datetime import datetime, timezone

base = Path('/home/dombarker/project-offloads')
prior = base / 'aspis-r1-r18-sampler-carrier-20261016'
w = base / 'aspis-r1-r18-sampler-rank-20261016'
p = base / 'aspis-r1-j17-port-20261015'
c = base / 'aspis-r1-r18-sampler-20261016/models'
old = base / 'aspis-r1-concrete-decoder-20261013'
w.mkdir(exist_ok=True)
shutil.copy2(prior / 'runner.py', w / 'runner.py')
spec = importlib.util.spec_from_file_location('runner', w / 'runner.py')
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
closure = json.loads((prior / 'rank-closure.json').read_text())
inventory = json.loads((prior / 'rank-cache-inventory.json').read_text())
base_snapshot = p / 'extracted/external-inputs-002.json'
data, _ = r.verify_snapshot(base_snapshot)
basekeys = r.external_keys(data)
bridge_manifest = p / 'bridge/manifest.json'
bridge = json.loads(bridge_manifest.read_text())
cm = json.loads((c / 'sources/SOURCE-MANIFEST.json').read_text())
audit = []
missing = []
data['roots'] = [
    {'name':'rank_bridge', 'source':str(p/'bridge/sources'), 'objects':str(p/'bridge/objects')},
    {'name':'rank_models', 'source':str(c/'sources'), 'objects':str(c/'objects')},
] + data['roots']
for row in inventory:
    name = row['module']; target = closure['modules'][name]
    if name in cm['modules']:
        item = cm['modules'][name]; src = c/'sources'/item['stage_as']
        receiptpath = c/'successful-targets'/(name+'.json')
        receipt = json.loads(receiptpath.read_text())
        objects = r.object_pins(c/'objects', name, data['olean_header_seal'])
        assert r.sha(src) == target['sha256'] == receipt['key']['source_sha256']
        assert receipt['exit_status'] == 0 and receipt['axioms']['passed']
        assert receipt['key']['runtime'] == data['runtime_files']
        assert receipt['key']['options'] == ['-j1','-M0']
        assert receipt['objects'] == objects
        expected = {}
        for dep in r.imports(src, implicit_init=True):
            if dep in cm['modules']:
                dr = json.loads((c/'successful-targets'/(dep+'.json')).read_text())
                expected[dep] = {'receipt_key':r.digest(dr['key']), 'objects':r.object_pins(c/'objects',dep,data['olean_header_seal'])}
            else:
                expected[dep] = {'objects':data['modules'][dep]['objects'], 'closure_key':basekeys[dep]}
        assert receipt['key']['imports'] == expected, name
        data['modules'][name] = {'root':'rank_models','source':str(src),'source_sha256':r.sha(src),
            'imports':r.imports(src,implicit_init=True),'objects':objects,
            'build_receipt':{'path':str(receiptpath),'sha256':r.sha(receiptpath)}}
        audit.append({'module':name,'origin':'recent C model receipt; source/runtime/import/object checked',
            'source_sha256':r.sha(src),'receipt_sha256':r.sha(receiptpath),'objects':objects})
    elif name in bridge['dependency_pins']:
        item = bridge['dependency_pins'][name]; src = p/'bridge'/item['source_snapshot']
        objects = r.object_pins(p/'bridge/objects',name,data['olean_header_seal'])
        assert r.sha(src) == target['sha256'] == item['source_sha256']
        assert objects['.olean']['sha256'] == item['object_sha256']
        assert item['exact_source_match_to_cache_revision'] is True
        deps = r.imports(src,implicit_init=True)
        assert not any(dep.startswith('Aeneas') or dep.startswith('AspisR72Sampler') for dep in deps)
        data['modules'][name] = {'root':'rank_bridge','source':str(src),'source_sha256':r.sha(src),
            'imports':deps,'objects':objects,'retained_cache_manifest':str(bridge_manifest)}
        audit.append({'module':name,'origin':'retained exact-source Lean 4.32 bridge cache; historical source/object attestation, not a new compile receipt',
            'source_sha256':r.sha(src),'objects':objects,'historical_attestation':item})
    else:
        missing.append(name)
assert len(audit) == 55 and len(missing) == 10
for name in [x['module'] for x in audit]:
    for dep in data['modules'][name]['imports']:
        assert dep in data['modules'], (name,dep)
r.external_keys(data)
pins = w/'input-pins'; pins.mkdir(exist_ok=True)
for src,dst in [(prior/'rank-closure.json','rank-closure.json'),
                (prior/'rank-cache-inventory.json','rank-cache-inventory.json'),
                (c/'sources/SOURCE-MANIFEST.json','models-source-manifest.json'),
                (p/'bridge/local-evidence/runtime.json','bridge-original-runtime.json')]:
    shutil.copy2(src,pins/dst); data['provenance_files'][str(pins/dst)] = r.sha(pins/dst)
data['provenance_files'][str(bridge_manifest)] = r.sha(bridge_manifest)
data['provenance_files'][str(base_snapshot)] = r.sha(base_snapshot)
data['scope'] = '55 exact-source cached project modules: 13 current receipt-attested models and 42 historical pure Lean 4.32 bridge objects. No historical Aeneas object reused. No Lean invoked by snapshot.'
data['captured_utc'] = datetime.now(timezone.utc).isoformat()
r.dump(w/'external-inputs-rank.json',data)
r.dump(w/'cache-audit.json',audit)
sources = w/'sources'; sources.mkdir(exist_ok=True)
entries = {}; rejection = []
for name in missing:
    target = closure['modules'][name]
    src = old/'sources'/(r.stem(name)+'.lean')
    assert r.sha(src) == target['sha256']
    dest = sources/(r.stem(name)+'.lean'); dest.parent.mkdir(parents=True,exist_ok=True)
    shutil.copy2(src,dest)
    entries[name] = {'source':target['path'],'source_sha256':r.sha(dest),'source_revision':closure['source_revision'],
        'imports':r.imports(dest),'stage_as':r.stem(name)+'.lean','role':'unchanged existing source-rank closure, current-backend focused check'}
    rejection.append({'module':name,'source_sha256':r.sha(src),'old_object_sha256':r.sha(old/'objects'/(r.stem(name)+'.olean')),
        'decision':'recompile unchanged source; do not reuse historical Aeneas-dependent objects or unkeyed import receipts'})
auditname = 'SourceSamplerByteRankAudit'
dest = sources/(auditname+'.lean')
dest.write_text('import R1SourceSamplerByteRank\n\n#print axioms AspisR1.SourceSamplerByteRank.word_value\n#print axioms AspisR1.SourceSamplerByteRank.run4_bytes\n#print axioms AspisR1.SourceSamplerByteRank.rank_lt\n')
entries[auditname] = {'source':'new audit-only generated target','source_sha256':r.sha(dest),'source_revision':closure['source_revision'],
    'imports':r.imports(dest),'stage_as':auditname+'.lean','role':'three exact source-rank theorem axiom reports'}
r.dump(sources/'SOURCE-MANIFEST.json',{'format':2,'modules':entries,'topological_order':missing+[auditname],'groups':{}})
r.dump(w/'old-cache-rejection.json',rejection)
r.staged(w); r.verify_snapshot(w/'external-inputs-rank.json')
print(json.dumps({'cached':len(audit),'targets':missing,'audit_target':auditname,
    'snapshot_sha256':r.sha(w/'external-inputs-rank.json'),'source_manifest_sha256':r.sha(sources/'SOURCE-MANIFEST.json')},indent=2))
