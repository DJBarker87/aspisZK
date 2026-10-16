#!/usr/bin/env python3
from pathlib import Path
from collections import Counter
import hashlib, json, re, subprocess

b = Path(__file__).resolve().parent
root = b.parents[4]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
inventory = json.loads((b/'full-inventory.json').read_text())
mods = inventory['modules']
pins = {x['module']:x for x in json.loads((b/'full-current-source-pins.json').read_text())}
assert len(mods) == len(pins) == 46 and not inventory['direct_import_object_mismatches']
assert Counter(x['kind'] for x in mods.values()) == {'current144':23, 'rank-reviewed-pure-cache':17, 'R17':5, 'A-focused-strict-predecessor':1}
staging = json.loads((b/'staging-receipt.json').read_text())
assert staging['inventory_sha256'] == sha(b/'full-inventory.json')
assert staging['current_source_pins_sha256'] == sha(b/'full-current-source-pins.json')
assert staging['target_source_pins_sha256'] == sha(b/'target-source-pins.json')
assert not staging['direct_import_object_mismatches'] and len(staging['external_direct_imports']) == 32
for module, x in mods.items():
    src = b/'provenance/sources'/(module.replace('.', '/')+'.lean')
    pin = pins[module]
    committed = subprocess.check_output(['git','show',pin['source_revision']+':'+pin['source']], cwd=root)
    assert src.read_bytes() == committed and sha(src) == x['source_sha256'] == pin['source_sha256']
    for dep,h in x['direct_import_objects'].items():
        expected = mods[dep]['object_sha256'] if dep in mods else staging['external_direct_imports'][dep]['object_sha256']
        assert expected == h, (module,dep)
    if x['kind'] == 'rank-reviewed-pure-cache':
        assert x['rank_snapshot_sha256'] == 'ddea49cae41e5cbe17961db56cc7d882075df4fc966cb90af20e006b0d94ed1b'
        continue
    p = b/'provenance/receipts'/(module+'.json')
    r = json.loads(p.read_text())
    assert sha(p) == x['receipt_sha256'] and r['exit_status'] == 0
    if x['kind'] == 'current144':
        assert r['source_sha256'] == x['source_sha256'] and r['output_sha256'] == x['object_sha256']
        assert {q['module']:q['object_sha256'] for q in r['direct_imports']} == x['direct_import_objects']
        assert all(set(q['axioms']) <= allowed for q in r['axiom_reports'])
    elif x['kind'] == 'R17':
        assert r['key']['source_sha256'] == x['source_sha256'] and r['objects']['.olean']['sha256'] == x['object_sha256']
        assert {n:q['objects']['.olean']['sha256'] for n,q in r['key']['imports'].items()} == x['direct_import_objects']
        assert r['axioms']['passed'] and all(set(q['axioms']) <= allowed for q in r['axioms']['reports'])
    else:
        assert r['source_sha256'] == x['source_sha256'] and r['olean_sha256'] == x['object_sha256']
        prior = b.parent/'r18-record-byte-codec-20261016/runs/strict-predecessor-a/receipt.json'
        assert sha(prior) == sha(p)

targets = {x['module']:x for x in json.loads((b/'complete-target-source-pins.json').read_text())}
attempts = {
    'semantic-modulo-a':('R0C.ModuloField',11),
    'semantic-slice-a':('R1FixedWidthSlice',2),
    'semantic-reconstruction-a':('R1FixedWidthReconstruction',1),
    'semantic-slices-a':('R1FixedWidthDecodedSlices',1),
    'semantic-wide-a':('R1WideExactLimbCodec',3),
    'semantic-folded-a':('R1FoldedLeafCodec',9),
    'semantic-coefficient-a':('R1SemanticCoefficientCodec',10),
    'semantic-low-a':('ExtractedPrefixSemanticLow',2),
}
produced = {}
for a,(module,count) in attempts.items():
    d=b/'runs'/a; r=json.loads((d/'receipt.json').read_text())
    mp=b/('input-manifest-'+a+'.json'); m=json.loads(mp.read_text())
    assert r['target']==module and r['exit_status']==0 and r['olean_sha256'] is not None
    assert r['source_sha256']==sha(d/'source.lean') and r['runner_sha256']==sha(d/'runner.py')
    assert r['input_manifest_sha256']==sha(mp)
    if module in targets:
        x=targets[module]
        committed=subprocess.check_output(['git','show',x['source_revision']+':'+x['source']],cwd=root)
        assert committed==(d/'source.lean').read_bytes() and x['source_sha256']==r['source_sha256']
    else:
        assert (root/'docs/research/100bit-spend-path-20261013/lean'/ (module+'.lean')).read_bytes()==(d/'source.lean').read_bytes()
    assert r['limits']=={'memory.max':'8589934592','memory.high':'6442450944','memory.swap.max':'0'}
    assert '-j1' in r['command'] and '-M0' in r['command'] and not r['dependency_rebuild']
    assert '4.32.0' in r['lean_version'] and len(r['runtime_sha256'])==4
    assert r['process_swaps']==0 and r['cgroup_swap_current']=='0' and r['memory_events_before']==r['memory_events_after']
    assert m['current_semantic_cache']['inventory_sha256']==sha(b/'full-inventory.json')
    assert m['current_semantic_cache']['staging_receipt_sha256']==sha(b/'staging-receipt.json')
    for n,x in mods.items():
        assert m['new_import_objects'][n.replace('.','/')+'.olean']==x['object_sha256']
        assert m['new_sources'][n.replace('.','/')+'.lean']==x['source_sha256']
    for n,h in produced.items():assert m['new_import_objects'][n.replace('.','/')+'.olean']==h
    produced[module]=r['olean_sha256']
    log=(d/'lean.log').read_text(); reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
    assert len(reports)==count,(a,len(reports),count)
    assert all(set(x.strip() for x in ax.split(','))<=allowed for _,ax in reports)
    assert 'sorryAx' not in log and 'error:' not in log
assert json.loads((b/'output-object-pins.json').read_text())==produced
old=json.loads((b/'prior-rank-ModuloField-receipt.json').read_text())
assert old['key']['imports']['AspisFormal.CircleGroupOrder']['objects']['.olean']['sha256']!=mods['AspisFormal.CircleGroupOrder']['object_sha256']
for line in (b/'SHA256SUMS').read_text().splitlines():
    h,p=line.split('  ',1);assert sha(b/p)==h,p
print('PASS:46 coherent reused predecessors; seven exact unchanged checks; strict-low bridge;39 standard-only reports; source/import/runtime/resource/output pins')
