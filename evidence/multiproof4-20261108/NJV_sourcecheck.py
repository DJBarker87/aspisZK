"""Owned source/receipt validator; all inherited inputs are read-only."""
from pathlib import Path
import hashlib,json,re,subprocess,lzma
E=Path(__file__).resolve().parent;P=E.parent/'multiproof3-20261108'
def blob(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes())
 assert hashlib.sha256(b).hexdigest()==Path(str(p)+'.sha256').read_text().strip()
 return b
sha=lambda p:hashlib.sha256(blob(p)).hexdigest()
old=(P/'NJP_sourcecheck.py').read_text()
# Re-run every unchanged predecessor assertion; redirect ONLY its own output.
code=old.replace('E=Path(__file__).resolve().parent;',f'E=Path({str(P)!r});')
code=code.replace("(E/'NJP_SOURCE_ASSOCIATION.json').write_text",f"(Path({str(E)!r})/'NJV_PREDECESSOR_SOURCE_ASSOCIATION.json').write_text")
exec(compile(code,'NJV_predecessor_validation','exec'),{'__file__':__file__,'__name__':'NJV_predecessor_validation'})
frozen=(E/'NJV_frozen_multiproof.rs.txt').read_text();native=(E/'NJV_multiproof.rs').read_text()
assert 'let parent = index_at(idx, i) >> arity.bits();' in frozen
assert 'let parent=super::index_at(&idx,i)>>super::Arity::Two.bits();' in native
assert 'let d = occupied_binary_parent(hash, val, i);' in frozen
assert 'let first=&val[i];let second=&val[i+1];' in native
assert 'Stop immediately BEFORE occupied_binary_parent(hash,val,i).' in native
assert not any(t in native for t in ['static mut','UnsafeCell','Atomic','Cell<','RefCell','Option<fn'])
# Same branch predicate, caller-established bounds evaluated before i+1.
assert 'kani::assume(0<n&&n<=16&&i<n&&w<=i&&at<=9216&&k<16&&j<32);' in native
assert 'kani::assume(i+1<n&&idx[i+1]==idx[i]^1);' in native
assert 'let first=&val[i+1];let second=&val[i+1];' not in native
controls=[]
for a,expected in [('NJV_K002',0),('NJV_K003',1)]:
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==expected
 v=E/(a+'_validation');g=json.loads((v/'NJV_TARGET_GRAPH.json').read_text());lock=json.loads((v/'NJV_LOCK.json').read_text());inputs=json.loads((v/'NJV_INPUTS.json').read_text())
 assert g['graph_matches_frozen'] and g['packages_frozen'] and not g['edge_errors'] and g['lock_unchanged']
 assert lock['unchanged'] and lock['before']==lock['after']
 assert inputs['KMX_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 cfg=json.loads((E/(a+'.json')).read_text());assert cfg['env']['CARGO_NET_OFFLINE']=='true'
 feats=next(x['features'] for x in g['features'] if x['name']=='aspis-r1-cost-probe')
 assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=set(feats)
 log=blob(E/a/'stdout.log').decode();assert 'timed out' not in log.lower()
 assert ('VERIFICATION:- SUCCESSFUL' if expected==0 else 'VERIFICATION:- FAILED') in log
 controls.append(dict(attempt=a,exit=expected,feature_count=len(g['features']),lock_sha256=lock['after'],source_sha256=sha(v/'NJV_harness.patch')))
result=dict(predecessor_validator_sha256=sha(P/'NJP_sourcecheck.py'),prefix_native_sha256=sha(E/'NJV_multiproof.rs'),frozen_source_sha256=sha(E/'NJV_frozen_multiproof.rs.txt'),controls=controls,pending_occupied_frame=True,new_trust_rows=[],native_semantic_transport='P6/D188 option-A RECLASSIFICATION',target_established=False)
(E/'NJV_SOURCE_ASSOCIATION.json').write_text(json.dumps(result,indent=2)+'\n')
print('NJV source/graph/lock/control validation PASS; inherited assertions unchanged; no credit from syntax alone')
