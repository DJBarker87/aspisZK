"""Bind the adopted no-op mark to the exact frozen source and retained features.
This is source-certificate validation under (z)(1), not a new native execution.
"""
from pathlib import Path
import hashlib,json,subprocess,copy
E=Path(__file__).resolve().parent; R=E.parents[1]
base=json.loads((E/'NHU_RETAINED_PINS.json').read_text())['revision']
def blob(path,rev=base):return subprocess.check_output(['git','show',rev+':'+path],cwd=R)
def sha(b):return hashlib.sha256(b).hexdigest()
source_path='crates/aspis-r1-cost-probe/src/r1_semantic.rs'
frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
src=blob(source_path,frozen).decode()
feature_path='evidence/verify-observed2-20261106/NHG_K080-graph-check.json'
graph=json.loads(blob(feature_path))
nef_path='evidence/slice-q-fnptr-20261029/NEF_SOURCE_PINS.json'
nef=json.loads(blob(nef_path))
def validate(s,g):
 body=s.split('fn mark(',1)[1].split('\nfn semantic_boundary',1)[0]
 expected='''obs: crate::verifier::Observer, i: u8) {
    #[cfg(feature="detail-phases")]
    if let Some(f)=obs {f(crate::verifier::Phase::SemanticPart(i));}
    #[cfg(not(feature="detail-phases"))]
    let _=(obs,i);
}
'''
 assert body==expected,'mark control/body changed'
 probe=next(p for p in g['selected_closure'] if p['name']=='aspis-r1-cost-probe')
 assert 'detail-phases' not in probe['features'],'profiling feature enabled'
 assert {'default','private-leaf-salts','optimized-terminal','program-build'} <= set(probe['features'])
 assert g['graph_matches_frozen'] and not g['edge_errors'] and not g['new_package_tuples']
validate(src,graph)
assert sha(src.encode())==nef['files'][source_path]['sha256']
controls=[]
for name,modified,g in [
 ('added effect',src.replace('let _=(obs,i);','panic!("effect"); let _=(obs,i);',1),graph),
 ('flipped cfg',src.replace('#[cfg(not(feature="detail-phases"))]','#[cfg(feature="detail-phases")]',1),graph),
 ('profiling enabled',src,copy.deepcopy(graph))]:
 if name=='profiling enabled':next(p for p in g['selected_closure'] if p['name']=='aspis-r1-cost-probe')['features'].append('detail-phases')
 try:validate(modified,g)
 except AssertionError as e:controls.append(dict(name=name,rejected=True,reason=str(e)))
 else:raise AssertionError('mutation accepted: '+name)
inputs={p:dict(sha256=sha(blob(p)),revision=base) for p in [feature_path,nef_path,'evidence/slice-q-fnptr-20261029/NEF_OBSERVER_CERTIFICATE.json','evidence/slice-q-fnptr-20261029/NEF_OBSERVER_TEST_RESULTS.json']}
out=dict(status='PASS',native_executions=0,route='source no-op reclassification under (z)(1); no trust removal',source=dict(path=source_path,revision=frozen,sha256=sha(src.encode())),inputs=inputs,controls=controls,model_roots=['AspisR1.NHU_Mark.result','AspisR1.NHU_Mark.frame','AspisR1.NHU_Mark.effects'],scope='deployed None observer; no Some/fn-pointer assertion or native verdict')
(E/'NHU_MARK_SOURCE.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(status='PASS',controls=len(controls))))
