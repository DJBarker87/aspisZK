"""Final source/evidence gate; complete rows and partial rows remain distinct.

Run on the private build host after the focused audit and replay. This checks
the previously tested source bytes again, not a new native differential.
"""
from pathlib import Path
import json, hashlib

D = Path('/home/dombarker/project-offloads/codex-pv-rdb2-20261028')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(f): return json.loads((D/f).read_text())

checked = []
def check_tree(x):
    if isinstance(x, dict):
        if 'path' in x and 'file_sha256' in x:
            p = Path(x['path'])
            assert sha(p) == x['file_sha256'], str(p)
            checked.append({'path':str(p),'sha256':sha(p)})
        for v in x.values(): check_tree(v)
    elif isinstance(x, list):
        for v in x: check_tree(v)

bindings = ['V240-deployed-body-binding.json','V240-primitive-binding.json',
            'V247-deployed-body-binding.json','V238-deployed-body-binding.json',
            'stdlib-transports.json']
for f in bindings: check_tree(load(f))
frozen = load('resume-frozen-manifest.json')
objects = []
for r in frozen['modules']:
    source = D/'lean-sources'/(r['module']+'.lean')
    obj = D/'lean-objects'/(r['module']+'.olean')
    assert sha(source) == r['source_sha256'], r['module']
    assert obj.exists(), r['module']
    objects.append({'module':r['module'],'source_sha256':sha(source),
                    'object_sha256':sha(obj),'object_bytes':obj.stat().st_size})
for n in (41198,41199):
    r = load('final-receipts/'+str(n)+'.json')
    assert r['exit'] == 0 and r['swap'] == '0'
    assert r['print_axioms']
wrapper = load('wrapper-results.json')
assert any('V238' in r['rows'] and r['result']=='PASS' for r in wrapper['results'])

remaining = {
 'V229':'Concrete allocation/reallocation resource effects and complete per-call std association remain; Layout, padding, alignment, AtomicPtr and pointer transports are now available.',
 'V230':'Complete project checker/instantiation binding and concrete allocation/resource effects remain; Layout and pointer transport families alone do not close the row.',
 'V231':'Full SHA mutable core/buffer/output source association and its selected callback cone were not replayed in this owned cohort; constructor/copy laws alone do not close SHA.',
 'V239':'Complete original/copy multilinear source binding and allocation/resource instantiation remain; constant-seven finite validation does not cover arbitrary columns.',
 'V256':'Concrete gamma sampler source/call association, every mutable restoration continuation and the complete selected callback cone remain; generic current-store restoration laws do not establish that instance.',
 'V257':'Concrete ordinary sampler source/call association, every mutable restoration continuation and the complete selected callback cone remain; generic current-store restoration laws do not establish that instance.',
 'V258':'Typed RawVec<T,A>::new_in wrapper association, allocator/resource family, and complete weights instantiation remain; the old mapping selected RawVecInner<A>::new_in instead.',
 'V259':'Box::new intrinsic lowering, allocation freshness/initialization and concrete resource-family/source association remain; allocator shim argument/effect transport is insufficient.'}
closed = {
 'V238':('PV_DL_CtSelected.selected_native','PV_RDB2_ResumeReplay.ct_wrapper',
          'Complete Ct wrapper/default/copy boundary; finalizer and TRUNC_SIDE remain explicit complete-Result parameters; full32 and output shape <=32 retained.'),
 'V240':('PV_RDB2_Compress.complete/installed','PV_RDB2_ResumeReplay.compressor',
          'Actual host_semantic caller invokes prover_shared index-loop helper; five emitted arithmetic operations selected literally; arbitrary raw words and all slice lengths, Result errors/divergence retained.'),
 'V247':('PV_RDB2_SumDeployed.complete/installed','PV_RDB2_ResumeReplay.sum',
          'Exact then/copied/fold body; invalid length performs no read; valid length is 1024 QM31 cells; original backing slice retained.')}
rows=[]
for row in sorted(set(remaining)|set(closed)):
    out={'row':row,'disposition':'RESTORED' if row in closed else 'SUSPENDED',
         'finding':False,'source_bindings':bindings,
         'new_source_file_checks':len(checked),'audit':41198,'focused_replay':41199,
         'endpoint_premises_removed':0,'endpoint_premises_added':0,'endpoint_premises_changed':0}
    if row in closed:
        law,replay,boundary=closed[row]
        out.update(evidence_class='structural (K-1 substitute)',law=law,replay_law=replay,boundary=boundary,
                   retained='Rust reference/Copy/intrinsic and compiler-cohort correspondence boundary; E1/E2, RunJoin, proof-account route, L1/L2/L3; no endpoint credit')
    else: out.update(evidence_class='partial structural transport; no restored credit',exact_reason=remaining[row])
    rows.append(out)
out={'rows':rows,'checked_files':checked,'owned_objects':objects,
     'source_bindings':[{ 'path':f,'sha256':sha(D/f)} for f in bindings],
     'original_conservative_envelopes':'Retained as historical inventory, not a dynamic call certificate; exclusions are recorded at each precise consumed helper/callback boundary.',
     'compiler_boundary':'Retained owner boundary D381/D386; this source-level gate is not a machine-code or privacy theorem.'}
(D/'resume-row-gate.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS final source hashes and owned proof objects; 3 RESTORED structural (K-1 substitute), 8 SUSPENDED; endpoint premises removed 0')
