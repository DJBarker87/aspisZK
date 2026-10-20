#!/usr/bin/env python3
"""Check exact source pins and ordered call-clause correspondence for the R17 query-values cut.
This is a provenance/cut checker, not a proof that arbitrary operations or the whole caller are equivalent.
"""
from pathlib import Path
import hashlib, json
ROOT=Path(__file__).resolve().parent
GEN=ROOT/'sources/GeneratedFuns-v1.lean'
ADAPT=ROOT/'sources/R17QueryValuesEntryActualDefs-v22.lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(GEN)=='7719ef4e98cbfe031d0bbcdc3b3bc9f320dd455752f728a130333d5f24084533'
assert sha(ADAPT)=='cc6f20c465a77bac9a083d319b2e9f8b1950ab85554ef2c50ef772e117b750d7'
g=GEN.read_text(); a=ADAPT.read_text()
gstart=g.index('def verifier.query_values_entry\n')
gend=g.index('\nend AspisR1QueryGeometryActual',gstart)
gbody=g[gstart:gend]
astart=a.index('def queryValuesEntry (q : Std.U32)')
aend=a.index('\ntheorem fibreIndexNew_success',astart)
obody=a[astart:aend]
source_clauses=[
 'UScalar.cast .Usize query', 'domain.FibreIndex.new u',
 'fast_domain.fibre_point val', 'u / 4#usize', 'i * 4#usize',
 'domain.FibreIndex.new i1', 'fast_domain.line_node val1',
 'i * 4#usize', 'i2 + 3#usize', 'domain.FibreIndex.new i3',
 'fast_domain.line_node val2', 'field.M31.mul line_x line_x',
 'field.M31.double m', 'field.M31.sub m1 field.M31.ONE',
 'Array.make 5#usize', 'core.slice.Slice.iter s',
 'CoreIterTraitsIteratorIteratorSharedAT.any', 'if b',
]
adapter_clauses=[
 'UScalar.cast .Usize q', 'fibreIndexNew u',
 'fast_domain.fibre_point actualCMOps val', 'UScalar.div u (4#usize)',
 'UScalar.mul i (4#usize)', 'fibreIndexNew i1',
 'line_node actualCMOps actualM31Ops val1', 'UScalar.mul i (4#usize)',
 'UScalar.add i2 (3#usize)', 'fibreIndexNew i3',
 'line_node actualCMOps actualM31Ops val2', 'actualM31Ops.mul line_x line_x',
 'actualM31Ops.double m', 'actualM31Ops.sub m1 (1#u32)',
 'Array.make 5#usize', 'core.slice.Slice.iter s', 'anyCheck it', 'if b',
]
def ordered(text, parts):
    pos=-1; found=[]
    for part in parts:
        i=text.find(part,pos+1)
        assert i>=0, f'missing/out-of-order clause: {part}'
        found.append(i);pos=i
    return found
ordered(gbody,source_clauses); ordered(obody,adapter_clauses)
for theorem in ['sourceMapTryFromResidual_eq_directMatch','queryErrorBranch_matches_emitted_closure',
                'successful_queryValuesEntry_core','successful_queryValuesEntry_stored']:
    assert f'theorem {theorem}' in a
assert 'core.result.Result.map_err' in gbody and 'CoreOpsTry.branch' in gbody and 'from_residual' in gbody
assert 'sourceMapTryFromResidual' in a and 'sourceDirectMatch' in a
assert 'anyCheck' in obody and 'anyCheck it = .ok (false, it\')' in a
result={
 'generated_Funs_sha256':sha(GEN),'generated_function_lines':'verifier.query_values_entry, lib.rs 381:0-391:1',
 'adapted_source_sha256':sha(ADAPT),'ordered_source_clauses':source_clauses,
 'ordered_adapter_clauses':adapter_clauses,
 'checks_passed':['pinned source bytes','ordered call-clause scan','map_err/Try/from_residual presence in source','Lean-proved map/Try/direct-match equation present','actual any call retained as parameter','stored-output theorem present'],
 'scope_limit':'This checker validates pinned text/order and theorem-presence only. It does not prove full generated-body identity, whole QueryGeometry::for_range correspondence, actual iterator-any implementation semantics, or field-op implementation identity.'}
(ROOT/'source-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
