#!/usr/bin/env python3
"""Deterministically stage the R292 first-vector initialization fragment; never compile."""
import hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent
SRC=ROOT/'docs/research/v8-full-view-zk-20260912/evidence/r305-current-batch-reverse-raw/raw-adapter-audit/provenance/R292Funs.input.lean'
s=SRC.read_text()
root_sig='def circle_norm.joined_inverse.line_norm.r110_norm.batch\n'
assert s.count(root_sig)==1
root_start=s.index(root_sig)
root_end=s.find('\n/--',root_start+len(root_sig))
if root_end<0: root_end=len(s)
root=s[root_start:root_end]
start_marker='        let i1 := Slice.len xs\n'
end_marker='        let i2 := Slice.len ys\n'
assert root.count(start_marker)==1, root.count(start_marker)
assert root.count(end_marker)==1, root.count(end_marker)
start=root.index(start_marker)
end=root.index(end_marker,start)
fragment=root[start:end]
assert fragment.endswith('        let px2 ←\n          circle_norm.joined_inverse.line_norm.r110_norm.batch_loop0 iter px1\n')
header='''import Aeneas.Std
import AspisR318BatchPrefixRaw
open Aeneas Aeneas.Std Result ControlFlow Error AspisR249R110Raw AspisR316SliceLastRaw AspisR318BatchPrefixRaw

noncomputable section
namespace AspisR328PrefixInitializationRaw

def selectedPrefix0 (xs : Slice U32) : Result (alloc.vec.Vec U32) := do
'''
tail='''        .ok px2

#print axioms selectedPrefix0

end AspisR328PrefixInitializationRaw
end
'''
target=OUT/'AspisR328PrefixInitializationRaw.lean'
target.write_text(header+fragment+tail)
assert target.read_text().count(fragment)==1
# Exact source-order reference census; entries are names/calls, not semantic dependencies.
refs=[
 'Slice.len xs',
 'alloc.vec.Vec.with_capacity B i1',
 'Slice.index_usize xs 0#usize',
 'alloc.vec.Vec.push px b3',
 'core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice B) xs { start := 1#usize }',
 'SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter s',
 'circle_norm.joined_inverse.line_norm.r110_norm.batch_loop0 iter px1',
]
report={
 'scope':'Mechanical source-fragment staging only; not compiled.',
 'source_file':str(SRC.relative_to(ROOT)),
 'source_sha256':hashlib.sha256(SRC.read_bytes()).hexdigest(),
 'source_root':'circle_norm.joined_inverse.line_norm.r110_norm.batch',
 'source_root_occurrences':1,
 'source_line_start':s[:root_start+start].count('\n')+1,
 'source_line_end_inclusive':s[:root_start+end].count('\n'),
 'start_boundary':'let i1 := Slice.len xs',
 'end_boundary_exclusive':'let i2 := Slice.len ys',
 'snippet_sha256':hashlib.sha256(fragment.encode()).hexdigest(),
 'snippet_source_text':fragment,
 'builder_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'target_file':str(target.relative_to(ROOT)),
 'target_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
 'target_fragment_exactly_source':target.read_text().count(fragment)==1,
 'replacement_count':0,
 'appended_harness_only':['definition wrapper selectedPrefix0(xs)', 'return .ok px2', 'namespace/import header', '#print axioms selectedPrefix0'],
 'reference_census_in_order':refs,
 'full_batch_guard_included':False,
 'standalone_rust_root':False,
 'boundary':'This is only the source-contiguous first-vector initialization fragment, presumed within the branch after validations in the full root. No proof of those guards or caller conditions is made.',
 'compiled':False,
 'axioms_printed':False
}
(OUT/'raw-adapter.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['source_sha256','source_line_start','source_line_end_inclusive','snippet_sha256','target_sha256','target_fragment_exactly_source','replacement_count']},indent=2))
