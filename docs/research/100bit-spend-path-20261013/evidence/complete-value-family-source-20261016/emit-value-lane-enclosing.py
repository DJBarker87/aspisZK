from pathlib import Path
import hashlib,json
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path')
p=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean'
s=p.read_text();prefix='pool_v1.pair_forest_semantic_terminal.'
start=s.index('def '+prefix+'add_value_lanes\n');end=s.index('\n/-- ',start)
body=s[start:end].rstrip()+'\n'
mapping={
 prefix+'add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31':'AspisR1SelectedMaskProbe.'+prefix+'add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31',
 prefix+'add_value_lanes_loop0':'AspisR1SelectedMaskProbe.'+prefix+'add_value_lanes_loop0',
 prefix+'add_value_lanes_loop1':'AspisR1SelectedMaskProbe.'+prefix+'add_value_lanes_loop1',
 prefix+'add_value_lanes_loop2':'AspisR1SelectedMaskProbe.'+prefix+'add_value_lanes_loop2',
 prefix+'add_value_lanes_loop3':'AspisR1SelectedMaskProbeIndexed.'+prefix+'add_value_lanes_loop3',
 prefix+'reconstruct_10':'AspisR1SelectedMaskProbeIndexed.'+prefix+'reconstruct_10',
 prefix+'add_preweighted':'AspisR1PreweightedCandidate.'+prefix+'add_preweighted',
 prefix+'VALUE_AUXILIARY_BLOCK':'AspisR1SelectedMaskProbe.'+prefix+'VALUE_AUXILIARY_BLOCK',
 'pool_v1.pair_forest_copy_terminal.Selectors.row':'AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors.row',
}
import re
pattern=re.compile('|'.join(re.escape(k) for k in sorted(mapping,key=len,reverse=True)))
counts={k:len(re.findall(re.escape(k),body)) for k in mapping}
adapted=pattern.sub(lambda m:mapping[m.group()],body)
inverse=re.compile('|'.join(re.escape(v) for v in sorted(mapping.values(),key=len,reverse=True)))
reverse={v:k for k,v in mapping.items()}
assert inverse.sub(lambda m:reverse[m.group()],adapted)==body
header='''import SelectorValueLaneGeneratedSlice
import SelectorValueLaneIndexedSlice
import SelectorValueLaneLoops012Slice
import PreweightedLoopSlice
import SelectorArrayMapRuntimeSlice

/-! Exact generated enclosing add_value_lanes declaration from the sealed
indexed source candidate. Only helper-reference qualification and the enclosing
namespace are adapted to the already checked isolated source modules. The
adapter is invertible; it does not replace the function body with a model. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ValueLaneCandidate
open AspisR1SelectedMaskProbe

'''
out=header+adapted+'\nend AspisR1ValueLaneCandidate\n'
q=Path('/tmp/ValueLaneEnclosingSlice.lean');q.write_text(out)
hashof=lambda b:hashlib.sha256(b).hexdigest()
manifest={'raw_generated_path':str(p.relative_to(repo)),'raw_generated_sha256':hashof(p.read_bytes()),'raw_declaration_sha256':hashof(body.encode()),'adapted_declaration_sha256':hashof(adapted.encode()),'module_sha256':hashof(q.read_bytes()),'namespace':'AspisR1ValueLaneCandidate','helper_reference_map':mapping,'original_reference_counts':counts,'inverse_recovers_exact_declaration':True,'generator_sha256':hashof(Path(__file__).read_bytes())}
Path('/tmp/ValueLaneEnclosingSlice.manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(manifest['module_sha256'])
