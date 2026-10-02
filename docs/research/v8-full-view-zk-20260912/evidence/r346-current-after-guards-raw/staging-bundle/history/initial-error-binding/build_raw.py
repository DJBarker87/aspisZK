#!/usr/bin/env python3
"""Rebuild the R346 after-guards wrapper from frozen R292 generated source."""
from pathlib import Path
import hashlib, json

HERE=Path(__file__).resolve().parent
WORKTREE=HERE.parents[1]
SOURCE=HERE/'provenance/R292Funs.input.lean'
ORIGINAL=WORKTREE/'.r21-scratch/r305-batch-reverse-raw/provenance/R292Funs.input.lean'
ORIGINAL_R292_TYPES=WORKTREE/'.r21-scratch/r305-batch-reverse-raw/provenance/R292Types.input.lean'
ORIGINAL_R156_TYPES=WORKTREE/'docs/research/v8-full-view-zk-20260912/lean/AspisR156FullFreeze/Types.lean'
R292_TYPES=HERE/'provenance/R292Types.input.lean'
R156_TYPES=HERE/'provenance/AspisR156FullFreeze.Types.lean'
EXPECTED_FUNS='4d40a5b7b540adec90efef80a5ed8a5b4403704b388506af21f357761d95aec4'
EXPECTED_R292_TYPES='972adf9e51991e13dee2e4f12621af6ba2ae613c04220bc7588ab3c8147ac833'
EXPECTED_R156_TYPES='c8571b518bfb09350cf54b971838c284cd4c188296c356de0ebcafb34a6e3bd7'
sha=lambda x:hashlib.sha256(x).hexdigest()
for path,expected in ((SOURCE,EXPECTED_FUNS),(ORIGINAL,EXPECTED_FUNS),(R292_TYPES,EXPECTED_R292_TYPES),(ORIGINAL_R292_TYPES,EXPECTED_R292_TYPES),(R156_TYPES,EXPECTED_R156_TYPES),(ORIGINAL_R156_TYPES,EXPECTED_R156_TYPES)):
 assert sha(path.read_bytes())==expected,(str(path),sha(path.read_bytes()))
s=SOURCE.read_text()
start='        let i1 := Slice.len xs\n'
end='        ok (core.result.Result.Ok (ox2, oy2))\n'
p0=s.index(start); p1=s.index(end,p0)+len(end)
fragment=s[p0:p1]
assert fragment.endswith(end)
assert s.count(start)==1 and s.count(end)==1

head='''import Aeneas.Std
import AspisR318BatchPrefixRaw
import AspisR305BatchReverseRaw
import AspisR278PrivateInverseRaw
import AspisR340BatchOutputRaw
import AspisR156FullFreeze.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR249R110Raw AspisR318BatchPrefixRaw AspisR305BatchReverseRaw
open AspisR278PrivateInverseRaw AspisR340BatchOutputRaw AspisR156FullFreeze

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

noncomputable section
namespace AspisR346AfterGuardsRaw

def selectedAfterGuards (xs ys : Slice U32) :
    Result (core.result.Result (VecU32 × VecU32) AspisR156FullFreeze.Error) := do
'''
tail='''

#print axioms selectedAfterGuards

end AspisR346AfterGuardsRaw
end
'''
output=head+fragment+tail
(HERE/'AspisR346AfterGuardsRaw.lean').write_text(output)

def line_no(off):return s.count('\n',0,off)+1
metadata={
 'status':'mechanical wrapper staging; uncompiled',
 'source_path':str(SOURCE),'source_sha256':EXPECTED_FUNS,
 'source_fragment_line_range_inclusive':[line_no(p0),line_no(p1)-1],
 'fragment_sha256':sha(fragment.encode()),'output_sha256':sha(output.encode()),
 'namespace':'AspisR346AfterGuardsRaw','wrapper':'selectedAfterGuards',
 'exact_imports':['Aeneas.Std','AspisR318BatchPrefixRaw','AspisR305BatchReverseRaw','AspisR278PrivateInverseRaw','AspisR340BatchOutputRaw','AspisR156FullFreeze.Types'],
 'bindings':{
  'B':'AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.B = Std.U32',
  'clone instance':'AspisR340BatchOutputRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone',
  'B.ZERO and B.inv':'AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO / B.inv',
  'B.input/add/sub/mul/reduce and P110':'AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm existing raw definitions',
  'batch_loop0/batch_loop1':'AspisR318BatchPrefixRaw.circle_norm.joined_inverse.line_norm.r110_norm',
  'batch_loop2/batch_loop3':'AspisR305BatchReverseRaw.circle_norm.joined_inverse.line_norm.r110_norm',
  'selectedOutput0/selectedOutput1 and VecU32':'AspisR340BatchOutputRaw',
  'Slice.last':'AspisR316SliceLastRaw imported through AspisR318BatchPrefixRaw',
  'Slice.len/is_empty/iter, vector, iterator adapters, collection, and option operations':'Aeneas.Std imported names referenced directly by the unchanged fragment'
 },
 'error_binding_audit':{
  'R292_source_definition':{'input_sha256':EXPECTED_R292_TYPES,'lean_name':'AspisR292PrivateBatch.Error','source':'../relation_callback.rs:62:27-62:101','constructors':['Length','Canonical','Sampler','Shape','Authentication','Terminal','Domain'],'attribute':'@[discriminant isize]'},
  'existing_candidate_binding':{'input_sha256':EXPECTED_R156_TYPES,'lean_name':'AspisR156FullFreeze.Error','source':'../relation_callback.rs:62:27-62:101','constructors':['Length','Canonical','Sampler','Shape','Authentication','Terminal','Domain'],'discriminant_instance':'instR156CallbackError maps constructors 0 through 6'},
  'wrapper_choice':'Uses existing AspisR156FullFreeze.Error as the inner core.result.Result error parameter; the exact extracted R292 declaration is a distinct Lean declaration in AspisR292PrivateBatch and its generated Types module is not imported here.',
  'uncertainty':'The compared declarations have identical recorded Rust source span, constructor names/order, and R156 has the explicit 0..6 discriminant instance; they are not definitionally the same namespaced Lean type. The selected suffix constructs only core.result.Result.Ok and never constructs an inner Error. No equivalence theorem or error-semantics claim is made; lead review must accept or revise this binding before compilation.'
 },
 'source_boundary':{
  'start':'Original line 527: else-branch body starts at `let i1 := Slice.len xs`, immediately after the source checks ending with `if b2 then ok (core.result.Result.Err Error.Domain) else` at lines 524-526.',
  'end':'Original line 605: includes the final `ok (core.result.Result.Ok (ox2, oy2))` line in full.',
  'guards_excluded':'The wrapper begins inside the validated else branch. It does not include or prove either input is nonempty, the earlier chain/any predicate, or the b2/error branch.',
  'operations_preserved':'All operations from vector capacity/push and prefix loops through Slice.last/unwrap, B field calls, zero-vector allocation, reverse loops, index-zero writes, and final nested Result.Ok are the contiguous unchanged source fragment. No helper or body replacement is performed.',
  'traversal':'The copied fragment explicitly constructs prefix iterators from slice ranges beginning at 1, then reverse range iterators with start 1 and end len for loop2/loop3. These are recorded syntactically; no traversal theorem is claimed.',
  'std_from_elem':'Uses the exact R340 Clone instance name in the fragment; allocation remains the Aeneas.Std `alloc.vec.from_elem` binding.',
  'compiler_unresolved':'No compiler/Lean compilation was run; source-to-model semantics and correspondence of imported Std helpers remain unresolved.'
 },
 'axiom_report':'One #print axioms selectedAfterGuards command is emitted. No output is claimed because no Lean compile was run.',
 'limits':['No compile.','No guard or full-callback theorem.','No error-type equivalence claim.','No tracked changes, staging, or commit.']
}
(HERE/'raw-binding-audit.json').write_text(json.dumps(metadata,indent=2)+'\n')
(HERE/'selected-source-fragment.txt').write_text(
  f'=== R292 validated branch exact fragment, lines {line_no(p0)}-{line_no(p1)-1} ===\n'+fragment)
print(json.dumps({'source_sha256':EXPECTED_FUNS,'fragment_sha256':metadata['fragment_sha256'],'output_sha256':metadata['output_sha256'],'line_range':metadata['source_fragment_line_range_inclusive'],'error_binding_uncertain':True},indent=2))
