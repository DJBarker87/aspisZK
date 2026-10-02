#!/usr/bin/env python3
"""Rebuild the exact R340 selected output raw wrappers from frozen R292 text."""
from pathlib import Path
import hashlib, json

HERE = Path(__file__).resolve().parent
WORKTREE = HERE.parents[1]
SOURCE = HERE / 'provenance/R292Funs.input.lean'
ORIGINAL = WORKTREE / '.r21-scratch/r305-batch-reverse-raw/provenance/R292Funs.input.lean'
EXPECTED = '4d40a5b7b540adec90efef80a5ed8a5b4403704b388506af21f357761d95aec4'
s = SOURCE.read_text()
sha = lambda b: hashlib.sha256(b).hexdigest()
assert sha(SOURCE.read_bytes()) == EXPECTED
assert sha(ORIGINAL.read_bytes()) == EXPECTED

clone_start = s.index('/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{impl core::clone::Clone')
clone_end = s.index('/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{impl core::cmp::PartialEq', clone_start)
clone_block = s[clone_start:clone_end]
assert 'def circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone.clone' in clone_block
assert 'def circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone :' in clone_block

start0 = '        let i3 := Slice.len xs\n'
start1 = '        let i5 := Slice.len ys\n'
end1 = '        ok (core.result.Result.Ok (ox2, oy2))\n'
pos0, pos1, posend = s.index(start0), s.index(start1), s.index(end1)
frag0, frag1 = s[pos0:pos1], s[pos1:posend]
assert frag0.endswith('        let ox2 := index_mut_back ix1\n')
assert frag1.endswith('        let oy2 := index_mut_back1 iy1\n')

head = '''import Aeneas.Std
import AspisR305BatchReverseRaw
import AspisR278PrivateInverseRaw

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR249R110Raw AspisR305BatchReverseRaw AspisR278PrivateInverseRaw

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

noncomputable section
namespace AspisR340BatchOutputRaw

'''
tail = '''
abbrev VecU32 := alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B
abbrev ResultVecU32 := Result VecU32

def selectedOutput0 (xs : Slice U32) (px2 : VecU32) (ix : U32) : ResultVecU32 := do
''' + frag0 + '''        ok ox2

def selectedOutput1 (ys : Slice U32) (py2 : VecU32) (iy : U32) : ResultVecU32 := do
''' + frag1 + '''        ok oy2

#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone.clone
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone
#print axioms selectedOutput0
#print axioms selectedOutput1

end AspisR340BatchOutputRaw
end
'''
output = head + clone_block + tail
(HERE / 'AspisR340BatchOutputRaw.lean').write_text(output)

# Source-exact evidence: save source line ranges and all selected original text.
lines = s.splitlines(keepends=True)
def line_no(offset): return s.count('\n', 0, offset) + 1
ranges = {
 'clone_declarations': [line_no(clone_start), line_no(clone_end)-1],
 'selectedOutput0_body': [line_no(pos0), line_no(pos1)-1],
 'selectedOutput1_body': [line_no(pos1), line_no(posend)-1],
}
(HERE / 'selected-source-fragments.txt').write_text(
 '=== exact R292 clone declarations, lines %d-%d ===\n%s\n'
 '=== exact selectedOutput0 body, lines %d-%d ===\n%s'
 '=== exact selectedOutput1 body, lines %d-%d ===\n%s'
 % (ranges['clone_declarations'][0],ranges['clone_declarations'][1],clone_block,
      ranges['selectedOutput0_body'][0],ranges['selectedOutput0_body'][1],frag0,
      ranges['selectedOutput1_body'][0],ranges['selectedOutput1_body'][1],frag1))

metadata = {
 'status':'mechanical raw staging; uncompiled',
 'source_path':str(SOURCE), 'source_sha256':EXPECTED,
 'output_sha256':sha(output.encode()), 'source_line_ranges':ranges,
 'selected_fragments_sha256':{'clone_declarations':sha(clone_block.encode()),'selectedOutput0_body':sha(frag0.encode()),'selectedOutput1_body':sha(frag1.encode())},
 'new_namespace':'AspisR340BatchOutputRaw',
 'copied_exact_declarations':['circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone.clone','circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone'],
 'wrappers':['selectedOutput0','selectedOutput1'],
 'allowed_source_adaptations':[],
 'bindings':{
  'B':'AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.B = Std.U32',
  'B.ZERO':'AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO',
  'Clone clone method and impl':'verbatim copied from the frozen R292 function source into R340 namespace',
  'batch_loop2':'AspisR305BatchReverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.batch_loop2',
  'batch_loop3':'AspisR305BatchReverseRaw.circle_norm.joined_inverse.line_norm.r110_norm.batch_loop3',
  'Slice.len / Iterator.rev.trait_default / Range DoubleEndedIterator / Vec.from_elem / Vec.index_mut':'Aeneas.Std imported declarations; bodies remain external to these copied fragments'
 },
 'source_boundary_and_control_flow':{
  'selectedOutput0':'begins at original `let i3 := Slice.len xs`; includes Vec.from_elem initialized from B.ZERO, reverse iterator [1, len(xs)), batch_loop2, index_mut at output index 0; returns `ok ox2`.',
  'selectedOutput1':'begins at original `let i5 := Slice.len ys`; includes Vec.from_elem initialized from B.ZERO, reverse iterator [1, len(ys)), batch_loop3, index_mut at output index 0; returns `ok oy2`.',
  'full_batch_guards':'The wrappers isolate these body fragments after the original guards and pair inverse. They do not contain, prove, or assert any full callback guard, validity branch, nonempty input check, or batch-result condition beyond Result propagation of the exact selected calls.',
  'traversal':'Both use the exact source reverse range `{ start := 1#usize, end := len }`; first calls loop2 and second loop3. No index or iterator expression was replaced.',
  'from_elem':'The exact original generic clone argument is used; implementation binding remains Aeneas.Std `alloc.vec.from_elem`.',
  'compiler_or_std_unresolved':'No compiler translation or semantic theorem is made. Std helper bodies/behavior are not copied or claimed; the wrappers retain their Aeneas.Std references.'
 },
 'axiom_reports':['#print axioms for both copied clone declarations and selectedOutput0/selectedOutput1 are emitted at file end. No Lean execution was run; output is not asserted.'],
 'limits':['No compilation.', 'No body/signature substitutions inside selected source fragments.', 'No full-batch guards, source-to-model semantics, or release claim.']
}
(HERE / 'raw-binding-audit.json').write_text(json.dumps(metadata,indent=2)+'\n')
print(json.dumps({'source_sha256':EXPECTED,'output_sha256':metadata['output_sha256'],'ranges':ranges,'fragment_hashes':metadata['selected_fragments_sha256']},indent=2))
