#!/usr/bin/env python3
"""Retain complete emitted resume code; bind only existing source/runtime names."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
tool=Path(__file__).resolve().parent;lean=tool.parents[1]/'lean';raw=tool/'rho-resume-inlined-generated'
s=(raw/'Types.lean').read_text();assert 'bytes : Slice Std.U8' in s and '«at» : Std.Usize' in s
full=tool/'rho-empty-reserve-source/vec-mod.rs'
std=(full if full.exists() else tool/'rho-empty-reserve-source/vec-used-slices.rs').read_text();i=std.index("IntoIterator for &'a mut Vec<T, A>");j=std.index('\n}',i);wrapper=std[i:j];assert 'fn into_iter(self) -> Self::IntoIter {\n        self.iter_mut()\n    }' in wrapper
outputs={
'AspisR1RhoResumeInlined/Types.lean':'''import AspisR1RhoReader.Types
namespace AspisR1RhoResumeInlined
abbrev field.M31 := AspisR1CuRho.field.M31
abbrev field.CM31 := AspisR1CuRho.field.CM31
abbrev field.QM31 := AspisR1CuRho.field.QM31
abbrev verifier.Error := AspisR1CuRho.verifier.Error
abbrev verifier.Reader := AspisR1CuRho.verifier.Reader
end AspisR1RhoResumeInlined
''',
'AspisR1RhoResumeInlined/FunsExternal.lean':'''import AspisR1RhoResumeInlined.Types
import AspisR1RhoReader.FunsExternal
namespace AspisR1RhoResumeInlined
open Aeneas Aeneas.Std Result
abbrev verifier.Error.Checkpoint := AspisR1CuRho.verifier.Error.Checkpoint
abbrev core.option.Option.ok_or := @AspisR1CuRho.core.option.Option.ok_or
abbrev field.QM31.from_le_bytes := AspisR1CuRho.field.QM31.from_le_bytes

/-- Exact std IntoIterator for &mut Vec: self.iter_mut(), with the inherited
Vec dereference and slice iterator plus their original writebacks. -/
def MutAVec.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
    {T : Type} (_A : Type) (weights : alloc.vec.Vec T) :
    Result (core.slice.iter.IterMut T × (core.slice.iter.IterMut T → alloc.vec.Vec T)) := do
  let (slice,vecBack) := alloc.vec.Vec.deref_mut weights
  let (iter,iterBack) ← core.slice.Slice.iter_mut slice
  .ok (iter,fun it => vecBack (iterBack it))
end AspisR1RhoResumeInlined
''',
'AspisR1RhoResumeInlined/Funs.lean':(raw/'Funs.lean').read_text()}
for n,s in outputs.items():
 p=lean/n
 if a.check:assert p.read_text()==s,n
 else:p.parent.mkdir(exist_ok=True,parents=True);p.write_text(s)
print(json.dumps({'check':a.check,'function_body_changes':0,'outputs':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in outputs.items()}}))
