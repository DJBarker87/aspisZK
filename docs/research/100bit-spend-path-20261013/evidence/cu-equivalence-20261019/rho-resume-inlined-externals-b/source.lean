import AspisR1RhoResumeInlined.Types
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
