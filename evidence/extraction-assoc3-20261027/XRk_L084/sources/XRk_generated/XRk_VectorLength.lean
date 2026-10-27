import XRk_Association
open Aeneas Aeneas.Std Result
namespace XRk_VectorLength
#print alloc.vec.FromIteratorVec.iterToList
#print core.iter.range.UScalarStep.forward_checked

theorem push {T : Type} (old next : alloc.vec.Vec T) (value : T)
    (run : alloc.vec.Vec.push old value=ok next) : next.val.length=old.val.length+1 := by
  unfold alloc.vec.Vec.push at run
  split at run
  · have same := congrArg (fun v : alloc.vec.Vec T => v.val.length) (Result.ok.inj run)
    simpa only [List.length_concat] using same.symm
  · cases run
#print axioms push
end XRk_VectorLength
