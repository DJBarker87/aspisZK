import XRk_Association
open Aeneas Aeneas.Std Result
namespace XRk_GeometryMeasure
def remaining {T : Type} (it : core.slice.iter.Iter T) : Nat := it.slice.val.length-it.i

theorem advance {T : Type} (it next : core.slice.iter.Iter T) (value : T)
    (run : core.slice.iter.IteratorSliceIter.next it=ok (some value,next)) :
    remaining next < remaining it := by
  unfold core.slice.iter.IteratorSliceIter.next at run
  split at run
  · have same := congrArg Prod.snd (Result.ok.inj run)
    change {slice := it.slice, i := it.i+1} = next at same
    subst next
    unfold remaining
    omega
  · cases run
#print axioms advance
end XRk_GeometryMeasure
