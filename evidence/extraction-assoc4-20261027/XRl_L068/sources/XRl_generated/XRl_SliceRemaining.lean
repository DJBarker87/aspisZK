import XRk_GeometryMeasure
open Aeneas Aeneas.Std Result
namespace XRl_SliceRemaining
open XRk_GeometryMeasure

theorem terminal {T : Type} (s next : core.slice.iter.Iter T)
    (run : core.slice.iter.IteratorSliceIter.next s=ok (none,next)) : remaining s=0 := by
  unfold core.slice.iter.IteratorSliceIter.next at run
  split at run
  · cases run
  · unfold remaining
    omega

theorem advance {T : Type} (s next : core.slice.iter.Iter T) (item : T)
    (run : core.slice.iter.IteratorSliceIter.next s=ok (some item,next)) :
    remaining s=remaining next+1 := by
  unfold core.slice.iter.IteratorSliceIter.next at run
  split at run
  · have same := congrArg Prod.snd (Result.ok.inj run)
    change {slice := s.slice,i := s.i+1}=next at same
    subst next
    dsimp only [remaining]
    omega
  · cases run
#print axioms terminal
#print axioms advance
end XRl_SliceRemaining
