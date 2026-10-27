import XRl_ReverseDomain
import XRk_ResultTools
open Aeneas Aeneas.Std Result
namespace XRl_Adapter
abbrev Back (T : Type) := core.slice.iter.IterMut T → Option T → core.slice.iter.IterMut T

theorem next_back_cursor {T : Type} (s next : core.slice.iter.IterMut T) (v : Option T) (back : Back T)
    (run : core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back s=ok (v,next,back)) :
    next.i=s.i := by
  unfold core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back at run
  obtain ⟨value,state,_,run⟩ := XRk_ResultTools.pair_bind_success _ _ _ run
  have same := congrArg (fun r => r.2.1.i) (Result.ok.inj run)
  exact same.symm

theorem next_back_restoration_cursor {T : Type} (s next : core.slice.iter.IterMut T) (v : Option T) (back : Back T)
    (run : core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back s=ok (v,next,back))
    (updated : core.slice.iter.IterMut T) (item : Option T) (same : updated.i=s.i) :
    (back updated item).i=s.i := by
  unfold core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back at run
  obtain ⟨value,state,_,run⟩ := XRk_ResultTools.pair_bind_success _ _ _ run
  have backeq := congrArg (fun r => r.2.2) (Result.ok.inj run)
  dsimp only at backeq
  rw [←backeq]
  cases item with
  | none => exact same
  | some x =>
    split
    · exact same
    · rfl
#print axioms next_back_cursor
#print axioms next_back_restoration_cursor
end XRl_Adapter
