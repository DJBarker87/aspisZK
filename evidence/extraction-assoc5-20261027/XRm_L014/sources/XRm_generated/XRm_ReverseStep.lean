import XRl_ReverseCursor
open Aeneas Aeneas.Std Result
namespace XRm_Reverse
abbrev Rev (T : Type) := core.iter.adapters.rev.Rev (core.slice.iter.IterMut T)
theorem cursor {T : Type}
    (d : core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.IterMut T) T)
    (s next : Rev T) (v : Option T) (restore : Rev T → Rev T)
    (write : Rev T → Option T → Rev T)
    (run : XRk_reverseNext d s=ok (v,next,restore,write)) : next.iter.i=s.iter.i := by
  unfold XRk_reverseNext at run
  obtain ⟨value,state,hstep,run⟩ := XRk_ResultTools.pair_bind_success _ _ _ run
  rcases state with ⟨it,back⟩
  have same := congrArg (fun r => r.2.1.iter.i) (Result.ok.inj run)
  exact same.symm.trans (XRl_Adapter.next_back_cursor s.iter it value back hstep)
#print axioms cursor
end XRm_Reverse
