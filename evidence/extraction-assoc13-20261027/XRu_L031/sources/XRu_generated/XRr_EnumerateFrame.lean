import XRr_MutIteratorFrame
open Aeneas Aeneas.Std Result XRk_ResultTools XRn_Join_Release
set_option autoImplicit false
namespace XRr_EnumerateFrame
abbrev It (T : Type) := core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T)
theorem source {T : Type} (dict : core.iter.traits.iterator.Iterator (core.slice.iter.IterMut T) T)
 (it next : It T) (o : Option (Usize × T)) (back : It T → Option (Usize × T) → It T)
 (run : XRn_Join_enumerateNext dict it=ok (o,next,back)) :
 next.iter.slice.length=it.iter.slice.length ∧
 (∀ target item, (back target item).iter.slice.length=target.iter.slice.length) ∧
 (match o with | none => True | some _ => next.iter.i=it.iter.i+1 ∧ it.iter.i< it.iter.slice.length) := by
 unfold XRn_Join_enumerateNext at run
 obtain ⟨v,next0,hnext,run⟩ := pair_bind_success _ _ _ run
 rcases next0 with ⟨it0,restore⟩
 have frame := XRr_MutIteratorFrame.source it.iter it0 v restore hnext
 obtain ⟨n,_,run⟩ := bind_success _ _ _ run
 cases Result.ok.inj run
 refine ⟨frame.1,?_,?_⟩
 · intro target item
   exact frame.2.1 target.iter (item.map Prod.snd)
 · cases v <;> exact frame.2.2
#print axioms source
end XRr_EnumerateFrame
