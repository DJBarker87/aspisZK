import XRn_Join_Funs
import XRk_ResultTools
open Aeneas Aeneas.Std Result XRk_ResultTools
set_option autoImplicit false
namespace XRr_MutIteratorFrame
theorem source {T : Type} (it next : core.slice.iter.IterMut T) (o : Option T)
 (back : core.slice.iter.IterMut T → Option T → core.slice.iter.IterMut T)
 (run : core.slice.iter.IteratorIterMut.next it=ok (o,next,back)) :
 next.slice.length=it.slice.length ∧
 (∀ target item, (back target item).slice.length=target.slice.length) ∧
 (match o with | none => True | some _ => next.i=it.i+1 ∧ it.i<it.slice.length) := by
 unfold core.slice.iter.IteratorIterMut.next at run
 split at run
 · rename_i active
   cases Result.ok.inj run
   refine ⟨rfl,?_,rfl,active⟩
   intro target item
   cases item <;> simp only [Slice.setAtNat_length]
 · cases Result.ok.inj run
   exact ⟨rfl,by intros;rfl,True.intro⟩
#print axioms source
end XRr_MutIteratorFrame
