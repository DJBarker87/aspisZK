import XRx_ValueOwned
import XRr_EnumerateFrame
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release
set_option autoImplicit false
namespace XRx_FinishStep
abbrev Q := aspis_core.field.QM31
abbrev It := XRr_EnumerateFrame.It Q
abbrev Back := It → It
/-- The exact mutable-iterator body after its bounded value bridge. The
returned restoration writes the new weight; the old element is discarded. -/
theorem source (b : verifier.BatchedWeights) (it : It) (back : Back)
 (i : Usize) (old : Q) (next : It)
 (restore : It → Option (Usize × Q) → It)
 (read : XRn_Join_enumerateNext
  (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT Q) it=
  ok (some (i,old),next,restore)) (bound : i.val<b.raw.length) :
 ∃ value : Q,
 verifier.BatchedWeights.value b i=ok value ∧
 verifier.BatchedWeights.finish_loop.body b it back=
 ok (.cont (next,fun target => back (restore target (some (i,value))))) ∧
 S8OwnedP6.value_owned b.raw.val[i.val]=ok (XRx_ValueOwned.oldQ value) := by
 obtain ⟨a,c,d,e,w,x,y,z,_,value,_,_,_,_⟩ := XRx_ValueRow.source b i bound
 refine ⟨⟨⟨w,x⟩,⟨y,z⟩⟩,value,?_,?_⟩
 · unfold verifier.BatchedWeights.finish_loop.body
   rw [read,bind_tc_ok]
   change (do let q ← verifier.BatchedWeights.value b i
              ok (@ControlFlow.cont (It × Back) Back
                (next,fun target => back (restore target (some (i,q)))))) = _
   rw [value]
   rfl
 · rw [←XRx_ValueOwned.source b i bound,value]
   rfl
#print axioms source
end XRx_FinishStep
