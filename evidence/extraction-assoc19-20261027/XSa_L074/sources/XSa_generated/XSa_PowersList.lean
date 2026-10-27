import XSa_PowersStep
open Aeneas Aeneas.Std Result ControlFlow
open XRo_Join_Carriers
set_option autoImplicit false
namespace XSa_PowersList

theorem paired (n : Nat) {N : Usize} (x : C.E) (hx : XRy_WideMultiply.Canonical x)
 (a : Array C.E N) (p : C.E) (hp : XRy_WideMultiply.Canonical p) (i : Usize)
 (remaining : i.val+n=N.val) :
 ∃ out pending xs,
 XRn_Join_Release.weights.powers_loop x a p i=ok (out,pending) ∧
 (pending=none ∨ pending=some out) ∧ XRn_Join_powers x n p=ok xs ∧
 out.val=a.val.take i.val++xs := by
 induction n generalizing a p i with
 | zero =>
   have hn : ¬i<N := by scalar_tac
   refine ⟨a,none,[],?_,Or.inl rfl,rfl,?_⟩
   · apply XRy_PowersLoop.done
     simp only [XRn_Join_Release.weights.powers_loop.body,if_neg hn]
   · rw [List.take_of_length_le (by rw [a.property];omega),List.append_nil]
 | succ n ih =>
   cases n with
   | zero =>
     refine ⟨a.set i p,some (a.set i p),[p],?_,Or.inr rfl,rfl,?_⟩
     · exact XRy_PowersLoop.done _ _ _ (XSa_PowersStep.last x p a i hx hp (by omega))
     · exact XSa_ArrayPrefix.last a i p (by omega)
   | succ m =>
     obtain ⟨j,p',hj,hp',em,hs⟩ := XSa_PowersStep.next x p a i hx hp (by omega)
     obtain ⟨out,pending,xs,hr,hpend,ex,hval⟩ := ih (a.set i p) p' hp' j (by omega)
     refine ⟨out,pending,p::xs,(XRy_PowersLoop.cont _ _ _ hs).trans hr,hpend,?_,?_⟩
     · simp only [XRn_Join_powers,em,ex,bind_tc_ok]
     · rw [hj,XSa_ArrayPrefix.write a i p (by omega)] at hval
       simpa only [List.append_assoc,List.cons_append,List.nil_append] using hval

#print axioms paired
end XSa_PowersList
