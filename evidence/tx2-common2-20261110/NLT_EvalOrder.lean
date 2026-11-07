import NLT_SiteOrder
set_option autoImplicit false
noncomputable section
namespace NLT_EvalOrder
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free NLT_SiteOrder
theorem ordered {A : Type} (p : Program Event A) (n : Nat) (shape : Shape n p) :
 (∀ e∈(eval p).events,n≤rank e) ∧ (eval p).events.Pairwise (fun a b=>rank a<rank b) := by
 induction shape with
 | ret n value => exact ⟨by simp [eval],List.Pairwise.nil⟩
 | prim n reply next tail ih =>
   cases reply with
   | ok value => exact ih value
   | fail error => exact ⟨by simp [eval],List.Pairwise.nil⟩
   | div => exact ⟨by simp [eval],List.Pairwise.nil⟩
 | call n codec seed next bound tail ih =>
   cases seed with
   | ok value =>
     have rest:=ih value
     constructor
     · intro e member
       rcases List.mem_cons.mp member with equal|member
       · subst e;exact bound
       · have h:=rest.1 e member;omega
     · apply List.Pairwise.cons
       · intro e member;have h:=rest.1 e member;omega
       · exact rest.2
   | fail error => exact ⟨by intro e member;have equal:=List.mem_singleton.mp member;subst e;exact bound,by simp [eval]⟩
   | div => exact ⟨by intro e member;have equal:=List.mem_singleton.mp member;subst e;exact bound,by simp [eval]⟩
set_option pp.proofs false
#print ordered
#print axioms ordered
end NLT_EvalOrder
