import NMP_PrepareState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Source occurrence7: prepared; complete reply and writeback at SAME arguments. -/
theorem occurrence7 {H W : Type} (c : Calls) (s : Parent H W) (v : verifier.View) (sem : r1_semantic.Verified H) :
 step c (.prepared s v sem) = (do
   let out ← invoke "TX1:179/Prepared_new" (sem,v,s.hash,s.scratch)
     (c.c3 s.digest sem v s.hash s.scratch)
   pure (.inl out)) := rfl
#print axioms occurrence7
end AspisR1.NMP_PrepareSteps
