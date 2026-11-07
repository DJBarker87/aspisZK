import NMP_PrepareState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Source occurrence6: mark; complete reply and writeback at SAME arguments. -/
theorem occurrence6 {H W : Type} (c : Calls) (s : Parent H W) (v : verifier.View) (sem : r1_semantic.Verified H) :
 step c (.mark s v sem) = (do
   let _ ← invoke "TX1:191/mark" (s.observer,verifier.Phase.Semantic)
     (c.c4 s.observer verifier.Phase.Semantic)
   pure (.inr (.prepared s v sem))) := rfl
#print axioms occurrence6
end AspisR1.NMP_PrepareSteps
