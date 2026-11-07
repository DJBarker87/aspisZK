import NMP_PrepareState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSteps
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMT_CallTree (Code invoke erase)
/-- Source occurrence5: observed; complete reply and writeback at SAME arguments. -/
theorem occurrence5 {H W : Type} (c : Calls) (s : Parent H W) (v : verifier.View) :
 step c (.observed s v) = (do
   let r ← invoke "TX1:137/verify_observed" (s.publicValue,v.semantic,s.hash,s.observer)
     (NMP_prepare.r1_semantic.verify_observed c.c5 c.c6 c.c7 c.c8 c.c9 s.digest s.publicValue v.semantic s.hash s.observer)
   match r with
   | .Err _ => pure (.inl (.Err verifier.Error.Semantic,s.scratch))
   | .Ok sem => pure (.inr (.mark s v sem))) := rfl
#print axioms occurrence5
end AspisR1.NMP_PrepareSteps
