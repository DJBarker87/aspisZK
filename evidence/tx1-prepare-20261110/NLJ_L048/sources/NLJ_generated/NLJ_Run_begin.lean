import NLJ_Continuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
theorem run_begin {H : Type} (i : Input H) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) :
 run (PreparedHashCode.bind (step {input:=i,locals:=.begin p t}) continuation) =
 run (denote {input:=i,locals:=.begin p t}) := by
 change run (PreparedHashCode.bind (PreparedHashCode.bind (S1SemanticCode.begin i.digest p t) _) continuation) =
  run (PreparedHashCode.bind (S1SemanticCode.begin i.digest p t) _)
 rw [NLJ_Monad.bind_assoc]
 apply NLJ_RunAlgebra.bind_congr
 intro reply
 rcases reply with ⟨reply,after⟩
 cases reply <;> rfl
#print axioms run_begin
end AspisR1.NLJ_Observed
end
