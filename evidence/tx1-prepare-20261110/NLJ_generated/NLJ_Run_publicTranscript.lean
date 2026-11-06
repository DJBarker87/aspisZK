import NLJ_Continuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
theorem run_publicTranscript {H : Type} (i : Input H) (p : r1_wire.Prefix) :
 run (PreparedHashCode.bind (step {input:=i,locals:=.publicTranscript p}) continuation) =
 run (denote {input:=i,locals:=.publicTranscript p}) := by
 change run (PreparedHashCode.bind (PreparedHashCode.bind (S1SemanticCode.publicTranscript i.digest i.publicValue i.hash p.c1_root) _) continuation) =
  run (PreparedHashCode.bind (S1SemanticCode.publicTranscript i.digest i.publicValue i.hash p.c1_root) _)
 rw [NLJ_Monad.bind_assoc]
 apply NLJ_RunAlgebra.bind_congr
 intro reply
 cases reply <;> rfl
#print axioms run_publicTranscript
end AspisR1.NLJ_Observed
end
