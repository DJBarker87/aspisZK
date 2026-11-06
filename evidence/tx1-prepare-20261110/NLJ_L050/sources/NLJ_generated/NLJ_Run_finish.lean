import NLJ_Continuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
theorem run_finish {H : Type} (i : Input H) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (c : r1_wire.Challenges) :
 run (PreparedHashCode.bind (step {input:=i,locals:=.finish p t c}) continuation) =
 run (denote {input:=i,locals:=.finish p t c}) := by
 change run (PreparedHashCode.bind (PreparedHashCode.bind
  (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation)
   i.digest i.publicValue p t c none)
  (fun (r : Out H) => Code.done (Sum.inl r : Post H))) continuation) = _
 apply NLJ_RunAlgebra.inl_return
 intro r
 rfl
#print axioms run_finish
end AspisR1.NLJ_Observed
end
