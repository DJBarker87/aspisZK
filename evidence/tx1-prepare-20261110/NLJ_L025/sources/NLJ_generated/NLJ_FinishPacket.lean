import NLJ_Child136
import NLJ_ObservedFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run)
def finishInput {H : Type} (i : Input H) (p : r1_wire.Prefix)
 (t : r1_wire.SemanticTranscript H) (c : r1_wire.Challenges) : NLC_Finish.Input H :=
 ⟨i.reservation,i.digest,i.publicValue,p,t,c⟩
def returnedReply {H : Type} : Result (Out H) → Result (Post H)
 | .ok r => .ok (.inl r) | .fail e => .fail e | .div => .div
/-- (bd) intermediate ONLY: install the OPEN136 packet at the SAME original
public/digest and the exact carried parsed Prefix/transcript/challenges. -/
theorem finish_packet {H : Type}
 (native : NLC_Finish.Input H → NLI_Interface.Observation H)
 (child136 : NLI_Interface.RowSpec_136 native)
 (i : Input H) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (c : r1_wire.Challenges) :
 let call := finishInput i p t c
 (native call).afterInput = call ∧
 run (step {input:=i,locals:=.finish p t c}) =
  ((native call).log,returnedReply (native call).reply) := by
 let call := finishInput i p t c
 obtain ⟨frame,_,reply⟩ := child136 call
 refine ⟨frame,?_⟩
 change run (PreparedHashCode.bind
  (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation)
   i.digest i.publicValue p t c none) (fun (r : Out H) => PreparedHashCode.Code.done (Sum.inl r : Post H))) = _
 rw [AuS1_Trace.run_bind]
 change run (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation)
   i.digest i.publicValue p t c none) = _ at reply
 rw [reply]
 cases h : (native call).reply <;> simp only [AuS1_Trace.continueRun,returnedReply,List.append_nil]
 all_goals rfl
#print axioms finish_packet
#print finish_packet
end AspisR1.NLJ_Observed
end
