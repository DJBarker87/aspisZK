import NLJ_Control137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Control137
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
theorem public_step (native136 : NLC_Finish.Input Unit → NLI_Interface.Observation Unit)
 (i : NLJ_Observed.Input Unit) (p : r1_wire.Prefix) :
 step native136 ⟨i,.publicTranscript p⟩ = run (NLJ_Observed.step ⟨i,.publicTranscript p⟩) := by
 change run (PreparedHashCode.bind (NHG_PublicTranscript.packetCode i.digest i.publicValue i.hash p.c1_root) _) =
  run (PreparedHashCode.bind (S1SemanticCode.publicTranscript i.digest i.publicValue i.hash p.c1_root) _)
 rw [AuS1_Trace.run_bind,AuS1_Trace.run_bind,←NHG_PublicTranscript.code i.digest i.publicValue i.hash p.c1_root]
 try rfl
#print axioms public_step
end AspisR1.NLJ_Control137
end
