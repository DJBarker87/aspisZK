import NLJ_Control137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Control137
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
theorem begin_step (native136 : NLC_Finish.Input Unit → NLI_Interface.Observation Unit)
 (i : NLJ_Observed.Input Unit) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript Unit) :
 step native136 ⟨i,.begin p t⟩ = run (NLJ_Observed.step ⟨i,.begin p t⟩) := by
 change run (PreparedHashCode.bind (NHG_BeginPackets.begin S1SemanticCode.semanticValidated i.digest p t) _) =
  run (PreparedHashCode.bind (S1SemanticCode.begin i.digest p t) _)
 rw [NHG_Begin.source]
 try rfl
#print axioms begin_step
end AspisR1.NLJ_Control137
end
