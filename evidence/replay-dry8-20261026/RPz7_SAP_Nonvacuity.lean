import RPz7_T2R_Acceptance
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_Nonvacuity
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw
open MultiproofConeCanonical

theorem accepted_input
    (driver : OraclePortStoredExperimentC4.Input → Program Bytes State Bool)
    (H : Bytes → State) (pub proof pub2 proof2 checkpoint : Slice U8) (written : Bytes)
    (facts : T2R_Acceptance.Facts driver H pub proof pub2 proof2 checkpoint written)
    (history : S2X.CheckpointVersionBinding written (bytesOf checkpoint.val))
    (binding : S2W_AuthenticatedInputs.P2Prime H proof pub proof2 pub2) :
    ∃ i : OraclePortStoredExperimentC4.Input,
      i.statement.pubBytes=bytesOf pub.val ∧ i.stored=bytesOf proof.val ∧
      i.statement.tag=2 ∧ i.statement.pubBytes.length=1880 ∧
      (eval H (driver i)).2=true ∧ ¬ ∀ j,(eval H (driver j)).2=false := by
  obtain ⟨i,publicBytes,stored,tag,size,fit,accepted⟩ := facts
  exact ⟨i,publicBytes,stored,tag,size,accepted history binding⟩

#print axioms accepted_input
end AspisR1.SAP_Nonvacuity
end
