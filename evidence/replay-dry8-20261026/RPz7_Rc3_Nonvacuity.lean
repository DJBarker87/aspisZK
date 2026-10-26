import RPz7_SAP_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc3_Nonvacuity
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw
open MultiproofConeCanonical

def Facts (driver : OraclePortStoredExperimentC4.Input → Program Bytes State Bool)
    (H : Bytes → State) (pub proof pub2 proof2 checkpoint : Slice U8) (written : Bytes) : Prop :=
  S2X.CheckpointVersionBinding written (bytesOf checkpoint.val) →
  S2W_AuthenticatedInputs.P2Prime H proof pub proof2 pub2 →
  ∃ i : OraclePortStoredExperimentC4.Input,
    i.statement.pubBytes = bytesOf pub.val ∧ i.stored = bytesOf proof.val ∧
    i.statement.tag = 2 ∧ i.statement.pubBytes.length = 1880 ∧
    (eval H (driver i)).2 = true ∧ ¬ ∀ j, (eval H (driver j)).2 = false

theorem derive (driver : OraclePortStoredExperimentC4.Input → Program Bytes State Bool)
    (H : Bytes → State) (pub proof pub2 proof2 checkpoint : Slice U8) (written : Bytes)
    (accepted : T2R_Acceptance.Facts driver H pub proof pub2 proof2 checkpoint written) :
    Facts driver H pub proof pub2 proof2 checkpoint written :=
  SAP_Nonvacuity.accepted_input driver H pub proof pub2 proof2 checkpoint written accepted

#print axioms derive
end AspisR1.Rc3_Nonvacuity
end
