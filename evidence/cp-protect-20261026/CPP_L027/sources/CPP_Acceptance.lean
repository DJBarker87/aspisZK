import T2R_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Acceptance
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical

def Facts (driver : OraclePortStoredExperimentC4.Input → Program Bytes State Bool)
    (H : Bytes → State) (pub proof pub2 proof2 checkpoint : Slice U8) (written : Bytes) : Prop :=
  ∃ i : OraclePortStoredExperimentC4.Input,
    i.statement.pubBytes = bytesOf pub.val ∧ i.stored = bytesOf proof.val ∧
    i.statement.tag = 2 ∧ i.statement.pubBytes.length = 1880 ∧
    75 + i.statement.pubBytes.length ≤ SelectedTranscriptParams.L ∧
    ∀ (p2prime : S2W_AuthenticatedInputs.P2Prime H proof pub proof2 pub2),
      (eval H (driver i)).2 = true ∧ ¬ (∀ j, (eval H (driver j)).2 = false)
end AspisR1.CPP_Acceptance
end
