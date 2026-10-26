import F3V_DigestCompatibility
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_CheckpointOracle
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem oracle {F C : Type} (c : DrvC_Installation.Configuration F C) (H : Bytes → State) :
    CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest (F3V_RunEvidence.D2 c H)) () H := by
  intro parts digest returned
  change F3U_Oracle.hashv H parts=ok digest at returned
  have eq := Result.ok.inj returned
  rw [←eq]
  exact F3U_Oracle.decoded H parts

#print axioms oracle
end AspisR1.F3V_CheckpointOracle
end
