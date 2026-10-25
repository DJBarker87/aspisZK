import AuS1_Map
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Stability
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft

/-- Later batch, query, writer and reader calls cannot change the original
commitment-prefix map. Duplicate addresses are kept in the ordered suffix. -/
 theorem after_commitment (trace suffix : List (Bytes × State)) (frame : Bytes)
    (read : Read trace frame) (parsed : Parsed) (kind : Nat) :
    OraclePortAllSelectedRecoveryC6.recovered (trace ++ suffix) frame parsed kind =
      OraclePortAllSelectedRecoveryC6.recovered trace frame parsed kind := by
  funext index
  unfold OraclePortAllSelectedRecoveryC6.recovered
  rw [SdkC_Replay.cut_append trace suffix frame read]

#print axioms after_commitment
end AspisR1.AuS1_Stability
end
