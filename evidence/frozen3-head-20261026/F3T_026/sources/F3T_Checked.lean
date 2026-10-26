import F3T_CanonicalChecks
import F3T_Causal
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Checked
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.AdaptiveFirstReadLaw
open F3T_Experiment F3T_Canon F3T_Charged F3T_Admission

 theorem original_clean (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (Q : Nat) (clean : ¬ RecordedBinaryExperimentBin.binaryCollision Q
      (eval H (projected D P))) :
    ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable (eval H (original D P)).1 := by
  intro bad
  apply clean
  change hitsBad _ emptyTable (eval H (projected D P)).1
  rw [projected_eval]
  change hitsBad _ emptyTable (eval H (recorded D (build D) P)).1
  rw [recorded_eval]
  exact TraceAppend.hitsBad_of_prefix _ _ _ _ bad

 theorem checks (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State,(eval H P).1.length≤Q) (H : Bytes → State)
    (clean : ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
      (eval H (projected D (canon P))))
    (accepted : (eval H (original D (canon P))).2.2=true) :
    LiteralAcceptanceTerminal.Checks (output D (canon P) H).semantic.value
      (rows D (canon P) H) := by
  exact Classical.choice (F3T_CanonicalChecks.accepted_checks D P H Q hq accepted
    (original_clean D (canon P) H (Q+1161) clean))

#print axioms original_clean
#print axioms checks
end AspisR1.F3T_Checked
end
