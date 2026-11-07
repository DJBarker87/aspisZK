import NMT_R2_345Frames
set_option autoImplicit false
namespace NMT_R2_345
open RSL NMT_345Observation NMT_R2_Observation

def checkpointObservation (keep : Bool) (a : OwnedAccount) (program : B32) (writable : Bool) :
 Obs (Except ProgramError Unit) :=
 if decide (a.owner ≠ program) || a.is_signer || a.executable || a.is_writable != writable then
  silent (.error .invalidAccountData)
 else tryObs (cloned keep a.length) fun n => check (n != CHECKPOINT_BYTES) .invalidAccountData

theorem checkpointObservation_valid (keep : Bool) (a : OwnedAccount) (program : B32)
 (writable : Bool) (env : Env) :
 NMT_R2.verifierCheckpoint a program writable env (checkpointObservation keep a program writable) := by
 unfold NMT_R2.verifierCheckpoint checkpointObservation
 split
 · rfl
 · exact try_valid _ _ _ _ env (cloned_valid keep a.length env)
    (fun n => check_valid _ _ env)

def stepCheckpoint (allocation : Allocation) (s : Parent)
 (next : Parent → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (checkpointObservation (allocation 0) s.checkpointAccount s.original.program_id true) (fun _ => next s)

theorem stepCheckpoint_valid (allocation : Allocation) (s : Parent)
 (next : Parent → Obs (Except ProgramError Bytes)) (suffix : RS Bytes) (env : Env)
 (later : suffix env (next s)) :
 RS.seq (NMT_R2.verifierCheckpoint s.checkpointAccount s.original.program_id true) suffix
  env (stepCheckpoint allocation s next) := by
 apply try_valid _ _ _ _ env (checkpointObservation_valid _ _ _ _ env)
 intro _
 exact later
#print axioms checkpointObservation_valid
#print axioms stepCheckpoint_valid
end NMT_R2_345
