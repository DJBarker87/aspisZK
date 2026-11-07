import NMT_R2_345Frames
set_option autoImplicit false
namespace NMT_R2_345
open RSL NMT_345Observation NMT_R2_Observation

def stepCheckpointData (allocation : Allocation) (s : Parent) (next : CheckpointData → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (cloned (allocation 1) s.checkpointAccount.bytes) (fun bytes => next ⟨s,bytes⟩)

theorem stepCheckpointData_valid (allocation : Allocation) (s : Parent)
 (next : CheckpointData → Obs (Except ProgramError Bytes)) (suffix : Bytes → RS Bytes) (env : Env)
 (later : ∀ bytes, suffix bytes env (next ⟨s,bytes⟩)) :
 RS.bind (NMT_R2.data s.checkpointAccount) suffix env (stepCheckpointData allocation s next) := by
 exact try_valid _ _ _ _ env (cloned_valid _ _ env) later
#print axioms stepCheckpointData_valid
end NMT_R2_345
