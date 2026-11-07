import NMT_R2_345Frames
set_option autoImplicit false
namespace NMT_R2_345
open RSL NMT_345Observation NMT_R2_Observation

def stepZero (s : CheckpointData) (next : CheckpointData → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (silent (requireZero s.checkpointData)) (fun _ => next s)

theorem stepZero_valid (s : CheckpointData) (next : CheckpointData → Obs (Except ProgramError Bytes))
 (suffix : RS Bytes) (env : Env) (later : suffix env (next s)) :
 RS.seq (RS.ofExcept (requireZero s.checkpointData)) suffix env (stepZero s next) := by
 apply try_valid _ _ _ _ env rfl
 intro _
 exact later
#print axioms stepZero_valid
end NMT_R2_345
