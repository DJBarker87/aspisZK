import NMT_R2_345Frames
set_option autoImplicit false
namespace NMT_R2_345
open RSL NMT_345Observation NMT_R2_Observation

def stepDistinct (s : Parent) (next : Parent → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (silent (requireDistinct [s.proofAccount,s.publicAccount,s.checkpointAccount])) (fun _ => next s)

theorem stepDistinct_valid (s : Parent) (next : Parent → Obs (Except ProgramError Bytes))
 (suffix : RS Bytes) (env : Env) (later : suffix env (next s)) :
 RS.seq (RS.ofExcept (requireDistinct [s.proofAccount,s.publicAccount,s.checkpointAccount])) suffix env (stepDistinct s next) := by
 apply try_valid _ _ _ _ env rfl
 intro _
 exact later
#print axioms stepDistinct_valid
end NMT_R2_345
