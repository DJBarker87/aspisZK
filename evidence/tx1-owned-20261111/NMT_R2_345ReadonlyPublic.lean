import NMT_R2_345Frames
set_option autoImplicit false
namespace NMT_R2_345
open RSL NMT_345Observation NMT_R2_Observation

def stepReadonlyPublic (s : Parent) (next : Parent → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (silent (readonlyBuffer s.publicAccount)) (fun _ => next s)

theorem stepReadonlyPublic_valid (s : Parent) (next : Parent → Obs (Except ProgramError Bytes))
 (suffix : RS Bytes) (env : Env) (later : suffix env (next s)) :
 RS.seq (RS.ofExcept (readonlyBuffer s.publicAccount)) suffix env (stepReadonlyPublic s next) := by
 apply try_valid _ _ _ _ env rfl
 intro _
 exact later
#print axioms stepReadonlyPublic_valid
end NMT_R2_345
