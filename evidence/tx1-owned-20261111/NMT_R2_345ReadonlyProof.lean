import NMT_R2_345Frames
set_option autoImplicit false
namespace NMT_R2_345
open RSL NMT_345Observation NMT_R2_Observation

def stepReadonlyProof (s : Parent) (next : Parent → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (silent (readonlyBuffer s.proofAccount)) (fun _ => next s)

theorem stepReadonlyProof_valid (s : Parent) (next : Parent → Obs (Except ProgramError Bytes))
 (suffix : RS Bytes) (env : Env) (later : suffix env (next s)) :
 RS.seq (RS.ofExcept (readonlyBuffer s.proofAccount)) suffix env (stepReadonlyProof s next) := by
 apply try_valid _ _ _ _ env rfl
 intro _
 exact later
#print axioms stepReadonlyProof_valid
end NMT_R2_345
