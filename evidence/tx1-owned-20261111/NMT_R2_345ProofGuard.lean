import NMT_R2_345Frames
set_option autoImplicit false
namespace NMT_R2_345
open RSL NMT_345Observation NMT_R2_Observation

def proofBad (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) (s : ProofData V C) : Bool :=
 s.proofData.length != PROOF_ACCOUNT_BYTES ||
 s.proofData.take AFTERSTATE_BYTES != s.candidate ||
 s.proofData.getD (AFTERSTATE_BYTES + 8) 0 != NMT_R2.TX1_345.S2_TAG

def stepProofGuard (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) (s : ProofData V C)
 (next : ProofData V C → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (check (proofBad V C s) .invalidAccountData) (fun _ => next s)

theorem stepProofGuard_valid (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) (s : ProofData V C)
 (next : ProofData V C → Obs (Except ProgramError Bytes)) (suffix : RS Bytes) (env : Env)
 (later : suffix env (next s)) :
 RS.seq (RS.check (proofBad V C s) .invalidAccountData) suffix env
  (stepProofGuard V C s next) := by
 exact try_valid _ _ _ _ env (check_valid _ _ env) (fun _ => later)
#print axioms stepProofGuard_valid
end NMT_R2_345
