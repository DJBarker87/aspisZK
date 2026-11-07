import NMT_R2_345Frames
set_option autoImplicit false
namespace NMT_R2_345
open RSL NMT_345Observation NMT_R2_Observation

def stepProofData (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) (allocation : Allocation)
 (s : Candidate V C) (next : ProofData V C → Obs (Except ProgramError Bytes)) : Obs (Except ProgramError Bytes) :=
 tryObs (cloned (allocation 5) s.proofAccount.bytes) (fun bytes => next ⟨s,bytes⟩)

theorem stepProofData_valid (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) (allocation : Allocation)
 (s : Candidate V C) (next : ProofData V C → Obs (Except ProgramError Bytes))
 (suffix : Bytes → RS Bytes) (env : Env)
 (later : ∀ bytes, suffix bytes env (next ⟨s,bytes⟩)) :
 RS.bind (NMT_R2.data s.proofAccount) suffix env (stepProofData V C allocation s next) := by
 exact try_valid _ _ _ _ env (cloned_valid _ _ env) later
#print axioms stepProofData_valid
end NMT_R2_345
