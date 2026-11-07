import NNH_Stage1BodyChild
set_option autoImplicit false
noncomputable section
namespace NNH_Stage1ProofDomain
open RSL NNH_Libraries

theorem extent (a : TX1_345.Args) (p pub ck : OwnedAccount) (saved : Bytes) (env : Env)
 (packet : NNH_Stage1Cut.Packet a p pub ck saved env) :
 (slice packet.proof_data AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES).length=57607 := by
 have first := (Bool.or_eq_false_iff.mp (Bool.or_eq_false_iff.mp packet.proof_guard).1).1
 have length := bne_eq_false_iff_eq.mp first
 simp only [slice,List.length_take,List.length_drop]
 rw [length]
 rfl

#print axioms extent
end NNH_Stage1ProofDomain
