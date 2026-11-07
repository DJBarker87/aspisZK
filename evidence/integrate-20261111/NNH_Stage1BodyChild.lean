import NNH_Tx1CallCut
set_option autoImplicit false
noncomputable section
namespace NNH_Stage1BodyChild
open RSL NNH_Libraries

def args (a : TX1_345.Args) (p pub ck : OwnedAccount) (saved : Bytes) (env : Env)
 (packet : NNH_Stage1Cut.Packet a p pub ck saved env) : TX1_094.Args VL :=
 ⟨C.semanticPublic packet.statement,packet.public_data,
  slice packet.proof_data AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES,(a.data.getD 1 0).toNat⟩

theorem produce (a : TX1_345.Args) (p pub ck : OwnedAccount) (saved : Bytes) (env : Env)
 (packet : NNH_Stage1Cut.Packet a p pub ck saved env) :
 Nonempty (NNH_Tx1CallCut.Packet (args a p pub ck saved env packet) saved env) := by
 apply NNH_Tx1CallCut.produce
 exact NNH_ExceptOk.unmap VL _ saved packet.child

#print axioms produce
end NNH_Stage1BodyChild
