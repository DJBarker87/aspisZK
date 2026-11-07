import NNH_Stage1R4
import NNH_Stage1PublicDomain
set_option autoImplicit false
noncomputable section
namespace NNH_Stage1PrepareDomain
open RSL NNH_Libraries

theorem prepare (a : TX1_345.Args) (p pub ck : OwnedAccount) (saved : Bytes) (env : Env)
 (packet : NNH_Stage1Cut.Packet a p pub ck saved env) :
 TX1_087.Domain VL ⟨C.semanticPublic packet.statement,
  slice packet.proof_data AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES,VL.zeroE29⟩ none :=
 ⟨NNH_Stage1ProofDomain.extent a p pub ck saved env packet,rfl,
  (NNH_Stage1PublicDomain.produce a p pub ck saved env packet).1,
  NNH_Stage1R4.produce a p pub ck saved env packet⟩

theorem caller (a : TX1_345.Args) (p pub ck : OwnedAccount) (saved : Bytes) (env : Env)
 (packet : NNH_Stage1Cut.Packet a p pub ck saved env) :
 TX1_094.Domain VL (NNH_Stage1BodyChild.args a p pub ck saved env packet) none
  (C.semanticPublic packet.statement) :=
 ⟨rfl,(NNH_Stage1PublicDomain.produce a p pub ck saved env packet).1⟩
#print axioms prepare
#print axioms caller
end NNH_Stage1PrepareDomain
