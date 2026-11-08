import NNH_S1DecodeExtent
import NNH_Stage1R4
import NNH_Stage1PublicDomain
set_option autoImplicit false
noncomputable section
namespace NNH_Stage1PrepareDomainR4
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
 ⟨rfl,(NNH_Stage1PublicDomain.produce a p pub ck saved env packet).1,
 NNH_S1DecodeExtent.source packet.public_data packet.statement packet.decode⟩
theorem decoder_discharge : TX1_345.P1880Discharge VL C := by
 intro bytes statement decoded
 exact NNH_S1DecodeExtent.source bytes statement decoded
#print axioms decoder_discharge
#print axioms prepare
#print axioms caller
end NNH_Stage1PrepareDomainR4
