import NNH_Run5bHost
import NNH_Stage1TopCut
import NNH_Stage1PrepareDomainR4
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bA1Domain
open Aeneas Aeneas.Std Result RSL NNH_Libraries NNH_Run5bCtx

theorem returned {W Tx : Type} (c : Ctx W Tx) (a : TX1_345.Args) (saved : Bytes)
 (called : NNH_ReturnsBundle.tx1Value a (envOf c) = .ok saved) :
 ∃ (p pub ck : OwnedAccount), a.accounts = [p,pub,ck] ∧
 ∃ packet : NNH_Stage1Cut.Packet a p pub ck saved (envOf c),
 TX1_094.Domain VL (NNH_Stage1BodyChild.args a p pub ck saved (envOf c) packet) none
  (C.semanticPublic packet.statement) ∧
 TX1_087.Domain VL ⟨C.semanticPublic packet.statement,
  slice packet.proof_data AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES,VL.zeroE29⟩ none ∧
 packet.public_data.length=1880 := by
 obtain ⟨p,pub,ck,shape,_,⟨packet⟩⟩ := NNH_Stage1TopCut.produce a saved (envOf c) called
 exact ⟨p,pub,ck,shape,packet,
  NNH_Stage1PrepareDomainR4.caller a p pub ck saved (envOf c) packet,
  NNH_Stage1PrepareDomainR4.prepare a p pub ck saved (envOf c) packet,
  NNH_S1DecodeExtent.source packet.public_data packet.statement packet.decode⟩
#print axioms returned
end AspisR1.NNH_Run5bA1Domain
end
