import NNV_DecodeP1880
import NNV_PreparedFront
import NNV_FinishTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_A1CanonicalCuts
open RSL NNH_Libraries NNH_Run5bCtx

theorem returned {W Tx : Type} (c : Ctx W Tx) (a : TX1_345.Args) (saved : Bytes)
 (called : NNH_ReturnsBundle.tx1Value a (envOf c) = .ok saved) :
 ∃ p pub ck, a.accounts=[p,pub,ck] ∧
 ∃ outer : NNH_Stage1Cut.Packet a p pub ck saved (envOf c),
 outer.public_data.length = TX1_094.P1880_LEN ∧
 TX1_094.Domain VL (NNH_Stage1BodyChild.args a p pub ck saved (envOf c) outer) none (C.semanticPublic outer.statement) ∧
 TX1_087.Domain VL ⟨C.semanticPublic outer.statement,slice outer.proof_data AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES,VL.zeroE29⟩ none ∧
 ∃ body : NNH_Tx1CallCut.Packet (NNH_Stage1BodyChild.args a p pub ck saved (envOf c) outer) saved (envOf c),
 ∃ sem v, Nonempty (NNV_PrepareFrontCut.Packet
  ⟨C.semanticPublic outer.statement,slice outer.proof_data AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES,VL.zeroE29⟩ (envOf c) sem v) ∧
 LIB_Prepared.value (sem,v,VL.zeroE29) (envOf c) = (.ok body.prepared.1,body.prepared.2) := by
 obtain ⟨p,pub,ck,shape,outer,width,d094,d087⟩ := NNV_DecodeP1880.returned c a saved called
 obtain ⟨body⟩ := NNH_Stage1BodyChild.produce a p pub ck saved (envOf c) outer
 obtain ⟨sem,v,front,prepared⟩ := NNV_PreparedFront.returned _ (envOf c) body.prepared.1 body.prepared.2 body.prepare
 exact ⟨p,pub,ck,shape,outer,width,d094,d087,body,sem,v,front,prepared⟩
#print axioms returned
end AspisR1.NNV_A1CanonicalCuts
end
