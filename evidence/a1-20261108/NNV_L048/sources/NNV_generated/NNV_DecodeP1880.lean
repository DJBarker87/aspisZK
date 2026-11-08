import NNH_Run5bA1Domain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_DecodeP1880
open Aeneas Aeneas.Std Result NNH_Libraries RSL
/-- Decoder liveness is not assumed. Any returned SAME statement forces the
native input length required by checkpoint and 094's caller clause. -/
theorem native (publicData : Slice U8) (st : C.Statement)
 (decoded : C.decodeStatement (LIB_Carriers.bytes publicData) = some st) :
 publicData.val.length = TX1_094.P1880_LEN := by
 have h := NNH_S1DecodeExtent.source _ st decoded
 simpa only [LIB_Carriers.bytes,NMS_R2N_RSLScalars.bytes,List.length_map,TX1_094.P1880_LEN] using h

/-- The 345 packet, 094 domain and 087 domain are all indexed by this decoder
witness, including R4. No independent public statement is selected. -/
theorem returned {W Tx : Type} (c : NNH_Run5bCtx.Ctx W Tx) (a : TX1_345.Args) (saved : Bytes)
 (called : NNH_ReturnsBundle.tx1Value a (NNH_Run5bCtx.envOf c) = .ok saved) :
 ∃ p pub ck, a.accounts = [p,pub,ck] ∧
 ∃ packet : NNH_Stage1Cut.Packet a p pub ck saved (NNH_Run5bCtx.envOf c),
 packet.public_data.length = TX1_094.P1880_LEN ∧
 TX1_094.Domain VL (NNH_Stage1BodyChild.args a p pub ck saved (NNH_Run5bCtx.envOf c) packet)
  none (C.semanticPublic packet.statement) ∧
 TX1_087.Domain VL ⟨C.semanticPublic packet.statement,
  slice packet.proof_data AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES,VL.zeroE29⟩ none := by
 obtain ⟨p,pub,ck,shape,packet,d094,d087,width⟩ := NNH_Run5bA1Domain.returned c a saved called
 exact ⟨p,pub,ck,shape,packet,width,d094,d087⟩
#print axioms native
#print axioms returned
end AspisR1.NNV_DecodeP1880
end
