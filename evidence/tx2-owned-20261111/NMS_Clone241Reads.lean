import NMS_Clone241Public
set_option autoImplicit false
namespace NMS_Clone241Reads
open RSL RSL.TX2_241 NMS_RSLRefine NMS_RSLStepFacts NMS_Clone241Replay

theorem fold (L : PoolLib) (V : V2Lib) (verify : VerifyNative V)
 (packet : VerifyPacket V verify) (a : Args) (domain : Domain V a)
 (validated : TX2_242.Validated L) (acc0 acc6 : OwnedAccount)
 (proofData checkpointData : Bytes)
 (count : a.accounts.length = 7)
 (index0 : a.accounts[0]? = some acc0) (index6 : a.accounts[6]? = some acc6)
 (read0 : acc0.bytes = .ok proofData) (read6 : acc6.bytes = .ok checkpointData)
 (checkpointChecked : verifierCheckpoint acc6 a.program_id false = .ok ())
 (scanExtent : validated.proof_length = PROOF_BYTES) :
 Refines (afterReads L V (observed verify) validated proofData checkpointData)
  (afterReads L V (modelVerify V) validated proofData checkpointData) := by
 unfold afterReads
 apply rsseq (refl _)
 apply rsbind_using (refl _)
 intro env u events passed observation run
 cases u
 have guard := check_return _ _ env events passed
 have proofExtent : proofData.length = AFTERSTATE_BYTES + validated.proof_length := by simpa using guard
 have suffix : Refines
   (RS.bind (RS.lift (L.encodeStatement validated.statement)) fun encoded =>
    RS.bind (RS.ofOption encoded .invalidInstructionData) fun publicBytes =>
    afterPublic L V (observed verify) validated proofData checkpointData publicBytes)
   (RS.bind (RS.lift (L.encodeStatement validated.statement)) fun encoded =>
    RS.bind (RS.ofOption encoded .invalidInstructionData) fun publicBytes =>
    afterPublic L V (modelVerify V) validated proofData checkpointData publicBytes) := by
   apply rsbind (refl _)
   intro encoded
   apply rsbind (refl _)
   intro publicBytes
   exact NMS_Clone241Public.fold L V verify packet a domain validated acc0 acc6
    proofData checkpointData publicBytes count index0 index6 read0 read6 checkpointChecked scanExtent proofExtent
 exact suffix env observation run
#print axioms fold
end NMS_Clone241Reads
