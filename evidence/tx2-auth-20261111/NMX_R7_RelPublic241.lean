import NMX_R7_RelVerify241
set_option autoImplicit false
namespace NMX_R7_RelPublic241
open NMX_R7_RelVerify241
open RSL RSL.TX2_241 NMS_R2Refine NMS_R2StepFacts NMS_R2Replay241
/-- The actual 064 observation can replace the model at this exact public,
proof-range and checkpoint triple, for every library whose law it refines.
All entered-path facts stay inside this suffix lemma. -/
theorem fold (L : PoolLib) (V : V2Lib) (verify : VerifyRelation V)
 (packet : RelPacket V verify) (a : Args) (domain : Domain V a)
 (validated : TX2_242.Validated L) (acc0 acc6 : OwnedAccount)
 (proofData checkpointData publicBytes : Bytes)
 (count : a.accounts.length = 7)
 (index0 : a.accounts[0]? = some acc0) (index6 : a.accounts[6]? = some acc6)
 (read0 : acc0.bytes = .ok proofData) (read6 : acc6.bytes = .ok checkpointData)
 (checkpointChecked : acc6.length = .ok CHECKPOINT_BYTES)
 (scanExtent : validated.proof_length = PROOF_BYTES)
 (proofExtent : proofData.length = AFTERSTATE_BYTES + validated.proof_length) :
 Refines (afterPublic L V verify validated proofData checkpointData publicBytes)
  (afterPublic L V (modelVerify V) validated proofData checkpointData publicBytes) := by
 unfold afterPublic
 apply rsbind_using (refl _)
 intro env u events passed observation run
 cases u
 have guard := check_return _ _ env events passed
 have publicExtent : publicBytes.length = STATEMENT_BYTES := by simpa using guard
 have dom := NMS_R2Domains.entered V a domain acc0 acc6 proofData checkpointData publicBytes
   count index0 index6 read0 read6 checkpointChecked validated.proof_length scanExtent proofExtent publicExtent
 exact (rsbind (lift (NMX_R7_RelVerify241.call V verify packet _ dom)) (fun _ => refl _)) env observation run
#print axioms fold
end NMX_R7_RelPublic241
