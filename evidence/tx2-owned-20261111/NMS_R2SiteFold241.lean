import NMS_R2PoolSites
import NMS_R2Fold241
set_option autoImplicit false
noncomputable section
namespace NMS_R2SiteFold241
open RSL RSL.TX2_241 NMS_R2Replay241
open NMS_R2Tail242 (Request Candidate Statement)
/-- The source fold with the CLOSED scanner/reconstruction models fixed.
The scanner width is proved from its SAME native observation, not an
own-input clause or an independently successful scanner reply. -/
theorem fold (L : PoolLib) (request : Request → L.Request)
 (candidate : Candidate → L.Afterstate) (statement : Statement → L.Statement)
 (D : DeployedIds) (V : V2Lib)
 (validate : TX2_242.Args → Env → Obs (Except ProgramError
   (TX2_242.Validated (NMS_R2PoolSites.install L request candidate statement))))
 (child242 : TX2_242.RowSpec_242 (NMS_R2PoolSites.install L request candidate statement) D validate)
 (verify : VerifyNative V) (child064 : VerifyPacket V verify)
 (a : Args) (domain : Domain V a) :
 NMS_R2Refine.Refines
  (replay (NMS_R2PoolSites.install L request candidate statement) V validate verify a)
  (TX2_241.Ref (NMS_R2PoolSites.install L request candidate statement) D V a) :=
 NMS_R2Fold241.fold _ D V validate child242
  (NMS_R2PoolSites.scanner_extent L request candidate statement) verify child064 a domain
#print axioms fold
end NMS_R2SiteFold241
