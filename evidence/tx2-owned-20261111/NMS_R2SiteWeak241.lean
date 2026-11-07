import NMS_R2SiteFold241
set_option autoImplicit false
noncomputable section
namespace NMS_R2SiteWeak241
open RSL RSL.TX2_241 NMS_R2Replay241
open NMS_R2Tail242 (Request Candidate Statement)
/-- G1b at the weak library, with scanner width discharged internally from
its fixed source law. Only the original D1 snapshot consistency is needed. -/
theorem fold (L : PoolLib) (request : Request → L.Request)
 (candidate : Candidate → L.Afterstate) (statement : Statement → L.Statement)
 (D : DeployedIds) (V : V2Lib)
 (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
 (validate : TX2_242.Args → Env → Obs (Except ProgramError
  (TX2_242.Validated (NMS_R2PoolSites.install L request candidate statement))))
 (child242 : TX2_242.RowSpec_242 (NMS_R2PoolSites.install L request candidate statement) D validate)
 (verify : VerifyNative {V with Root0 := fun _ _ => True,tx2auth := w})
 (child064 : VerifyPacket {V with Root0 := fun _ _ => True,tx2auth := w} verify)
 (a : Args) (consistent : ∀ x ∈ a.accounts, Consistent x) :
 NMS_R2Refine.Refines
  (replay (NMS_R2PoolSites.install L request candidate statement)
   {V with Root0 := fun _ _ => True,tx2auth := w} validate verify a)
  (TX2_241.Ref (NMS_R2PoolSites.install L request candidate statement) D
   {V with Root0 := fun _ _ => True,tx2auth := w} a) :=
 NMS_R2SiteFold241.fold L request candidate statement D _ validate child242 verify child064 a
  ⟨consistent,fun _ _ _ _ _ _ _ _ _ _ => trivial⟩
#print axioms fold
end NMS_R2SiteWeak241
