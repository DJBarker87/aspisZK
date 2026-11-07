import NMS_SafePackets
import NMS_RSL242Fold
set_option autoImplicit false
namespace NMS_Safe242Fold
open RSL NMS_RSLRefine NMS_SafePackets
/-- Source-relational fold with the explicitly recorded NHJ clone-domain
caller clause. All observable conclusion clauses are exactly canonical RSL.
This is NOT an assertion of the stronger, True-domain canonical packet. -/
theorem fold (L : PoolLib) (D : DeployedIds)
 (authenticate : TX2_233.Args → Env → Obs (Except ProgramError Authenticated))
 (packet : RowSpec233 L D authenticate) (a : TX2_242.Args) (safe : Safe a.accounts) :
 Refines (NMS_RSL242Fold.replay L D authenticate a) (TX2_242.Ref L D a) := by
 unfold NMS_RSL242Fold.replay TX2_242.Ref
 apply rsseq (refl _)
 apply rsbind (refl _)
 intro q
 apply rsseq (refl _)
 apply rsbind (refl _)
 intro lane
 apply rsbind (refl _)
 intro slot
 apply rsbind
 · intro env o run
   exact ⟨trivial,by rw [run]; exact packet _ env safe⟩
 · intro auth
   exact refl _
#print axioms fold
end NMS_Safe242Fold
