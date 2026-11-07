import NMX_R2_RSL233Replay
set_option autoImplicit false
namespace NMX_R2_RSL233Fold
open RSL NMX_R2_Refine
/-- The complete canonical control tree, including both malformed-count Err
variants. Observed children enter only at their original reached arguments. -/
def replay (L : PoolLib) (D : DeployedIds)
 (laneNative : Bytes → Env → Obs (Except ProgramError LaneState))
 (registryNative : TX2_234.Args → Env → Obs (Except ProgramError Unit))
 (a : TX2_233.Args) : RS Authenticated :=
 match a.accounts with
 | [p,m,c,l,r,e,v] =>
   NMX_R2_RSL233Replay.replayBody L D laneNative registryNative a p m c l r e v
 | _ => RS.throw (if a.accounts.length < 7 then .notEnoughAccountKeys else .invalidArgument)

/-- Canonical full-observation SOURCE fold. It covers every Result and stop
prefix but does not yet claim an emitted/native interpretation or row root. -/
theorem fold (L : PoolLib) (D : DeployedIds)
 (laneNative : Bytes → Env → Obs (Except ProgramError LaneState))
 (registryNative : TX2_234.Args → Env → Obs (Except ProgramError Unit))
 (lanePacket : TX2_217.RowSpec_217 laneNative)
 (registryPacket : TX2_234.RowSpec_234 L D registryNative)
 (a : TX2_233.Args) :
 Refines (replay L D laneNative registryNative a) (TX2_233.Ref L D a) := by
 unfold replay TX2_233.Ref
 generalize a.accounts = accounts
 cases accounts with
 | nil => exact refl _
 | cons p rest1 =>
   cases rest1 with
   | nil => exact refl _
   | cons m rest2 =>
     cases rest2 with
     | nil => exact refl _
     | cons c rest3 =>
       cases rest3 with
       | nil => exact refl _
       | cons l rest4 =>
         cases rest4 with
         | nil => exact refl _
         | cons r rest5 =>
           cases rest5 with
           | nil => exact refl _
           | cons e rest6 =>
             cases rest6 with
             | nil => exact refl _
             | cons v rest7 =>
               cases rest7 with
               | nil => exact NMX_R2_RSL233Replay.body_fold L D laneNative registryNative lanePacket registryPacket a p m c l r e v
               | cons extra remaining => exact refl _
#print axioms fold
end NMX_R2_RSL233Fold
