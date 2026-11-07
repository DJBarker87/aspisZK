import NMX_RSL233Replay
set_option autoImplicit false
namespace NMX_RSL233Fold
open RSL NMS_RSLRefine
/-- The complete canonical control tree, including both malformed-count Err
variants. Observed children enter only at their original reached arguments. -/
def replay (L : PoolLib) (D : DeployedIds)
 (laneNative : Bytes → Env → Obs (Except ProgramError LaneState))
 (registryNative : TX2_234.Args → Env → Obs (Except ProgramError Unit))
 (a : TX2_233.Args) : RS Authenticated :=
 match a.accounts with
 | [p,m,c,l,r,e,v] =>
   NMX_RSL233Replay.replayBody L D laneNative registryNative a p m c l r e v
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
 split <;> first
 | exact NMX_RSL233Replay.body_fold L D laneNative registryNative lanePacket registryPacket _ _ _ _ _ _ _ _
 | exact refl _
#print axioms fold
end NMX_RSL233Fold
