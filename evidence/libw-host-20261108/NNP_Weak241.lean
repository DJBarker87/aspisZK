import LIBW_WeakPerEnv
import NMS_R2Weak241
set_option autoImplicit false
noncomputable section
namespace NNP_Weak241
open RSL RSL.TX2_241 NMS_R2Replay241

theorem fold_env {Ambient : Type} (world : NLM_PacketTypes.World Ambient)
 (L : PoolLib) (D : DeployedIds)
 (validate : TX2_242.Args → Env → Obs (Except ProgramError (TX2_242.Validated L)))
 (child242 : TX2_242.RowSpec_242 L D validate)
 (scan : NMS_R2Facts242.ScannerExtent L)
 (verify : VerifyNative (LIBW_WeakPerEnv.weakEnv world))
 (child064 : VerifyPacket (LIBW_WeakPerEnv.weakEnv world) verify)
 (a : Args) (consistent : ∀ x ∈ a.accounts, Consistent x) :
 NMS_R2Refine.Refines
  (replay L (LIBW_WeakPerEnv.weakEnv world) validate verify a)
  (TX2_241.Ref L D (LIBW_WeakPerEnv.weakEnv world) a) :=
 NMS_R2Weak241.fold L D LIBB_V2Star.library (LIBW_WeakPerEnv.wEnv world)
  validate child242 scan verify child064 a consistent

theorem fold_any (Ambient : Type) (L : PoolLib) (D : DeployedIds)
 (validate : TX2_242.Args → Env → Obs (Except ProgramError (TX2_242.Validated L)))
 (child242 : TX2_242.RowSpec_242 L D validate)
 (scan : NMS_R2Facts242.ScannerExtent L)
 (verify : VerifyNative (LIBW_WeakPerEnv.weakAny Ambient))
 (child064 : VerifyPacket (LIBW_WeakPerEnv.weakAny Ambient) verify)
 (a : Args) (consistent : ∀ x ∈ a.accounts, Consistent x) :
 NMS_R2Refine.Refines
  (replay L (LIBW_WeakPerEnv.weakAny Ambient) validate verify a)
  (TX2_241.Ref L D (LIBW_WeakPerEnv.weakAny Ambient) a) :=
 NMS_R2Weak241.fold L D LIBB_V2Star.library (LIBW_WeakPerEnv.wAny Ambient)
  validate child242 scan verify child064 a consistent

#print axioms fold_env
#print axioms fold_any
end NNP_Weak241
