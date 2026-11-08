import LIBW_WeakPerEnv
import NMV_NNCWeak
set_option autoImplicit false
noncomputable section
namespace NNP_G2
open RSL

theorem weak240_env {Ambient : Type} (world : NLM_PacketTypes.World Ambient)
 (L : PoolLib) (D : DeployedIds) (allocation : NMV_ConcreteWindows.Allocation)
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D (LIBW_WeakPerEnv.weakEnv world) child)
 (a : TX2_240.Args) (s : SdkState) (env : Env) :
 TX2_240.Ref L D (LIBW_WeakPerEnv.weakEnv world) a s env
  (NMV_ConcreteWindows.stage2 allocation child a s env) :=
 NMV_CandidateRoots.root240 L D _ allocation child packet a s env
  (TCK.domain240_weaken _ _ a s)

theorem frame_env {Ambient : Type} (world : NLM_PacketTypes.World Ambient)
 (L : PoolLib) (D : DeployedIds) (pl : NMV_NoWrite.PoolLaws L)
 (allocation : NMV_ConcreteWindows.Allocation)
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D (LIBW_WeakPerEnv.weakEnv world) child)
 (a : TX2_240.Args) (s : SdkState) (env : Env) :
 TAS.Frame s (NMV_ConcreteWindows.stage2 allocation child a s env) :=
 NMV_G2Reference.frame L D LIBB_V2Star.library pl (LIBW_WeakPerEnv.wEnv world)
  (LIBW_WeakPerEnv.writeFree world) a s env _
  (weak240_env world L D allocation child packet a s env)

theorem sdk_env {Ambient : Type} (world : NLM_PacketTypes.World Ambient)
 (L : PoolLib) (D : DeployedIds) (allocation : NMV_ConcreteWindows.Allocation)
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D (LIBW_WeakPerEnv.weakEnv world) child)
 (a : TX2_240.Args) (s t : SdkState) (env : Env)
 (r : Except ProgramError Unit) (events : List Event)
 (returned : NMV_ConcreteWindows.stage2 allocation child a s env = ⟨.ret (r,t),events⟩) :
 t.cells = s.cells ∧ t.next = s.next + (if TX2_240.badRoute a then 0 else 7) := by
 have h := weak240_env world L D allocation child packet a s env
 rw [returned] at h
 exact NMV_G2State.reference_sdk L D _ a s t env r events h

theorem weak240_any (Ambient : Type)
 (L : PoolLib) (D :DeployedIds) (allocation : NMV_ConcreteWindows.Allocation)
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D (LIBW_WeakPerEnv.weakAny Ambient) child)
 (a : TX2_240.Args) (s : SdkState) (env : Env) :
 TX2_240.Ref L D (LIBW_WeakPerEnv.weakAny Ambient) a s env
  (NMV_ConcreteWindows.stage2 allocation child a s env) :=
 NMV_CandidateRoots.root240 L D _ allocation child packet a s env
  (TCK.domain240_weaken _ _ a s)

theorem frame_any (Ambient : Type)
 (L : PoolLib) (D : DeployedIds) (pl : NMV_NoWrite.PoolLaws L)
 (allocation : NMV_ConcreteWindows.Allocation)
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D (LIBW_WeakPerEnv.weakAny Ambient) child)
 (a : TX2_240.Args) (s : SdkState) (env : Env) :
 TAS.Frame s (NMV_ConcreteWindows.stage2 allocation child a s env) :=
 NMV_G2Reference.frame L D LIBB_V2Star.library pl (LIBW_WeakPerEnv.wAny Ambient)
  (LIBW_WeakPerEnv.writeFree_any Ambient) a s env _
  (weak240_any Ambient L D allocation child packet a s env)

theorem sdk_any (Ambient : Type)
 (L : PoolLib) (D : DeployedIds) (allocation : NMV_ConcreteWindows.Allocation)
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D (LIBW_WeakPerEnv.weakAny Ambient) child)
 (a : TX2_240.Args) (s t : SdkState) (env : Env)
 (r : Except ProgramError Unit) (events : List Event)
 (returned : NMV_ConcreteWindows.stage2 allocation child a s env = ⟨.ret (r,t),events⟩) :
 t.cells = s.cells ∧ t.next = s.next + (if TX2_240.badRoute a then 0 else 7) := by
 have h := weak240_any Ambient L D allocation child packet a s env
 rw [returned] at h
 exact NMV_G2State.reference_sdk L D _ a s t env r events h

#print axioms weak240_env
#print axioms frame_env
#print axioms sdk_env
#print axioms weak240_any
#print axioms frame_any
#print axioms sdk_any
end NNP_G2
