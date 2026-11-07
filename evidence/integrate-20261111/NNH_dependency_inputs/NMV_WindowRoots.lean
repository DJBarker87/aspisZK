import NMV_WindowStage
import NMV_G2State
set_option autoImplicit false
namespace NMV_WindowRoots
open RSL NMV_WindowEval

/-- Canonical 240 packet, parametric in EVERY verifier library, after the
source-fission windows are interpreted by their SDK/std/runtime laws. -/
theorem root240 (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (w : Windows) (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D V child) :
 TX2_240.RowSpec_240 L D V (NMV_WindowStage.stage2 w child) := by
 intro a s env dom
 exact NMV_RslFold.fold240 L D V child packet a s env dom _
   (NMV_WindowStage.cut240 w child a s env)

/-- Canonical 344 packet, full child error/owned checkpoint and copy footprint. -/
theorem root344 (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V)
 (w : Windows) (child : TX1_345.Args → Env → Obs (Except ProgramError Bytes))
 (packet : TX1_345.RowSpec_345 V P C child) :
 TX1_344.RowSpec_344 V P C (NMV_WindowStage.stage1 w child) := by
 intro a s env _
 exact NMV_RslFold.fold344 V P C child packet a s env _
   (NMV_WindowStage.cut344 w child a s env)

/-- Actual window-interpreted weak instance: no Root0 or selected-occurrence
hypothesis, and no separate wrapper-producer/endpoint premise. -/
theorem weak240 (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (law : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
 (w : Windows) (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D (TCK.weaken V law) child)
 (a : TX2_240.Args) (s : SdkState) (env : Env) :
 TX2_240.Ref L D (TCK.weaken V law) a s env (NMV_WindowStage.stage2 w child a s env) :=
 root240 L D (TCK.weaken V law) w child packet a s env (TCK.domain240_weaken V law a s)

theorem weak_sdk (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (law : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
 (w : Windows) (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D (TCK.weaken V law) child)
 (a : TX2_240.Args) (s t : SdkState) (env : Env)
 (r : Except ProgramError Unit) (events : List Event)
 (returned : NMV_WindowStage.stage2 w child a s env = ⟨.ret (r,t),events⟩) :
 t.cells=s.cells ∧ t.next=s.next+(if TX2_240.badRoute a then 0 else 7) := by
 have h := weak240 L D V law w child packet a s env
 rw [returned] at h
 exact NMV_G2State.reference_sdk L D (TCK.weaken V law) a s t env r events h

#print axioms root240
#print axioms root344
#print axioms weak240
#print axioms weak_sdk
end NMV_WindowRoots
