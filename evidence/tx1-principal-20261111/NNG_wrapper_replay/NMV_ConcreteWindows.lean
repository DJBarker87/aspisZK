import NMV_SnapshotExec
import NMV_CopyExec
set_option autoImplicit false
namespace NMV_ConcreteWindows
open RSL NMV_WindowEval

/-- Concrete SDK/std/runtime interpretation of all stage fission windows.
No buffer bound, successful-child premise, or wrapper-output premise. -/
def windows (allocation : Nat → Bool) : Windows where
 snapshot := fun a x y s _ => NMV_SnapshotExec.run allocation a x y s
 clear := fun bytes _ => ⟨.ret (),[.returnData bytes]⟩
 clock := fun env => ⟨.ret env.clock,[.clock env.clock]⟩
 copy := fun a ck s _ => NMV_CopyExec.run a ck s
 snapshot_law := NMV_SnapshotExec.law allocation
 clear_law := fun _ _ => rfl
 clock_law := fun env => by
   refine Or.inl ⟨env.clock,[],⟨.ret env.clock,[.clock env.clock]⟩,rfl,?_,rfl⟩
   exact Or.inl ⟨(),[.clock env.clock],⟨.ret env.clock,[]⟩,rfl,rfl,rfl⟩
 copy_law := NMV_CopyExec.law

/-- Per-invocation allocation choices are observations, not an own-input
clause. All actual success/abort patterns at snapshot sites are admitted. -/
abbrev Allocation := TX2_240.Args → SdkState → Env → Nat → Bool

def stage2 (allocation : Allocation)
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (a : TX2_240.Args) (s : SdkState) (env : Env) : Obs (Except ProgramError Unit × SdkState) :=
 NMV_WindowStage.stage2 (windows (allocation a s env)) child a s env

def stage1 (allocation : Allocation)
 (child : TX1_345.Args → Env → Obs (Except ProgramError Bytes))
 (a : TX1_344.Args) (s : SdkState) (env : Env) : Obs (Except ProgramError Unit × SdkState) :=
 NMV_WindowStage.stage1 (windows (allocation a s env)) child a s env

theorem root240 (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (allocation : Allocation)
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D V child) :
 TX2_240.RowSpec_240 L D V (stage2 allocation child) := by
 intro a s env dom
 exact NMV_WindowRoots.root240 L D V (windows (allocation a s env)) child packet a s env dom

theorem root344 (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V)
 (allocation : Allocation)
 (child : TX1_345.Args → Env → Obs (Except ProgramError Bytes))
 (packet : TX1_345.RowSpec_345 V P C child) :
 TX1_344.RowSpec_344 V P C (stage1 allocation child) := by
 intro a s env dom
 exact NMV_WindowRoots.root344 V P C (windows (allocation a s env)) child packet a s env dom

#print axioms root240
#print axioms root344
end NMV_ConcreteWindows
