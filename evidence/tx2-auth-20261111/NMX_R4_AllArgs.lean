import NMX_R4_ArgsPort
import NMX_R3_Instantiated233
set_option autoImplicit false
noncomputable section
namespace NMX_R4_AllArgs
open Aeneas Aeneas.Std RSL NMX_SourceModel

/-- Total operational port. This becomes a candidate only after its observed
source association is supplied; representation facts never enter Domain. -/
def execution (owners : Owners) (alloc : NMX_R2_NativeExecution.Allocations) (failure : Error)
 (laneAllocation : Bytes → Env → Bool)
 (registryAllocation : TX2_234.Args → Env → Nat → Bool)
 (a : TX2_233.Args) (env : Env) : Obs (Except ProgramError Authenticated) :=
 if count : a.accounts.length = 7 then
   let native := NMX_R2_ArgsReify.reify (NMX_R4_ProjectionRef.args a) (NMX_R4_ArgsPort.bounds a count)
   NMX_R2_NativeExecution.run owners alloc failure
    (NMX_R3_LaneInstance.native owners.lane laneAllocation)
    (NMX_R2_CanonicalChildren.registry (NMX_R3_RegistryRoot.authenticate registryAllocation)) env
    (NMX_R2_Skeleton.auth native.program native.accounts native.pool native.lane native.slot)
 else ⟨.ret (.error (if a.accounts.length < 7 then .notEnoughAccountKeys else .invalidArgument)),[]⟩

theorem operational (owners : Owners) (alloc : NMX_R2_NativeExecution.Allocations) (failure : Error)
 (laneAllocation : Bytes → Env → Bool)
 (registryAllocation : TX2_234.Args → Env → Nat → Bool) :
 TX2_233.RowSpec_233 LIBB_PoolLib.library LIBB_PoolLib.deployed
  (execution owners alloc failure laneAllocation registryAllocation) := by
 intro a env _
 unfold execution
 split
 · rename_i count
   have h := NMX_R3_Instantiated233.represented owners alloc failure laneAllocation registryAllocation
    (NMX_R4_ProjectionRef.args a) (NMX_R4_ArgsPort.bounds a count) env
   rw [NMX_R4_ProjectionRef.reference] at h
   exact h
 · rename_i count
   rw [NMX_R2_CountReference.other _ _ a count]
   rfl
#print axioms operational
end NMX_R4_AllArgs
end
