import R1Z.PV_RunJoin_Deployed
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InitialCapacity
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable [ProverRwFull.ExternalTypes]
variable {CommitHandle Aux Coins N L C : Type}
variable (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N L C)

theorem provider_coordinates (r : PV_RunJoin_Deployed.World runtime) :
    r.state.provider = PV_RunJoin_CompletedWorld.provider runtime.world r.coins :=
  congrArg (fun s => s.provider) r.state_eq

theorem capacity (r : PV_RunJoin_Deployed.World runtime) :
    r.state.provider.used.val < r.state.provider.replies.val.length := by
  rw [provider_coordinates runtime r]
  have cursor : (PV_RunJoin_CompletedWorld.provider runtime.world r.coins).used.val = 0 := rfl
  have length : (PV_RunJoin_CompletedWorld.provider runtime.world r.coins).replies.val.length = 128 := by
    simp only [PV_RunJoin_CompletedWorld.provider,List.length_ofFn]
  rw [cursor,length]
  exact Nat.zero_lt_succ _

#print axioms provider_coordinates
#print axioms capacity
end R1Z.PV_RunJoin_InitialCapacity
