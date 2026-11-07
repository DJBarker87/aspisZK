import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S013
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 13: rust; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (proof : r1_pool_adapter.owned.OwnedAccount)
 (masterAccount : r1_pool_adapter.owned.OwnedAccount)
 (checkpointAccount : r1_pool_adapter.owned.OwnedAccount)
 (laneAccount : r1_pool_adapter.owned.OwnedAccount)
 (registryAccount : r1_pool_adapter.owned.OwnedAccount)
 (entryAccount : r1_pool_adapter.owned.OwnedAccount)
 (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount)
 (next : Unit → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.distinct (Array.make 7#usize [proof,masterAccount,checkpointAccount,
  laneAccount,registryAccount,entryAccount,verifierCheckpoint]))) next) ()) =
 tryThen (r1_pool_adapter.owned.require_distinct_accounts ops (Array.make 7#usize [proof,masterAccount,checkpointAccount,
  laneAccount,registryAccount,entryAccount,verifierCheckpoint])) (fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ())) := by
 rw [NMX_StepCore.entered]
 exact NMX_ResultSteps.rust ops owners _ _ next
#print axioms step
end NMX_S013
end
