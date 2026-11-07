import NMX_R2_NativeDataBox
import NMX_R2_CheckpointPacket
import NMX_R2_ReadonlyNative
import NMX_R2_DistinctNative
set_option autoImplicit false
noncomputable section
namespace NMX_R2_NativeCommands
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel

/-- Every entered source command uses its actual typed arguments. The local
std interpretation is concrete; CLOSED pure helper roots are consumed here.
OPEN child observations remain complete and are constrained by the later fold. -/
theorem member (owners : Owners) (alloc : NMX_R2_NativeExecution.Allocations) (failure : Error)
 (ln : NMX_R2_RawChildren.LaneNative) (rn : NMX_R2_RawChildren.RegistryNative)
 (env : RSL.Env) {A : Type} (cmd : Command A) :
 NMX_R2_Semantics.command owners ln rn cmd env
  (NMX_R2_NativeExecution.command owners alloc failure ln rn env cmd) := by
 cases cmd with
 | raw r => rfl
 | readonlyBuffer a => exact NMX_R2_ReadonlyNative.buffer a env
 | checkpointGuard a program writable => exact NMX_R2_CheckpointPacket.packet env alloc.clone failure a program writable
 | readonlyAccount a expected => exact NMX_R2_ReadonlyNative.account (NMX_R2_StdOps.install env alloc.clone failure) a expected env
 | distinct accounts => exact NMX_R2_DistinctNative.packet (NMX_R2_StdOps.install env alloc.clone failure) accounts env
 | data a => exact NMX_R2_NativeDataBox.data env alloc.clone failure a
 | key a => rfl
 | toBytes key => rfl
 | fromBytes bytes => rfl
 | asRef key => rfl
 | master bytes => exact NMX_R2_NativeDataBox.box alloc.master owners.master (NMX_MasterValue.decoded bytes) env
 | checkpoint bytes => exact NMX_R2_NativeDataBox.box alloc.checkpoint owners.checkpoint (NMX_CheckpointValue.decoded bytes) env
 | lane bytes => rfl
 | registry verifier pool ma m r e slot => rfl
 | pda seeds program => rfl
 | snapshot payload => exact NMX_R2_NativeDataBox.box alloc.snapshot owners.snapshot (.Ok payload) env
#print axioms member
end NMX_R2_NativeCommands
end
