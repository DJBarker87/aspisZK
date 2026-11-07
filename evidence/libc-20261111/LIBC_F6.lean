import LIBC_Checkpoint
import NHS_CheckpointPacket
set_option autoImplicit false
noncomputable section
namespace LIBC_F6
open Aeneas Aeneas.Std RSL
/-- No invented post-abort state: the allocation outcome has exactly the
empty event prefix and the successful path has all three actual digest calls. -/
theorem outcomes (a : LIBC_Checkpoint.Args) (env : Env) (o : Obs Bytes) :
 LIBC_Checkpoint.child.law a env o ↔ LIBC_Checkpoint.Domain a ∧
 (o=⟨.ret (LIBC_Checkpoint.value a env),LIBC_Checkpoint.events a env⟩ ∨ o=⟨.abort,[]⟩) := Iff.rfl
/-- Prior-stage provenance is replaced by exactly the current-pair
DriverEstablishedDomain. This does not assume any preceding child succeeds. -/
theorem current_pair (a : LIBC_Checkpoint.Args) :
 NGC_KNE_Caller.DriverEstablishedDomain (LIBC_CheckpointDomain.reached a) ↔
 NGC_KNE_Caller.WriterDomain (LIBC_Checkpoint.prepared a) (LIBC_Checkpoint.accumulator a) :=
 LIBC_CheckpointDomain.driver_iff a
#print axioms outcomes
#print axioms current_pair
end LIBC_F6
