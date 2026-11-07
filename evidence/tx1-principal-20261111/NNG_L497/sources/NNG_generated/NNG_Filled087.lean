import NMP_EmittedContext
import LIBC_Filled
import NNG_Data137
import NNG_EmittedCallGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Filled087
open Aeneas Aeneas.Std Result NMP_prepare

/-- Full fallible heap reply on the SAME reservation binder. Clone is invoked
only at u8 in this parent; its CLOSED064 model is checked below. -/
def call (env : RSL.Env) {T : Type} (_copy : core.marker.Copy T) (n : Usize) (x : T) :
    Result (core.result.Result (alloc.vec.Vec T) aspis_core.r0.Error) :=
  .ok (if env.reservation then .Ok ⟨List.replicate n.val x,by
    rw [List.length_replicate]; scalar_tac⟩ else .Err .Allocation)

def port (r : core.result.Result (alloc.vec.Vec U8) aspis_core.r0.Error) : Except Unit RSL.Bytes :=
  match r with | .Ok v=>.ok (LIB_Carriers.bytes (alloc.vec.Vec.deref v)) | .Err _=>.error ()

theorem model (env : RSL.Env) (n : Usize) :
  NNG_EmittedCallGraph.resultMap port (call env core.marker.CopyU8 n 0#u8) =
    NNG_EmittedCallGraph.resultMap LIBC_Filled.port
      (OraclePortStdAllocation.filled n 0#u8 env.reservation) := by
  rw [LIBC_Filled.model]
  cases env.reservation <;> rfl

theorem projected (env : RSL.Env) (n : Usize) :
  NNG_EmittedCallGraph.resultMap port (call env core.marker.CopyU8 n 0#u8) =
    .ok (LIBC_Filled.value n.val env) := by
  rw [model]
  exact LIBC_Filled.model_port n env
#print axioms model
#print axioms projected
end AspisR1.NNG_Filled087
