import PCD_State
set_option autoImplicit false
namespace PCD
/-- Syscall-level observations are separate from runtime value laws. -/
structure ClearObservation where
  bytes : Bytes
  reply : Exit Unit
  events : List Event
structure ReadObservation where
  reply : Exit Register
  events : List Event

/-- POOL:344 typed target, to be proved by PCB at the actual runtime wrapper.
No read-register value law, CPI frame or successful runtime call is inferred.
The empty-byte syscall argument and its call position are the native obligation. -/
def RowSpec_POOL_344 (native : State → ClearObservation) : Prop :=
  ∀ s, (native s).bytes = [] ∧ (native s).reply = .ok () ∧
    (native s).events = [.clear]

/-- POOL:345 returns the SAME syscall reply unchanged at the same state.
The underlying syscall is an explicit interpretation parameter for this open
packet, never an Ops hypothesis in a CLOSED root. -/
def RowSpec_POOL_345 (native syscall : State → ReadObservation) : Prop :=
  ∀ s, native s = syscall s

/-- Named runtime return-data trust, not a native certificate. -/
def RuntimeReturnData (read : State → Register)
    (write : State → Key → Bytes → State) : Prop :=
  ∀ s program bytes, 1 ≤ bytes.length → bytes.length ≤ 1024 →
    read (write s program bytes) = some (program,bytes)

def RuntimeReturnDataClear (clear : State → State) (read : State → Register) : Prop :=
  ∀ s, read (clear s) = none

/-- The exact distinction used by NIB: state equality is supplied separately
from the platform value law; a chronology summary cannot supply this equality. -/
theorem same_projection_read (read : State → Register)
    (write : State → Key → Bytes → State) (law : RuntimeReturnData read write)
    (s reached : State) (program : Key) (bytes : Bytes)
    (nonempty : 1 ≤ bytes.length) (bounded : bytes.length ≤ 1024)
    (projection : reached = write s program bytes) :
    read reached = some (program,bytes) := by
  rw [projection]
  exact law s program bytes nonempty bounded

#print axioms same_projection_read
end PCD
