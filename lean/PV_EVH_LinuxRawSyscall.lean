import PV_EVH_LinuxRawControl
set_option autoImplicit false
noncomputable section
namespace PV_EVH_LinuxRawSyscall
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_World (World)
open PV_EVH_LinuxRawControl (Reply)
variable [ExternalTypes]

/-- Serialization of mathematical syscall observations, not Rust formatting or
stderr. The register/ABI association remains V370; flags are fixed to zero. -/
def request (address length : Nat) : PV_RJ4IDB.NativeEvent :=
  .side (PV_EVH_StackZero.ascii "getrandom.raw.request")
    (PV_EVH_StackZero.ascii (toString address ++ ":" ++ toString length ++ ":0"))

def response (r : Reply) : PV_RJ4IDB.NativeEvent :=
  .side (PV_EVH_StackZero.ascii "getrandom.raw.response")
    (match r.result with
    | .returned (.ok ret) => PV_EVH_StackZero.ascii (toString ret) ++
        PV_EVH_StackEntropyFill.encode r.buffer
    | .returned (.fail _) => PV_EVH_StackZero.ascii "source.failure"
    | .returned .div => PV_EVH_StackZero.ascii "source.divergence"
    | .fault _ => PV_EVH_StackZero.ascii "runtime.fault"
    | .exhausted => PV_EVH_StackZero.ascii "prefix.exhaustion")

/-- No syscall return is fabricated: raw kernel deliveries retain their world,
post-buffer, status, and boundary observations. Request precedes that prefix;
only a completed raw return has a response event. -/
def call (kernel : Nat → Nat → Array U8 64#usize → World → Reply)
    (address length : Nat) (a : Array U8 64#usize) (w : World) : Reply :=
  let r := kernel address length a w
  {r with events := request address length :: (r.events ++
    match r.result with
    | .returned (.ok _) => [response r]
    | _ => [])}

theorem returned_prefix (kernel : Nat → Nat → Array U8 64#usize → World → Reply)
    (address length : Nat) (a : Array U8 64#usize) (w : World) (ret : Int)
    (h : (kernel address length a w).result = .returned (.ok ret)) :
    (call kernel address length a w).events =
      request address length :: ((kernel address length a w).events ++
        [response (kernel address length a w)]) := by
  simp only [call,h]

theorem fault_prefix (kernel : Nat → Nat → Array U8 64#usize → World → Reply)
    (address length : Nat) (a : Array U8 64#usize) (w : World) (e : PV_EVH_Runtime.Fault)
    (h : (kernel address length a w).result = .fault e) :
    (call kernel address length a w).events =
      request address length :: (kernel address length a w).events := by
  simp only [call,h,List.append_nil]

theorem exhaustion_prefix (kernel : Nat → Nat → Array U8 64#usize → World → Reply)
    (address length : Nat) (a : Array U8 64#usize) (w : World)
    (h : (kernel address length a w).result = .exhausted) :
    (call kernel address length a w).events =
      request address length :: (kernel address length a w).events := by
  simp only [call,h,List.append_nil]

theorem payload_retained (kernel : Nat → Nat → Array U8 64#usize → World → Reply)
    (address length : Nat) (a : Array U8 64#usize) (w : World) :
    (call kernel address length a w).result = (kernel address length a w).result ∧
    (call kernel address length a w).buffer = (kernel address length a w).buffer ∧
    (call kernel address length a w).world = (kernel address length a w).world := ⟨rfl,rfl,rfl⟩

#print axioms returned_prefix
#print axioms fault_prefix
#print axioms exhaustion_prefix
#print axioms payload_retained
end PV_EVH_LinuxRawSyscall
