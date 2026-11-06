import NJH_SyscallLaws
set_option autoImplicit false
namespace NJH_ReplyComposition
open Aeneas Aeneas.Std Result
/-- Compose the full raw Clock reply with an explicitly supplied error
conversion. It is NOT an assertion that a particular conversion is the SDK's. -/
def project {E : Type} (mapError : U64 → E) :
    core.result.Result NJH_Ref.Clock U64 → core.result.Result U64 E
  | .Ok clock => .Ok clock.slot
  | .Err status => .Err (mapError status)
theorem slot_ok {E : Type} (mapError : U64 → E) (clock : NJH_Ref.Clock) :
    (do let r ← NJH_Ref.clock_ref 0#u64 clock; ok (project mapError r)) =
      ok (.Ok clock.slot) := by rw [NJH_SyscallLaws.clock_ok]; rfl
theorem slot_error {E : Type} (mapError : U64 → E) (status : U64)
    (clock : NJH_Ref.Clock) (h : status ≠ 0#u64) :
    (do let r ← NJH_Ref.clock_ref status clock; ok (project mapError r)) =
      ok (.Err (mapError status)) := by rw [NJH_SyscallLaws.clock_error status clock h]; rfl
/-- Continuations see the SAME complete error and original ambient state. -/
theorem error_prefix {E R S : Type} (e : E) (s : S)
    (next : U64 → Result (core.result.Result R E)) :
    ((do match (core.result.Result.Err e : core.result.Result U64 E) with
      | .Err err => ok (core.result.Result.Err err : core.result.Result R E)
      | .Ok slot => next slot),s) = (ok (core.result.Result.Err e : core.result.Result R E),s) := rfl
#print axioms slot_ok
#print axioms slot_error
#print axioms error_prefix
end NJH_ReplyComposition
