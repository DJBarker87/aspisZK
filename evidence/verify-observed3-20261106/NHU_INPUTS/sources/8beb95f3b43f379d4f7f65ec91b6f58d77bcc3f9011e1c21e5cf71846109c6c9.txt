import NHU_ClaimsHeap
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_ClaimsOutcome
abbrev Flags := Nat→Bool
/-- Ghost initialization transducer for a single decoder/write boundary.
This is not a native Box ownership or destructor interpretation. -/
def step {A E : Type} (p : Nat) (before : Flags)
 (decoded : core.result.Result A E) : core.result.Result Unit E×Flags :=
 match decoded with
 | .Err e => (.Err e,before)
 | .Ok _ => (.Ok (),NHU_ClaimsHeap.write p before)

def run {A E : Type} (p : Nat) (before : Flags)
 (decoded : Result (core.result.Result A E)) : Result (core.result.Result Unit E×Flags) := do
 let status←decoded
 ok (step p before status)

theorem rejected {A E : Type} (p : Nat) (before : Flags) (e : E) :
 run p before (ok (.Err e) : Result (core.result.Result A E))=ok (.Err e,before) := rfl

theorem written {A E : Type} (p : Nat) (before : Flags) (a : A) :
 run p before (ok (.Ok a) : Result (core.result.Result A E))=
 ok (.Ok (),NHU_ClaimsHeap.write p before) := rfl

theorem failed {A E : Type} (p : Nat) (before : Flags) (e : Aeneas.Std.Error) :
 run p before (fail e : Result (core.result.Result A E))=fail e := rfl

theorem diverged {A E : Type} (p : Nat) (before : Flags) :
 run p before (div : Result (core.result.Result A E))=div := rfl

theorem next_invariant {A E : Type} (p : Nat) (a : A) :
 run p (NHU_ClaimsHeap.initialized p) (ok (.Ok a) : Result (core.result.Result A E))=
 ok (.Ok (),NHU_ClaimsHeap.initialized (p+1)) := by
 rw [written]
 congr 2
 funext cell
 exact NHU_ClaimsHeap.step p cell

#print axioms rejected
#print axioms written
#print axioms failed
#print axioms diverged
#print axioms next_invariant
end AspisR1.NHU_ClaimsOutcome
