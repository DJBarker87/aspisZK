import NKP_BoxCuts
import NKA_ClaimsRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_BoxAction
open Aeneas Aeneas.Std Result
abbrev PE := NKF_BoxModel.PE
structure Owned (T : Type) where
 owner : Nat
 value : T
 deriving DecidableEq
inductive Event where
 | allocate (owner bytes alignment : Nat)
 | returned (owner : Nat)
 | exhausted
 deriving DecidableEq

/-- Box::new is infallible at its Rust Result type. A rejected allocation
aborts instead of constructing InvalidAccountData. Reservation is the outcome
at this SAME allocation site under the retained Allocator interpretation. -/
def newBox {T S : Type} (allocator : S2W_D189Wrappers.Allocator S)
 (before : S) (bytes : Nat) (r : NP6_StdModel.Reservation)
 (owner : Nat) (value : T) : Result (Owned T × S) := do
 let post ← allocator.allocate before bytes
 match r with
 | .Ok _ => ok (⟨owner,value⟩,post)
 | .Err _ => fail .panic

/-- Literal source order: decode/map_err/? first, Box::new only on Ok. -/
def run {T S : Type} (allocator : S2W_D189Wrappers.Allocator S)
 (before : S) (bytes : Nat) (r : NP6_StdModel.Reservation) (owner : Nat)
 (decoded : Result (core.result.Result T PE)) :
 Result (core.result.Result (Owned T) PE × S) := do
 let raw ← decoded
 match raw with
 | .Err e => ok (.Err e,before)
 | .Ok value => do
  let (box,post) ← newBox allocator before bytes r owner value
  ok (.Ok box,post)

/-- The event projection keeps the allocation prefix even on fail/div.
No cleanup/second allocation occurs in the returning wrapper tail. -/
def events {T S : Type} (allocator : S2W_D189Wrappers.Allocator S)
 (before : S) (bytes alignment : Nat) (r : NP6_StdModel.Reservation) (owner : Nat)
 (decoded : Result (core.result.Result T PE)) : List Event :=
 match decoded with
 | .ok (.Ok _) => .allocate owner bytes alignment ::
   match allocator.allocate before bytes,r with
   | .ok _,.Ok _ => [.returned owner]
   | .ok _,.Err _ => [.exhausted]
   | _,_ => []
 | _ => []

theorem rejected {T S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (n : Nat) (r : NP6_StdModel.Reservation) (owner : Nat) (e : PE) :
 run a s n r owner (ok (.Err e : core.result.Result T PE))=ok (.Err e,s) := rfl

theorem allocator_failure {T S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (n : Nat) (r : NP6_StdModel.Reservation) (owner : Nat) (value : T)
 (e : Error) (h : a.allocate s n=fail e) :
 run a s n r owner (ok (.Ok value))=fail e := by
 simp only [run,newBox,bind_tc_ok,h,bind_tc_fail]

theorem allocator_divergence {T S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (n : Nat) (r : NP6_StdModel.Reservation) (owner : Nat) (value : T)
 (h : a.allocate s n=div) : run a s n r owner (ok (.Ok value))=div := by
 simp only [run,newBox,bind_tc_ok,h,bind_tc_div]

theorem reservation_rejection {T S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (n : Nat) (owner : Nat) (value : T) (e : NP6_StdModel.ReserveError) :
 run a s n (.Err e) owner (ok (.Ok value))=
 (do let _ ← a.allocate s n; fail .panic) := by
 simp only [run,newBox,bind_tc_ok]
 cases h:a.allocate s n <;> simp [h]

theorem returning {T S : Type} (a : S2W_D189Wrappers.Allocator S) (s post : S)
 (n : Nat) (owner : Nat) (value : T) (h : a.allocate s n=ok post) :
 run a s n (.Ok ()) owner (ok (.Ok value))=ok (.Ok ⟨owner,value⟩,post) := by
 simp only [run,newBox,bind_tc_ok,h]
 rfl

/-- Lift an existing complete value Result, without assuming decoder or
allocation success. Both wrappers use this implication at SAME bytes. -/
theorem substitute {T S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (n : Nat) (r : NP6_StdModel.Reservation) (owner : Nat)
 (value : core.result.Result T PE) (reference : Result (core.result.Result T PE))
 (h : ok value=reference) : run a s n r owner (ok value)=run a s n r owner reference :=
 congrArg (run a s n r owner) h

#print axioms rejected
#print axioms allocator_failure
#print axioms allocator_divergence
#print axioms reservation_rejection
#print axioms returning
#print axioms substitute
end AspisR1.NKY_BoxAction
end
