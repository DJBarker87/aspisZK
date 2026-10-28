import R1Z.PV_RDB2C_PV_B2_C_ConstructorSuccess
import R1Z.PV_RDB2C_Box
namespace R1Z.PV_RDB2C_V259
open Aeneas Aeneas.Std Result PV_B2_C_WeightsNative PV_B2_C_ConstructorRows
open PV_RDB2C_PublicRequests PV_RDB2C_Box
abbrev Weight := host_weights.Weights
abbrev World (S : Type) := PV_RDB2C_Box.World Weight S
abbrev Returned := Except Unit (core.result.Result (Nat × Weight) verifier.Error)

def request : Request := ⟨2116,4,none⟩

def finish {S : Type} (allocate : Request → S → Option Nat × S)
    (r : core.result.Result Weight verifier.Error) (world : World S) : Returned × World S :=
  match r with
  | .Err e => (.ok (.Err e),world)
  | .Ok value =>
    let (out,world) := lowered allocate request value world
    match out with
    | .allocationAbort => (.error (),world)
    | .returned p value => (.ok (.Ok (p,value)),world)

def copied {S : Type} (allocate : Request → S → Option Nat × S)
    (variant : transport.Variant) (alpha : Array K 10#usize) (z : Array Point 2#usize)
    (world : World S) : Result (Returned × World S) := do
  let r ← host_weights.Weights.new variant alpha z
  ok (finish allocate r world)

def original {S : Type} (allocate : Request → S → Option Nat × S)
    (variant : transport.Variant) (alpha : Array K 10#usize) (z : Array Point 2#usize)
    (world : World S) : Result (Returned × World S) := do
  let r ← PV_B2_C_ConstructorSuccess.staged variant alpha z
  ok (finish allocate r world)

theorem complete {S : Type} (allocate : Request → S → Option Nat × S)
    (variant : transport.Variant) (alpha : Array K 10#usize) (z : Array Point 2#usize)
    (world : World S) :
    copied allocate variant alpha z world=original allocate variant alpha z world := by
  unfold copied original
  rw [PV_B2_C_ConstructorSuccess.new_eq_staged]

/-- Abort remains an outer allocation outcome. It is not a fabricated
verifier Error::Allocation. Allocator private post-state is retained. -/
theorem failure_branch {S : Type} (allocate : Request → S → Option Nat × S)
    (value : Weight) (world : World S) (state : S)
    (h : allocate request world.allocator=(none,state)) :
    finish allocate (.Ok value) world =
      (.error (),{world with allocator := state,requests := world.requests++[request]}) := by
  simp only [finish,lowered,h]

theorem public_request (left right : Weight) :
    (fun (_ : Weight) => request) left=(fun (_ : Weight) => request) right := rfl

#print axioms complete
#print axioms failure_branch
#print axioms public_request
end R1Z.PV_RDB2C_V259
