import R1Z.PV_RDB2C_PV_B2_F_MaterializeRequest
import R1Z.PV_RDB2C_TypedRawVec
import R1Z.PV_RDB2C_Box
namespace R1Z.PV_RDB2C_V258
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_MutationStep
open PV_RDB2C_PublicRequests PV_RDB2C_Box
abbrev World (S : Type) := PV_RDB2C_Box.World Out S
abbrev RustResult := PV_B2_F_AllocationTransport.RustResult

def request : Request := ⟨32768,4,none⟩

def restore {S : Type} (p : Nat) (r : Result RustResult) (world : World S) : World S :=
  match r with
  | .ok (.Ok out) => {world with objects := fun a => if a=p then some out else world.objects a}
  | _ => world

/-- Full request/initialization/world adapter: zero-filled buffer on success,
Allocation before every arithmetic/mutable write on failure. -/
def run {S : Type} (compute : host_weights.Weights → E → Result RustResult)
    (allocate : Request → S → Option Nat × S) (w : host_weights.Weights) (kappa : E)
    (world : World S) : Result RustResult × World S :=
  match lowered allocate request PV_B2_F_AllocationTransport.zeros world with
  | (.allocationAbort,after) => (ok (.Err verifier.Error.Allocation),after)
  | (.returned p _,after) =>
    let r := compute w kappa
    (r,restore p r after)

def copied {S : Type} (allocate : Request → S → Option Nat × S)
    (w : host_weights.Weights) (kappa : E) (world : World S) :=
  run (PV_B2_F_AllocationEffects.copied (ok .supplied)) allocate w kappa world

def original {S : Type} (allocate : Request → S → Option Nat × S)
    (w : host_weights.Weights) (kappa : E) (world : World S) :=
  run (PV_B2_F_MaterializeRequest.original (ok .supplied)) allocate w kappa world

/-- Source order keeps the total, effect-free powers computation before the
public allocation. Every allocation outcome remains explicit. -/
def source {S : Type} (allocate : Request → S → Option Nat × S)
    (w : host_weights.Weights) (kappa : E) (world : World S) :
    Result RustResult × World S :=
  match host_weights.powers7 kappa with
  | .fail e => (fail e,world)
  | .div => (div,world)
  | .ok k =>
    match lowered allocate request PV_B2_F_AllocationTransport.zeros world with
    | (.allocationAbort,after) => (ok (.Err verifier.Error.Allocation),after)
    | (.returned p _,after) =>
      let r : Result RustResult := do
        let out ← PV_B2_F_MaterializeFrozen.remaining w k 1024 0#usize
          PV_B2_F_AllocationTransport.zeros
        ok (.Ok out)
      (r,restore p r after)

theorem source_order {S : Type} (allocate : Request → S → Option Nat × S)
    (w : host_weights.Weights) (kappa : E) (world : World S) :
    source allocate w kappa world=original allocate w kappa world := by
  obtain ⟨k,hk⟩ := PV_B2_C_Powers7Total.source kappa
  simp only [source,hk,original,run,PV_B2_F_MaterializeRequest.original,bind_tc_ok]

theorem complete {S : Type} (allocate : Request → S → Option Nat × S)
    (w : host_weights.Weights) (kappa : E) (world : World S) :
    copied allocate w kappa world=original allocate w kappa world := by
  have h : PV_B2_F_AllocationEffects.copied (ok .supplied) =
      PV_B2_F_MaterializeRequest.original (ok .supplied) := by
    funext weights challenge
    exact PV_B2_F_MaterializeRequest.complete_result (ok .supplied) weights challenge
  unfold copied original
  rw [h]

theorem allocation_failure {S : Type} (allocate : Request → S → Option Nat × S)
    (w : host_weights.Weights) (kappa : E) (world : World S) (state : S)
    (h : allocate request world.allocator=(none,state)) :
    copied allocate w kappa world =
      (ok (.Err verifier.Error.Allocation),
       {world with allocator := state,requests := world.requests++[request]}) := by
  simp only [copied,run,lowered,h]

theorem public_request (left right : host_weights.Weights) (a b : E) :
    (fun (_ : host_weights.Weights) (_ : E) => request) left a =
    (fun (_ : host_weights.Weights) (_ : E) => request) right b := rfl

#print axioms source_order
#print axioms complete
#print axioms allocation_failure
#print axioms public_request
end R1Z.PV_RDB2C_V258
