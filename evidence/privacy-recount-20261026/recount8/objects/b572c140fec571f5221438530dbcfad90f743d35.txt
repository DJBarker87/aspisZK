import R1Z.PV_FXM_DropSelected
import R1Z.PV_FXM_ReserveFacts
set_option autoImplicit false
namespace R1Z.PV_FXM_Physical
open Aeneas Aeneas.Std ProverRwFull

/-- Complete allocator-accessible state. Physical freed-memory writes and
external effects are here; the library buffer's `memory` field is a logical
snapshot whose validity is controlled by `live`, not a physical-free theorem. -/
structure Runtime (S F : Type) where
  allocator : S
  bytes : Nat → Option Nat
  external : F

/-- An arbitrary accessible external frame is inside Runtime. A separate D
can be a disjoint frame; no allocator-accessible state is assumed unchanged. -/
theorem drop_effect {S F D : Type}
    (free : Nat → Nat → Nat → Runtime S F → Runtime S F)
    (b : PV_FXM_DropWorld.Buffer)
    (w : PV_FXM_DropWorld.World (Runtime S F) D) (h : b.capacity≠0) :
    (PV_FXM_DropWorld.native free b w).2.allocator.bytes=
      (free b.address (4*b.capacity) 4 w.allocator).bytes ∧
    (PV_FXM_DropWorld.native free b w).2.allocator.external=
      (free b.address (4*b.capacity) 4 w.allocator).external := by
  unfold PV_FXM_DropWorld.native PV_FXM_DropWorld.release
  rw [if_neg h]
  exact ⟨rfl,rfl⟩

theorem drop_source_reference {S F D : Type}
    (free : Nat → Nat → Nat → Runtime S F → Runtime S F)
    (b : PV_FXM_DropWorld.Buffer)
    (w : PV_FXM_DropWorld.World (Runtime S F) D) :
    PV_FXM_DropWorld.native free b w=PV_FXM_DropWorld.reference free b w :=
  PV_FXM_DropWorld.source_reference free b w

theorem reserve_effect {T S F D : Type}
    (step : PV_FXM_ReserveWorld.Request → Runtime S F → Option Nat × Runtime S F)
    (shape : PV_FXM_ReserveWorld.Shape) (b : PV_FXM_ReserveWorld.Buffer T)
    (additional : Nat) (w : PV_FXM_ReserveWorld.World (Runtime S F) D) :
    let req : PV_FXM_ReserveWorld.Request :=
      ⟨b.address,b.capacity,b.values.length+additional,shape⟩
    (PV_FXM_ReserveWorld.finish step shape b additional w).world.allocator.bytes=
      (step req w.allocator).2.bytes ∧
    (PV_FXM_ReserveWorld.finish step shape b additional w).world.allocator.external=
      (step req w.allocator).2.external := by
  have h := PV_FXM_ReserveFacts.finish_effects step shape b additional w
  exact ⟨congrArg Runtime.bytes h.1,congrArg Runtime.external h.1⟩

theorem reserve_source_reference {T S F D : Type}
    (step : PV_FXM_ReserveWorld.Request → Runtime S F → Option Nat × Runtime S F)
    (wordMax byteMax : Nat) (shape : PV_FXM_ReserveWorld.Shape)
    (b : PV_FXM_ReserveWorld.Buffer T) (additional : Nat)
    (w : PV_FXM_ReserveWorld.World (Runtime S F) D) :
    PV_FXM_ReserveWorld.native step wordMax byteMax shape b additional w =
      PV_FXM_ReserveWorld.reference step wordMax byteMax shape b additional w :=
  PV_FXM_ReserveWorld.source_reference step wordMax byteMax shape b additional w

#print axioms drop_effect
#print axioms drop_source_reference
#print axioms reserve_effect
#print axioms reserve_source_reference
end R1Z.PV_FXM_Physical
