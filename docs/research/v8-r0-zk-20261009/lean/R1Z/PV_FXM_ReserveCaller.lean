import R1Z.PV_FXM_ReserveSelected
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_FXM_ReserveCaller
open Aeneas Aeneas.Std ProverRwFull PV_FXM_ReserveWorld
variable [ExternalTypes]

/-- The updated runtime header is retained beside the extracted vector value.
In particular, the next push receives the post-reserve capacity, not a capacity
reconstructed from the unchanged value list. -/
def postMetadata {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (v : alloc.vec.Vec T)
    (m : PV_FXM_ReserveSelected.Metadata v) (n : Usize) (w : World S F) :
    PV_FXM_ReserveSelected.Metadata v :=
  let e := native step wordMax byteMax shape (PV_FXM_ReserveSelected.buffer v m) n.val w
  ⟨e.buffer.address,e.buffer.capacity,by
    have h := values_preserved step wordMax byteMax shape
      (PV_FXM_ReserveSelected.buffer v m) n.val w
    calc v.val.length = e.buffer.values.length := (congrArg List.length h).symm
         _ ≤ e.buffer.capacity := e.buffer.fits⟩

theorem execution {T S F A : Type} (ops : ExternalFuns) (Allocator : Type)
    (step : Request → S → Option Nat × S) (wordMax byteMax : Nat)
    (shape : Type → Shape)
    (metadata : {U : Type} → (v : alloc.vec.Vec U) → PV_FXM_ReserveSelected.Metadata v)
    (encode : PV_FXM_ReserveWorld.Error → alloc.collections.TryReserveError)
    (v : alloc.vec.Vec T) (n : Usize) (w : World S F)
    (caller : core.result.Result Unit alloc.collections.TryReserveError →
      alloc.vec.Vec T → Buffer T → World S F → Result A) :
    (do let (r,v') ← @alloc.vec.Vec.try_reserve_exact _
          (PV_FXM_ReserveSelected.selected ops step wordMax byteMax shape metadata encode w)
          T Allocator v n
        let e := native step wordMax byteMax (shape T)
          (PV_FXM_ReserveSelected.buffer v (metadata v)) n.val w
        caller r v' e.buffer e.world) =
      let e := reference step wordMax byteMax (shape T)
        (PV_FXM_ReserveSelected.buffer v (metadata v)) n.val w
      caller (PV_FXM_ReserveSelected.returned encode e.returned) v e.buffer e.world := by
  simp only [PV_FXM_ReserveSelected.complete,bind_tc_ok,source_reference]
  rfl

theorem metadata_header {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (v : alloc.vec.Vec T)
    (m : PV_FXM_ReserveSelected.Metadata v) (n : Usize) (w : World S F) :
    (postMetadata step wordMax byteMax shape v m n w).address=
      (native step wordMax byteMax shape (PV_FXM_ReserveSelected.buffer v m) n.val w).buffer.address ∧
    (postMetadata step wordMax byteMax shape v m n w).capacity=
      (native step wordMax byteMax shape (PV_FXM_ReserveSelected.buffer v m) n.val w).buffer.capacity :=
  ⟨rfl,rfl⟩

#print axioms execution
#print axioms metadata_header
end R1Z.PV_FXM_ReserveCaller
