import R1Z.PV_FXM_DropSelected
import R1Z.PV_FXM_ZeroConsumed
import R1Z.PV_FXM_ReserveCaller
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_FXM_AuditInstall
open Aeneas Aeneas.Std ProverRwFull PV_FXM_ReserveWorld
variable [ExternalTypes] {S F : Type}

/-- Composition of the four callback field updates in one original carrier.
The reserve dictionary remains indexed by the current invocation world and
metadata. This is not a state-free whole-prover execution theorem. -/
@[reducible] def selected (ops : ExternalFuns)
    (step : Request → S → Option Nat × S) (wordMax byteMax : Nat)
    (shape : Type → Shape)
    (metadata : {T : Type} → (v : alloc.vec.Vec T) → PV_FXM_ReserveSelected.Metadata v)
    (encode : PV_FXM_ReserveWorld.Error → alloc.collections.TryReserveError)
    (w : World S F) : ExternalFuns :=
  PV_FXM_ReserveSelected.selected
    (PV_FXM_ZeroSelected.selected (PV_FXM_DropSelected.selected ops))
    step wordMax byteMax shape metadata encode w

variable (ops : ExternalFuns) (step : Request → S → Option Nat × S)
  (wordMax byteMax : Nat) (shape : Type → Shape)
  (metadata : {T : Type} → (v : alloc.vec.Vec T) → PV_FXM_ReserveSelected.Metadata v)
  (encode : PV_FXM_ReserveWorld.Error → alloc.collections.TryReserveError) (w : World S F)

theorem other_fields :
    {selected ops step wordMax byteMax shape metadata encode w with
      op4 := ops.op4,op32 := ops.op32,op122 := ops.op122,op123 := ops.op123}=ops := rfl

theorem drop (v : alloc.vec.Vec U32) :
    (selected ops step wordMax byteMax shape metadata encode w).op4 v=.ok () := by
  change (PV_FXM_DropSelected.selected ops).op4 v=.ok ()
  exact PV_FXM_DropSelected.installed ops v

theorem other_drop_types {T : Type} (h : T≠alloc.vec.Vec U32) (x : T) :
    (selected ops step wordMax byteMax shape metadata encode w).op4 x=ops.op4 x := by
  change (PV_FXM_DropSelected.selected ops).op4 x=ops.op4 x
  exact PV_FXM_DropSelected.other_types ops h x

theorem array {N : Usize} (a : Array U8 N) :
    (selected ops step wordMax byteMax shape metadata encode w).op122
      PV_FXM_ZeroSelected.byteZero a=.ok (Array.repeat N 0#u8) := by
  change (PV_FXM_ZeroSelected.selected (PV_FXM_DropSelected.selected ops)).op122
    PV_FXM_ZeroSelected.byteZero a=.ok (Array.repeat N 0#u8)
  exact PV_FXM_ZeroSelected.array_installed (PV_FXM_DropSelected.selected ops) a

theorem scalar (x : U8) :
    (selected ops step wordMax byteMax shape metadata encode w).op123
      PV_FXM_ZeroSelected.byteDefault x=.ok 0#u8 := by
  change (PV_FXM_ZeroSelected.selected (PV_FXM_DropSelected.selected ops)).op123
    PV_FXM_ZeroSelected.byteDefault x=.ok 0#u8
  exact PV_FXM_ZeroSelected.scalar_installed (PV_FXM_DropSelected.selected ops) x

theorem reserve {T : Type} (Allocator : Type) (v : alloc.vec.Vec T) (n : Usize) :
    (selected ops step wordMax byteMax shape metadata encode w).op32 Allocator v n=
      .ok (PV_FXM_ReserveSelected.returned encode
        (native step wordMax byteMax (shape T)
          (PV_FXM_ReserveSelected.buffer v (metadata v)) n.val w).returned,v) := rfl

#print axioms other_fields
#print axioms drop
#print axioms other_drop_types
#print axioms array
#print axioms scalar
#print axioms reserve
end R1Z.PV_FXM_AuditInstall
