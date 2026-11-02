import R1Z.ProverRwFullExternalFuns
import R1Z.PDict_ReserveErrorSource
import R1Z.PV_FXM_ReserveWorld
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_FXM_ReserveSelected
open Aeneas Aeneas.Std ProverRwFull
open PV_FXM_ReserveWorld
variable [ExternalTypes]

structure Metadata {T : Type} (v : alloc.vec.Vec T) where
  address : Nat
  capacity : Nat
  fits : v.val.length≤capacity

def buffer {T : Type} (v : alloc.vec.Vec T) (m : Metadata v) : Buffer T :=
  ⟨m.address,m.capacity,v.val,m.fits⟩

def nativeError : PV_FXM_ReserveWorld.Error → PDict_ReserveError.alloc.collections.TryReserveError
  | .capacityOverflow => ⟨.CapacityOverflow⟩
  | .allocError layout => ⟨.AllocError layout ()⟩

/-- In the selected dictionary this carrier equality is the existing op5
installation. It is a type identity, not an assumption of a source law. -/
def encodeError (h : alloc.collections.TryReserveError =
    PDict_ReserveError.alloc.collections.TryReserveError) (e : PV_FXM_ReserveWorld.Error) :
    alloc.collections.TryReserveError := cast h.symm (nativeError e)

def returned (encode : PV_FXM_ReserveWorld.Error → alloc.collections.TryReserveError) :
    Except PV_FXM_ReserveWorld.Error Unit → core.result.Result Unit alloc.collections.TryReserveError
  | .ok u => .Ok u
  | .error e => .Err (encode e)

@[reducible] def selected {S F : Type} (ops : ExternalFuns)
    (step : Request → S → Option Nat × S) (wordMax byteMax : Nat)
    (shape : Type → Shape) (metadata : {T : Type} → (v : alloc.vec.Vec T) → Metadata v)
    (encode : PV_FXM_ReserveWorld.Error → alloc.collections.TryReserveError)
    (w : World S F) : ExternalFuns :=
  {ops with op32 := fun {T} _ v n =>
    let e := native step wordMax byteMax (shape T) (buffer v (metadata v)) n.val w
    Result.ok (returned encode e.returned,v)}

theorem other_fields {S F : Type} (ops : ExternalFuns)
    (step : Request → S → Option Nat × S) (wordMax byteMax : Nat)
    (shape : Type → Shape) (metadata : {T : Type} → (v : alloc.vec.Vec T) → Metadata v)
    (encode : PV_FXM_ReserveWorld.Error → alloc.collections.TryReserveError) (w : World S F) :
    {selected ops step wordMax byteMax shape metadata encode w with op32 := ops.op32}=ops := rfl

theorem error_payload (h : alloc.collections.TryReserveError =
    PDict_ReserveError.alloc.collections.TryReserveError) (e : PV_FXM_ReserveWorld.Error) :
    cast h (encodeError h e)=nativeError e := by simp only [encodeError,cast_cast,cast_eq]

/-- This is a world-indexed family of original-carrier dictionaries. The
allocator error is an inner Err, never converted into panic or unconditional Ok. -/
theorem complete {T S F : Type} (ops : ExternalFuns) (A : Type)
    (step : Request → S → Option Nat × S) (wordMax byteMax : Nat)
    (shape : Type → Shape) (metadata : {U : Type} → (v : alloc.vec.Vec U) → Metadata v)
    (encode : PV_FXM_ReserveWorld.Error → alloc.collections.TryReserveError)
    (v : alloc.vec.Vec T) (n : Usize) (w : World S F) :
    @alloc.vec.Vec.try_reserve_exact _
      (selected ops step wordMax byteMax shape metadata encode w) T A v n =
    .ok (returned encode (native step wordMax byteMax (shape T)
      (buffer v (metadata v)) n.val w).returned,v) := rfl

theorem execution {T S F A : Type} (ops : ExternalFuns) (Allocator : Type)
    (step : Request → S → Option Nat × S) (wordMax byteMax : Nat)
    (shape : Type → Shape) (metadata : {U : Type} → (v : alloc.vec.Vec U) → Metadata v)
    (encode : PV_FXM_ReserveWorld.Error → alloc.collections.TryReserveError)
    (v : alloc.vec.Vec T) (n : Usize) (w : World S F)
    (caller : core.result.Result Unit alloc.collections.TryReserveError →
      alloc.vec.Vec T → World S F → Result A) :
    (do let (r,v') ← @alloc.vec.Vec.try_reserve_exact _
          (selected ops step wordMax byteMax shape metadata encode w) T Allocator v n
        caller r v' (native step wordMax byteMax (shape T) (buffer v (metadata v)) n.val w).world) =
      caller (returned encode (reference step wordMax byteMax (shape T)
        (buffer v (metadata v)) n.val w).returned) v
        (reference step wordMax byteMax (shape T) (buffer v (metadata v)) n.val w).world := by
  simp only [complete,bind_tc_ok,source_reference]
  rfl

#print axioms other_fields
#print axioms error_payload
#print axioms complete
#print axioms execution
end R1Z.PV_FXM_ReserveSelected
