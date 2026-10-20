import CuSavingsRhoEmptyReserve
import AspisR1RhoHeap.TypesExternal

/-! Logical projection of the actual std reservation wrapper, restricted to
its actual Vec::new input. Buffer capacity/allocation results remain arbitrary;
no buffer-copying, reservation-success, or equivalence proposition is assumed.
Nonempty inputs retain a separate arbitrary computation and are never used by
source_filled. The zero-length source frame justifies erasing only capacity. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoEmptyReserveModel
open Aeneas Aeneas.Std Result AspisR1RhoEmptyReserve AspisR1CuRho

structure Backend where
  ReserveError : Type
  Buffer : Type → Type → Type
  initial : (T A : Type) → Buffer T A
  operations : (T A : Type) → RawReserve (Buffer T A) ReserveError
  nonempty : {T : Type} → (A : Type) → alloc.vec.Vec T → Usize →
    Result ((core.result.Result Unit ReserveError) × alloc.vec.Vec T)

def reserveEmpty (backend : Backend) {T : Type} (A : Type) (additional : Usize) :
    Result ((core.result.Result Unit backend.ReserveError) × alloc.vec.Vec T) := do
  let (result,_) ← source_reserve (backend.operations T A)
    ⟨backend.initial T A,0#usize⟩ additional
  .ok (result,alloc.vec.Vec.new T)

/-- This instance's empty branch is the logical projection proved from the
whole emitted std wrapper. It preserves allocation errors and divergence. -/
@[reducible] def heapReserve (backend : Backend) : HeapReserve where
  ReserveError := backend.ReserveError
  reserve := fun {T} A input additional =>
    if input.val.isEmpty then reserveEmpty backend A additional
    else backend.nonempty A input additional

theorem reserve_new (backend : Backend) (T A : Type) (additional : Usize) :
    (heapReserve backend).reserve A (alloc.vec.Vec.new T) additional =
      reserveEmpty backend A additional := rfl

theorem reserve_empty_frame (backend : Backend) (T A : Type) (additional : Usize)
    (result : core.result.Result Unit backend.ReserveError) (output : alloc.vec.Vec T)
    (h : (heapReserve backend).reserve A (alloc.vec.Vec.new T) additional = .ok (result,output)) :
    output=alloc.vec.Vec.new T := by
  rw [reserve_new] at h
  unfold reserveEmpty at h
  cases hr : source_reserve (backend.operations T A) ⟨backend.initial T A,0#usize⟩ additional with
  | fail error => simp only [hr,bind_tc_fail] at h;cases h
  | div => simp only [hr,bind_tc_div] at h;cases h
  | ok pair =>
    simp only [hr,bind_tc_ok,uncurry_apply_pair] at h
    exact (congrArg Prod.snd (Result.ok.inj h)).symm

theorem physical_projection {B E T : Type} (ops : RawReserve B E)
    (initial : B) (physical : VecProjection B) (additional : Usize)
    (result : core.result.Result Unit E)
    (h : source_reserve ops ⟨initial,0#usize⟩ additional = .ok (result,physical)) :
    (alloc.vec.Vec.new T).val.length=physical.len.val := by
  have hl := CuSavingsRhoEmptyReserve.source_length ops ⟨initial,0#usize⟩ physical additional result h
  rw [hl]
  scalar_tac

#print axioms Backend
#print axioms reserve_new
#print axioms reserve_empty_frame
#print axioms physical_projection
end AspisR1.CuSavingsRhoEmptyReserveModel
