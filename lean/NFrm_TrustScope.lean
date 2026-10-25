import ClaimsUnrolledFinish
import S2W_D189Consolidation
import Port1_Library

/-! Interface countermodels, NOT executions of Rust std or shipped source.
They prevent silently expanding the existing copy/allocator trust records. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFrm_TrustScope
open Aeneas Aeneas.Std Result

/-- Both slots are well typed and return; neither is a native interpretation. -/
def erasing : ClaimsUnrolledFinish.StdCalls where
  reserve := fun _ _ _ => ok (.Ok (), alloc.vec.Vec.new _)
  intoBox := fun _ _ => ok (alloc.vec.Vec.deref (alloc.vec.Vec.new _))

def singleton : alloc.vec.Vec Unit := ⟨[()], by simp; scalar_tac⟩

def ReserveFrame (calls : ClaimsUnrolledFinish.StdCalls) : Prop :=
  ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T) (n : Usize)
    (r : core.result.Result Unit AspisR1ClaimsUnrolledParent.alloc.collections.TryReserveError)
    (after : alloc.vec.Vec T), calls.reserve A v n = ok (r,after) → after.val = v.val

def BoxContents (calls : ClaimsUnrolledFinish.StdCalls) : Prop :=
  ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T) (after : Slice T),
    calls.intoBox A v = ok after → after.val = v.val

theorem reserve_frame_not_from_slots : ¬ ReserveFrame erasing := by
  intro frame
  have bad := frame Unit singleton 1#usize (.Ok ()) (alloc.vec.Vec.new Unit) rfl
  change ([] : List Unit) = [()] at bad
  cases bad

theorem box_contents_not_from_slots : ¬ BoxContents erasing := by
  intro frame
  have bad := frame Unit singleton (alloc.vec.Vec.deref (alloc.vec.Vec.new Unit)) rfl
  change ([] : List Unit) = [()] at bad
  cases bad

/-- Returning, inhabited countermodel: no impossible acceptance premise or
failing allocator is used. This only concerns the exact existing interfaces. -/
theorem copy_allocator_nonvacuity :
    ∃ (copy : S2Trust.Heap Unit → Nat → S2Trust.Payload → S2W_TrustedStd.Outcome Unit)
      (allocator : S2W_D189Wrappers.Allocator Unit)
      (calls : ClaimsUnrolledFinish.StdCalls),
      S2W_TrustedStd.TrustedStd copy ∧
      allocator.allocate () 1 = ok () ∧ allocator.cleanup () = ok () ∧
      (∃ result, calls.reserve Unit singleton 1#usize = ok result) ∧
      (∃ result, calls.intoBox Unit singleton = ok result) ∧
      ¬ ReserveFrame calls ∧ ¬ BoxContents calls := by
  refine ⟨S2W_TrustedStd.specification,
    ⟨fun state _ => ok state, fun state => ok state⟩, erasing,
    S2W_TrustedStd.specification_satisfies Unit, rfl, rfl,
    ⟨_,rfl⟩, ⟨_,rfl⟩, reserve_frame_not_from_slots, box_contents_not_from_slots⟩

/-- The copy law cannot supply an additional native reserve/Box field. -/
theorem no_uniform_reduction :
    ¬ (∀ calls : ClaimsUnrolledFinish.StdCalls,
      S2W_TrustedStd.TrustedStd (S2W_TrustedStd.specification (F := Unit)) →
      ReserveFrame calls ∧ BoxContents calls) := by
  intro reduction
  exact reserve_frame_not_from_slots
    (reduction erasing (S2W_TrustedStd.specification_satisfies Unit)).1

#print axioms reserve_frame_not_from_slots
#print axioms box_contents_not_from_slots
#print axioms copy_allocator_nonvacuity
#print axioms no_uniform_reduction
#print S2W_TrustedStd.TrustedStd
#print S2W_D189Wrappers.Allocator
#print S2W_D189Consolidation.RuntimeEntrypointAdmission
#print AdapterRw.RuntimeEntrypointAdmission
#print S2W_ExtractionBoundary.RuntimeSyscall
#print Port1_Library.TrustedStd
#print ClaimsUnrolledFinish.StdCalls
end AspisR1.NFrm_TrustScope
end
