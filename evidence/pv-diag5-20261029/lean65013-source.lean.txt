import PV_DIAG3_Ownership
/-! anyhow ErrorImpl field order, Box/Vec cleanup, and LazyLock::drop.
All allocator operations remain explicit. No deallocation is silently
classified as an empty effect or as publicly scheduled. -/
set_option autoImplicit false
namespace PV_DIAG3
variable {S : Type}
inductive LazyState where | incomplete | complete | poisoned
 deriving DecidableEq, Repr
def lazyDrop (state : LazyState) (dropClosure dropValue : Op S Unit) : Op S Unit :=
 match state with
 | .incomplete => dropClosure
 | .complete => dropValue
 | .poisoned => pure ()
def boxDeallocate (size : Nat) (deallocate : Op S Unit) : Op S Unit :=
 if size = 0 then pure () else deallocate
/-- The pointee is dropped before Box::drop; its allocation is also freed
when the pointee unwinds. RawVec similarly follows vector element cleanup. -/
def allocationDrop (payload deallocate : Op S Unit)
 (doublePanic : Panic → Panic → Op S Unit) : Op S Unit := scope payload deallocate doublePanic
/-- ErrorImpl<E>: static vtable reference, backtrace, then _object. The Box
allocation is released after fields; concrete payload Drop is not omitted. -/
def errorObjectDrop (backtrace message deallocate : Op S Unit)
 (doublePanic : Panic → Panic → Op S Unit) : Op S Unit :=
 allocationDrop (scope backtrace message doublePanic) deallocate doublePanic


theorem lazy_incomplete_drops_closure (f v : Op S Unit) :
 lazyDrop .incomplete f v = f := rfl
#print axioms lazy_incomplete_drops_closure

theorem lazy_complete_drops_value (f v : Op S Unit) :
 lazyDrop .complete f v = v := rfl
#print axioms lazy_complete_drops_value

theorem lazy_poisoned_no_field (f v : Op S Unit) :
 lazyDrop .poisoned f v = pure () := rfl
#print axioms lazy_poisoned_no_field

theorem box_zero_layout (free : Op S Unit) : boxDeallocate 0 free = pure () := by
 simp [boxDeallocate]
#print axioms box_zero_layout

theorem box_nonzero_layout (n : Nat) (free : Op S Unit) :
 boxDeallocate (n+1) free = free := by simp [boxDeallocate]
#print axioms box_nonzero_layout

theorem allocation_drop_aborts (payload free : Op S Unit)
 (dp : Panic → Panic → Op S Unit) (s t : S) (es : List Event) (c : Crash)
 (h : payload s = ⟨es,t,.abort c⟩) :
 allocationDrop payload free dp s = ⟨es,t,.abort c⟩ :=
 scope_abort_no_cleanup es s t c payload free dp h
#print axioms allocation_drop_aborts

theorem allocation_drop_panic_frees (payload free : Op S Unit)
 (dp : Panic → Panic → Op S Unit) (s t : S) (es : List Event) (p : Panic)
 (h : payload s = ⟨es,t,.panic p⟩) :
 allocationDrop payload free dp s = prepend es (unwind p free dp t) :=
 scope_panic es s t p payload free dp h
#print axioms allocation_drop_panic_frees

theorem error_fields_normal_order (b m free : Op S Unit)
 (dp : Panic → Panic → Op S Unit) (s t u v : S) (bs ms fs : List Event)
 (hb : b s = ⟨bs,t,.value ()⟩) (hm : m t = ⟨ms,u,.value ()⟩)
 (hf : free u = ⟨fs,v,.value ()⟩) :
 errorObjectDrop b m free dp s = ⟨bs++ms++fs,v,.value ()⟩ := by
 unfold errorObjectDrop allocationDrop
 have fields := normal_drop_order () s t u bs ms b m dp hb hm
 exact normal_drop_order () s u v (bs++ms) fs (scope b m dp) free dp fields hf
#print axioms error_fields_normal_order
end PV_DIAG3
