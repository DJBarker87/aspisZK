import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RDCD4_Copy194
open Aeneas Aeneas.Std Result
/-- Source copy_from_slice_impl checks lengths before its sole memory write.
The actual argument-confined copy intrinsic remains at V370. -/
def implementation {T : Type} (dst src : List T) : Result (List T) :=
  if dst.length ≠ src.length then fail .panic else ok src

def wrapper {T : Type} (dst src : List T) : Result (List T) := implementation dst src

def model {T : Type} (dst src : List T) : Result (List T) :=
  if dst.length=src.length then ok src else fail .panic

theorem binding {T : Type} (dst src : List T) : wrapper dst src=model dst src := by
  by_cases h : dst.length=src.length <;> simp only [wrapper,implementation,model,h,not_true_eq_false,not_false_eq_true,if_true,if_false]

theorem success {T : Type} (dst src : List T) (h : dst.length=src.length) :
    wrapper dst src=ok src := by rw [binding,model,if_pos h]

theorem mismatch {T : Type} (dst src : List T) (h : dst.length≠src.length) :
    wrapper dst src=fail .panic := by rw [binding,model,if_neg h]

theorem source_frame {T : Type} (dst src : List T) (h : dst.length=src.length) :
    (do let out ← wrapper dst src;ok (out,src))=ok (src,src) := by
  rw [success dst src h,bind_tc_ok]
#print axioms binding
#print axioms success
#print axioms mismatch
#print axioms source_frame
end R1Z.PV_RDCD4_Copy194
