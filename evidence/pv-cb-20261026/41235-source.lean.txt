import R1Z.PV_CB_PartialForward
import R1Z.PV_CB_CanonicalUpdate
set_option autoImplicit false
namespace R1Z.PV_CB_PartialArrayUpdate
open Aeneas Aeneas.Std Result

/-- Exact partial update invariant: an out-of-bounds error remains an error. -/
theorem update {A : Type} {N : Usize} (valid : A → Prop) (values : Array A N)
    (vv : PV_CB_CanonicalArrays.Valid valid values) (index : Usize) (value : A)
    (hv : valid value) :
    PV_CB_PartialForward.Post (PV_CB_CanonicalArrays.Valid valid) (Array.update values index value) := by
  intro out h
  unfold Array.update at h
  cases read : values[index]? with
  | none => rw [read] at h; cases h
  | some old =>
    rw [read] at h
    cases h
    exact PV_CB_CanonicalUpdate.list_set valid values.val index.val value vv hv
#print axioms update
end R1Z.PV_CB_PartialArrayUpdate
