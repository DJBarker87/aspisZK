import R1Z.PV_Inv_GlobalSafety
import R1Z.PV_Inv_RawInvoke
set_option autoImplicit false
namespace R1Z.PV_Inv_GlobalOrigin
open PV_Inv_RawSlots PV_Inv_GlobalSlots PV_Inv_GlobalSafety
variable {I V W : Type} [DecidableEq I] [Zero W] [DecidableEq W]

theorem origin (z : V) (es : List (I × Entry V W)) (s : State I V W)
    (hr : PV_Inv_GlobalSlots.run (empty z) es=some s) (key : I) (v : V)
    (hv : v ∈ PV_Inv_RawInvoke.reached (s key)) :
    ∃ e ∈ es, e.1=key ∧ e.2.value=v := by
  have h := run_good (fun k v => ∃ e ∈ es, e.1=k ∧ e.2.value=v) (empty z) s es
    (empty_good z _) (fun e he => ⟨e,he,rfl,rfl⟩) hr
  exact PV_Inv_RawInvoke.reached_good _ (s key) (h key) v hv

#print axioms origin
end R1Z.PV_Inv_GlobalOrigin
