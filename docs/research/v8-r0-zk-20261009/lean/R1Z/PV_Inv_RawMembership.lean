import R1Z.PV_Inv_RawRun
set_option autoImplicit false
namespace R1Z.PV_Inv_RawMembership
open PV_Inv_RawSlots PV_Inv_RawRun
variable {V W : Type} [Zero W] [DecidableEq W]

theorem reached_origin (es : List (Entry V W)) (z : V) (t : Slots V W)
    (hr : run (empty z) es = some t) (i : Fin 2) (active : (t i).weight ≠ 0) :
    ∃ e ∈ es, e.value = (t i).value := by
  have h := preserves (fun v => ∃ e ∈ es, e.value=v) es (empty z) t
    (empty_good _ z) (fun e he => ⟨e,he,rfl⟩) hr
  exact h i active

#print axioms reached_origin
end R1Z.PV_Inv_RawMembership
