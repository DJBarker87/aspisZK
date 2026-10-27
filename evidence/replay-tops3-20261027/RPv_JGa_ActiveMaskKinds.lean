import RPu_FIq_Native13
set_option autoImplicit false
namespace AspisR1.JGa_ActiveMaskKinds
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
def Kind (mask : U16) := mask=6144#u16 ∨ mask=6145#u16 ∨ mask=4097#u16 ∨ mask=2048#u16 ∨ mask=2049#u16 ∨ mask=1749#u16 ∨ mask=26214#u16
theorem all (mask : U16) (hm : mask∈constants.ACTIVE_ROW_MASKS.val) : Kind mask := by
  simp only [constants.ACTIVE_ROW_MASKS,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [Kind]
#print axioms all
end AspisR1.JGa_ActiveMaskKinds
