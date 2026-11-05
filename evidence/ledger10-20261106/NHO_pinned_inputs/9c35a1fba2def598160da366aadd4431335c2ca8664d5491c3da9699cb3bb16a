import NGG_Ref.Funs
import NFV_RequestGuards
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGG_Loader
abbrev Key := Array U8 32#usize
def loaders (a b c : Key) : Array Key 3#usize := ⟨[a,b,c],by simp⟩
theorem result (owner a b c : Key) :
    NGG_Ref.supported_loader owner (loaders a b c) =
      ok (decide (owner.val = a.val ∨ owner.val = b.val ∨ owner.val = c.val)) := by
  have h0 : Array.index_usize (loaders a b c) 0#usize = ok a := by rfl
  have h1 : Array.index_usize (loaders a b c) 1#usize = ok b := by rfl
  have h2 : Array.index_usize (loaders a b c) 2#usize = ok c := by rfl
  simp only [NGG_Ref.supported_loader,h0,h1,h2,bind_tc_ok,NFV_RequestGuards.array]
  by_cases ha : owner.val = a.val <;> by_cases hb : owner.val = b.val <;>
    by_cases hc : owner.val = c.val <;> simp [ha,hb,hc]
#print axioms result
end NGG_Loader
