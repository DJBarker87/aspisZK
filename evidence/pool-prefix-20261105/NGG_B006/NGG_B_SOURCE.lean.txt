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
  simp [NGG_Ref.supported_loader, loaders, NFV_RequestGuards.array]
#print axioms result
end NGG_Loader
