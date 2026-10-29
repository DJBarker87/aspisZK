import R1Z.PV_RDB2E_FallbackRoundShape

section
-- Unchanged source component R1Z.PV_CBL_FallbackRoundTotal
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackRoundTotal
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar
set_option autoImplicit false
/-- Reconstruct every four-word input by symbolic indexes, with no finite enumeration. -/
theorem pack_eta (a : A4) :
    pack a.val[0]! a.val[1]! a.val[2]! a.val[3]! = a := by
  apply Subtype.ext
  have h : a.val.length=4 := a.property
  match a with
  | ⟨[],h⟩ => simp at h
  | ⟨[_],h⟩ => simp at h
  | ⟨[_,_],h⟩ => simp at h
  | ⟨[_,_,_],h⟩ => simp at h
  | ⟨[_,_,_,_],h⟩ => rfl
  | ⟨_::_::_::_::_::_,h⟩ => simp at h
#print axioms pack_eta
end R1Z.PV_CBL_FallbackRoundTotal

end
