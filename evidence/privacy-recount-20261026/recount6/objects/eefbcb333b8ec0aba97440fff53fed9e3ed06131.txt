import R1Z.PV_CBL_FallbackArray4
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_BlockArrayEta
open PV_CBL_FallbackArray4
set_option autoImplicit false
theorem eta (v : A4) : pack v.val[0]! v.val[1]! v.val[2]! v.val[3]! = v := by
  apply Subtype.ext
  match v with
  | ⟨[],h⟩ => simp at h
  | ⟨[_],h⟩ => simp at h
  | ⟨[_,_],h⟩ => simp at h
  | ⟨[_,_,_],h⟩ => simp at h
  | ⟨[_,_,_,_],h⟩ => rfl
  | ⟨_::_::_::_::_::_,h⟩ => simp at h
#print axioms eta
end R1Z.PV_CBL_BlockArrayEta
