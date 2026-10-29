import R1Z.PV_RDB2E_FallbackArray8
import R1Z.PV_RDB2E_FallbackScalar

section
-- Unchanged source component R1Z.PV_CBL_FallbackStateCodec
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackStateCodec
open PV_CBL_FallbackScalar
set_option autoImplicit false
def encode (s : State) : Array U32 8#usize :=
  PV_CBL_FallbackArray8.pack s.a s.b s.c s.d s.e s.f s.g s.h
def decode (v : Array U32 8#usize) : State :=
  ⟨v.val[0]!,v.val[1]!,v.val[2]!,v.val[3]!,v.val[4]!,v.val[5]!,v.val[6]!,v.val[7]!⟩
theorem decode_encode (s : State) : decode (encode s)=s := by cases s; rfl
theorem encode_decode (v : Array U32 8#usize) : encode (decode v)=v := by
  apply Subtype.ext
  match v with
  | ⟨[],h⟩ => simp at h
  | ⟨[_],h⟩ => simp at h
  | ⟨[_,_],h⟩ => simp at h
  | ⟨[_,_,_],h⟩ => simp at h
  | ⟨[_,_,_,_],h⟩ => simp at h
  | ⟨[_,_,_,_,_],h⟩ => simp at h
  | ⟨[_,_,_,_,_,_],h⟩ => simp at h
  | ⟨[_,_,_,_,_,_,_],h⟩ => simp at h
  | ⟨[_,_,_,_,_,_,_,_],h⟩ => rfl
  | ⟨_::_::_::_::_::_::_::_::_::_,h⟩ => simp at h
#print axioms encode
#print axioms decode
#print axioms decode_encode
#print axioms encode_decode
end R1Z.PV_CBL_FallbackStateCodec

end
