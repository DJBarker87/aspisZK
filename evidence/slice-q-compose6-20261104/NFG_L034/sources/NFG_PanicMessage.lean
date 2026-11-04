import Aeneas.Std
set_option autoImplicit false
namespace NFG_PanicMessage
open Aeneas Aeneas.Std
def value : Str := ⟨[99#u8,97#u8,110#u8,110#u8,111#u8,116#u8,32#u8,105#u8,110#u8,118#u8,101#u8,114#u8,116#u8,32#u8,122#u8,101#u8,114#u8,111#u8,32#u8,105#u8,110#u8,32#u8,81#u8,77#u8,51#u8,49#u8], by simp; scalar_tac⟩
theorem bytes : value.val.map UScalar.val = [99, 97, 110, 110, 111, 116, 32, 105, 110, 118, 101, 114, 116, 32, 122, 101, 114, 111, 32, 105, 110, 32, 81, 77, 51, 49] := rfl
#print axioms bytes
end NFG_PanicMessage
