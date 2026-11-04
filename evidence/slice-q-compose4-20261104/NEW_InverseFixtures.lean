import NEW_InverseAssociation
open Aeneas Aeneas.Std Result
namespace NEW_InverseFixtures
def packed (x : U32) : Lean.Json :=
 match NEW_InverseActual.aspis_core.field.M31.inv x with
 | .ok value => Lean.toJson value.val
 | .fail .assertionFailure => .str "assertionFailure"
 | .fail _ => .str "other-failure"
 | .div => .str "div"
def fixtures : List (String × Lean.Json) := [
 ("0",packed 0#u32),
 ("1",packed 1#u32),
 ("2",packed 2#u32),
 ("3",packed 3#u32),
 ("2147483646",packed 2147483646#u32),
 ("2147483647",packed 2147483647#u32),
 ("2147483648",packed 2147483648#u32),
 ("4294967295",packed 4294967295#u32),
 ("17",packed 17#u32),
 ("123456789",packed 123456789#u32),
 ("3735928559",packed 3735928559#u32)
]
#eval (Lean.Json.mkObj fixtures).compress
end NEW_InverseFixtures
