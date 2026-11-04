import NGG_Ref.Types
open Aeneas Aeneas.Std Result
namespace NGG_Ref
/-- Total option elimination; no external hypothesis. -/
def core.option.Option.ok_or {T E : Type} (x : Option T) (err : E) :
    Result (Aeneas.Std.core.result.Result T E) :=
  ok (match x with | none => .Err err | some value => .Ok value)
end NGG_Ref
