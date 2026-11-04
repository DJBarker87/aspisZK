import NGG_SpineRef.Funs
import NGG_Scalar
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGG_LayoutValue
open NGG_SpineRef
def cursor (rollover : Bool) : Usize := if rollover then 5#usize else 4#usize
def expected (rollover withdrawal : Bool) : Usize :=
  if rollover then if withdrawal then 18#usize else 13#usize
  else if withdrawal then 17#usize else 12#usize
def fields (rollover withdrawal : Bool) : Layout :=
  if rollover then
    ⟨5#usize,6#usize,7#usize,8#usize,10#usize,11#usize,
      (if withdrawal then 17#usize else 12#usize),12#usize⟩
  else ⟨4#usize,5#usize,6#usize,7#usize,9#usize,10#usize,
      (if withdrawal then 16#usize else 11#usize),11#usize⟩
def value (rollover withdrawal : Bool) (n : Usize)
    (unique : core.result.Result Unit NGGSpineError) : core.result.Result Layout NGGSpineError :=
  if n != expected rollover withdrawal then
    if n < expected rollover withdrawal then .Err .NotEnoughAccountKeys else .Err .InvalidArgument
  else match unique with | .Err e => .Err e | .Ok _ => .Ok (fields rollover withdrawal)

end NGG_LayoutValue
