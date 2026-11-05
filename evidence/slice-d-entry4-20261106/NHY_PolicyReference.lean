import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
namespace NHY_PolicyReference
def policy_ref
  (flags : Std.U8) (program_zero : Bool) (authority_zero : Bool)
  (binding_zero : Bool) :
  Result Std.U8
  := do
  let i ← lift (~~~ 3#u8)
  let i1 ← lift (flags &&& i)
  if i1 != 0#u8
  then ok 1#u8
  else
    if program_zero
    then ok 2#u8
    else
      if binding_zero
      then ok 2#u8
      else
        let i2 ← lift (flags &&& 1#u8)
        let i3 ← lift (flags &&& 2#u8)
        if i3 != 0#u8
        then
          if i2 != 0#u8
          then if true != authority_zero
               then ok 3#u8
               else ok 0#u8
          else ok 3#u8
        else if (i2 != 0#u8) != authority_zero
             then ok 3#u8
             else ok 0#u8

#print axioms policy_ref
end NHY_PolicyReference
