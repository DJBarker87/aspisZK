import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
namespace NHY_RegistryReference
def flag_ref (v : Std.U8) (mask : Std.U8) : Result Bool := do
  let i ← lift (v &&& mask)
  ok (i != 0#u8)

def retirement_ref (v : Std.U64) : Result Bool := do
  ok (v = core.num.U64.MAX)

def status_ref (v : Std.U8) : Result (Option Std.U8) := do
  match v with
  | 0#uscalar => ok (some 0#u8)
  | 1#uscalar => ok (some 1#u8)
  | 2#uscalar => ok (some 2#u8)
  | 3#uscalar => ok (some 3#u8)
  | _ => ok none
#print axioms flag_ref
#print axioms retirement_ref
#print axioms status_ref
end NHY_RegistryReference
