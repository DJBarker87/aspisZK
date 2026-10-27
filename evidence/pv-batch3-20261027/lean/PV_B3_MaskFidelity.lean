import PV_B3_MaskFinite
namespace PV_B3_MaskFidelity
open Aeneas Aeneas.Std Result
open PV_B3_Forest_134
set_option autoImplicit false
-- Executable differential only, never kernel evaluation as a theorem proof.
-- MaskFinite supplies the symbolic rank/fuel factoring first.
def mask_values : Result (List Nat) := do
  let r ← PV_B3_MaskFinite.reference
  match r with
  | .Ok xs => ok (xs.val.map (fun x => x.val))
  | .Err _ => fail .panic
#eval mask_values
#print axioms mask_values
end PV_B3_MaskFidelity
