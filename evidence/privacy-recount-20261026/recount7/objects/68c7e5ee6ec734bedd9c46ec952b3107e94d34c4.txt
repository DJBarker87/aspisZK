import PV_B3_Mask117Finite
namespace PV_B3_Mask117Fidelity
open Aeneas Aeneas.Std Result PV_B3_Copy_117
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
 def values (q : Q) : List Nat := [q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val]
 def result (point_value : Q) : Result (List Nat) := do
  let q ← PV_B3_Mask117Finite.reference
    (Array.repeat 16#usize aspis_core.field.QM31.ONE)
    (Array.repeat 10#usize aspis_core.field.QM31.ONE)
    aspis_core.field.QM31.ONE (Array.repeat 10#usize point_value)
  ok (values q)
#eval result aspis_core.field.QM31.ONE
#eval result {c0 := {a := 0#u32,b := 2147483648#u32},c1 := {a := 0#u32,b := 0#u32}}
#print axioms result
end PV_B3_Mask117Fidelity
