import PV_B3_PolynomialFinite
namespace PV_B3_PolynomialFidelity
open Aeneas Aeneas.Std Result PV_B3_Copy_117
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
 def values (q : Q) : List Nat := [q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val]
 def canonical_case : Result (List Nat) := do
  let q ← PV_B3_PolynomialFinite.reference
    (Array.repeat 28#usize aspis_core.field.QM31.ONE) aspis_core.field.QM31.ONE
  ok (values q)
 def raw_case : Result (List Nat) := do
  let p ← Array.update (Array.repeat 28#usize aspis_core.field.QM31.ZERO) 2#usize aspis_core.field.QM31.ONE
  let q ← PV_B3_PolynomialFinite.reference p
    {c0 := {a := 0#u32,b := 2147483648#u32},c1 := {a := 0#u32,b := 0#u32}}
  ok (values q)
#eval canonical_case
#eval raw_case
#print axioms canonical_case
#print axioms raw_case
end PV_B3_PolynomialFidelity
