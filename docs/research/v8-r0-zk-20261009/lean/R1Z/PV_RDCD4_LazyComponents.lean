import R1Z.PV_RDCD4_FieldSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_LazyComponents
open Aeneas Aeneas.Std Result
abbrev M := ProverRwFull.aspis_core.field.M31
abbrev C := ProverRwFull.aspis_core.field.CM31
abbrev Q := ProverRwFull.aspis_core.field.QM31
namespace F
abbrev add := PV_RDCD4_FieldSource.aspis_core.field.M31.add
abbrev cadd := PV_RDCD4_FieldSource.aspis_core.field.CM31.add
end F
/-- Exact construction order, including every Result-returning scalar addition. -/
def components (q : Q) : Result (List (List M)) := do
  let sum ← F.cadd q.c0 q.c1
  let c0 ← F.add q.c0.a q.c0.b
  let c1 ← F.add q.c1.a q.c1.b
  let c2 ← F.add sum.a sum.b
  ok [[q.c0.a,q.c0.b,c0],[q.c1.a,q.c1.b,c1],[sum.a,sum.b,c2]]

theorem shape (q : Q) :
    components q = (do
      let sum ← F.cadd q.c0 q.c1
      let c0 ← F.add q.c0.a q.c0.b
      let c1 ← F.add q.c1.a q.c1.b
      let c2 ← F.add sum.a sum.b
      ok [[q.c0.a,q.c0.b,c0],[q.c1.a,q.c1.b,c1],[sum.a,sum.b,c2]]) := rfl
#print axioms shape
end R1Z.PV_RDCD4_LazyComponents
