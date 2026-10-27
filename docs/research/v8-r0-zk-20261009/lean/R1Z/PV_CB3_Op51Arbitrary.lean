import R1Z.PV_CB3_Op51Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_Op51Arbitrary
open Aeneas Aeneas.Std Result ProverRwFull
/-- The P6 harness constructs these fields directly, including noncanonical words. -/
def carrier (a b c d e f g h : Std.U32) : aspis_core.field.wide_exact.WideExact :=
  { c0 := {c0 := {a := a, b := b}, c1 := {a := c, b := d}},
    c1 := {c0 := {a := e, b := f}, c1 := {a := g, b := h}} }
theorem carrier_complete (x : aspis_core.field.wide_exact.WideExact) :
    carrier x.c0.c0.a x.c0.c0.b x.c0.c1.a x.c0.c1.b
      x.c1.c0.a x.c1.c0.b x.c1.c1.a x.c1.c1.b = x := rfl
variable [ExternalTypes]
/-- Complete extracted Result at every carrier; native P6 gate is all_carriers. -/
theorem op51_source (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (PV_CB3_Op51Source.selected ops).op51 x = PV_CB3_Op51Source.Raw.wide_bytes_flat x :=
  PV_CB3_Op51Source.op51_source ops x
#print axioms carrier_complete
#print axioms op51_source
end R1Z.PV_CB3_Op51Arbitrary
