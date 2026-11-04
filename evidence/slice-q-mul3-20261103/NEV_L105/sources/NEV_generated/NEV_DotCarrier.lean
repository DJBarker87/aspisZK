import FIo_NativeTypes
set_option autoImplicit false
namespace NEV_DotCarrier
open Aeneas Aeneas.Std
abbrev NC := FIo_Native.aspis_core.field.CM31
abbrev NQ := FIo_Native.aspis_core.field.QM31
abbrev NE := FIo_Native.aspis_core.field.wide_exact.WideExact
-- Exact coordinate predicates, with no unrelated decoder/fixture imports.
def canonC (x : NC) : Prop := x.a.val<2147483647 ∧ x.b.val<2147483647
def canonQ (x : NQ) : Prop := canonC x.c0 ∧ canonC x.c1
def canonE (x : NE) : Prop := canonQ x.c0 ∧ canonQ x.c1
end NEV_DotCarrier
