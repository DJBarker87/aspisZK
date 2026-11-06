import NJQ_EntryTotal
set_option autoImplicit false
noncomputable section
namespace NJY_Entry
open Aeneas Aeneas.Std Result NJI_V1Carrier
/-- NJY-RT201: exact width/header, status rejection/complete constructor,
CLOSED validator206, and full suffix. No child Result is left free. -/
abbrev Cut := NJQ_EntryTotal.Cut
abbrev reference := NJQ_Entry.reference
abbrev model := NJQ_Entry.model
/-- Native (ay) segment certificates remain separately required. -/
theorem source (b : Slice U8) (log : Option E) (out : core.result.Result E F)
 (cut : Cut b log out) : ok out=reference b :=
 NJQ_EntryTotal.native_source b log out cut
set_option pp.proofs false in
#print source
#print axioms source
end NJY_Entry
