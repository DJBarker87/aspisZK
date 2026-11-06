import NJQ_RegistryTotal
set_option autoImplicit false
noncomputable section
namespace NJY_Registry
open Aeneas Aeneas.Std Result NJI_V1Carrier
/-- NJY-RT203: exact width/header, complete constructor, CLOSED validator208,
and full suffix segments. Cut's child Result is instantiated internally. -/
abbrev Cut := NJQ_RegistryTotal.Cut
abbrev reference := NJQ_Registry.reference
abbrev model := NJQ_Registry.model
/-- Source-ordered frame composition reused from NJQ; native admission is a
separate (ay) segment packet, never inferred just from this theorem. -/
theorem source (b : Slice U8) (log : Option R) (out : core.result.Result R F)
 (cut : Cut b log out) : ok out=reference b :=
 NJQ_RegistryTotal.native_source b log out cut
set_option pp.proofs false in
#print source
#print axioms source
end NJY_Registry
