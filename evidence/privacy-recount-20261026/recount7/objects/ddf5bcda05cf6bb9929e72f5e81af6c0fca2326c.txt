import R1Z.PV_Src_ExternalReference

/-! Concrete external-layer extraction dictionary. The shipped/reference
association is the unstubbed all-word Kani gate in
`evidence/pv-runjoin12-20261027/pv12-runjoin-kani-11`; that association is P6,
not a Lean theorem. The theorem below is the nominal extraction adapter only.
No source execution trace or side-channel equality is asserted. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ShippedExternal
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort

abbrev E_shipped : ExternalLinear := PV_Src_ExternalReference.dictionary

theorem call_eq_extraction (state : Array U32 16#usize) :
    @poseidon2.external_linear_lazy E_shipped state =
      AspisBuilderPoseidonReference.poseidon2.builder_reference.external_owned state := rfl

#print axioms E_shipped
#print axioms call_eq_extraction
end R1Z.PV_RunJoin_ShippedExternal
