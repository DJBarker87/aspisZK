import R1Z.BuilderForestAdmissionPort
import R1Z.BuilderPoseidonExtracted

/-! Executable pure callback from the already extracted owned external layer.
The dictionary is explicit, with no global instance and no effect assumption.
Its source association is the separate Kani leaf, not a Lean equality axiom. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ExternalReference
open Aeneas Aeneas.Std Result
abbrev run := AspisBuilderPoseidonReference.poseidon2.builder_reference.external_owned
abbrev dictionary : BuilderForestAdmissionPort.ExternalLinear := ⟨run⟩

theorem call_eq (state : Array U32 16#usize) :
    @BuilderForestAdmissionPort.poseidon2.external_linear_lazy dictionary state = run state := rfl

#print axioms call_eq
end R1Z.PV_Src_ExternalReference
