import R1Z.PV_CBL_JoinAdapter
import R1Z.PV_CBL_AppendBundle
import R1Z.PV_CBL_DigestSoftSource
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_CallbackBundle
set_option autoImplicit false
/-- Additive publication of the existing seven-law dictionary; all older names persist. -/
abbrev AppendTypes := PV_CBL_AppendBundle.Types
abbrev selectedAppend := PV_CBL_AppendBundle.selected
abbrev op25_source_append := PV_CBL_AppendBundle.op25_source
abbrev op28_source_append := PV_CBL_AppendBundle.op28_source
abbrev op29_source_append := PV_CBL_AppendBundle.op29_source
abbrev op30_source_append := PV_CBL_AppendBundle.op30_source
abbrev op31_source_append := PV_CBL_AppendBundle.op31_source
abbrev op34_source_append := @PV_CBL_AppendBundle.op34_source
abbrev op35_source_append := PV_CBL_AppendBundle.op35_source
/-- These proof-valued aliases publish the exact extracted owned soft reference.
They do not instantiate the native generic SHA callbacks or runtime dispatcher. -/
abbrev soft_padding_source := PV_CBL_PadArraySource.source
abbrev soft_compress_source := PV_CBL_SoftByteExtracted.source
abbrev soft_update_source := PV_CBL_DigestUpdateSource.source
abbrev soft_finalize_source := PV_CBL_FinalizeSoftSource.source
abbrev soft_digest_source := PV_CBL_DigestSoftSource.source
open ProverRwFull
/-- P6 value dictionary: bounded native association is recorded separately. -/
@[reducible] def selectedJoin (base : ExternalTypes)
    (ops : @ExternalFuns (AppendTypes base)) : @ExternalFuns (AppendTypes base) :=
  letI : ExternalTypes := AppendTypes base
  {selectedAppend base ops with op26 := fun {P} inst p q => do
    let path ← inst.as_ref q
    PV_CBL_JoinAdapter.reference p path}
theorem op26_source (base : ExternalTypes) (ops : @ExternalFuns (AppendTypes base))
    {P : Type} (inst : core.convert.AsRef P String) (p : String) (q : P) :
    @ExternalFuns.op26 (AppendTypes base) (selectedJoin base ops) P inst p q =
      (do let path ← inst.as_ref q
          PV_CBL_JoinAdapter.reference p path) := rfl
#print axioms selectedJoin
#print axioms op26_source
#print axioms AppendTypes
#print axioms selectedAppend
#print axioms op25_source_append
#print axioms op28_source_append
#print axioms op29_source_append
#print axioms op30_source_append
#print axioms op31_source_append
#print axioms op34_source_append
#print axioms op35_source_append
#print axioms soft_padding_source
#print axioms soft_compress_source
#print axioms soft_update_source
#print axioms soft_finalize_source
#print axioms soft_digest_source
end R1Z.PV_CBL_CallbackBundle
