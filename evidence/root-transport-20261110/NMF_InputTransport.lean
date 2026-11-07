import NLW_ByteIdentity
import NLP_InputDomain
set_option autoImplicit false
noncomputable section
namespace NMF_InputTransport
open Aeneas Aeneas.Std AspisR1
/-- The literal callee predicate, transported through byte equality only. -/
theorem root0 (saved ck oldProof proof : Slice U8)
 (old : NLP_InputDomain.Root0 saved oldProof)
 (checkpoint : MultiproofConeCanonical.bytesOf ck.val=MultiproofConeCanonical.bytesOf saved.val)
 (inputs : MultiproofConeCanonical.bytesOf proof.val=MultiproofConeCanonical.bytesOf oldProof.val) :
 NLP_InputDomain.Root0 ck proof := by
 have hc:=NLW_ByteIdentity.bytes_injective _ _ checkpoint
 have hp:=NLW_ByteIdentity.bytes_injective _ _ inputs
 simpa only [NLP_InputDomain.Root0,hc,hp] using old
/-- Exact definitional identity with the caller's existing spelling. -/
theorem caller_clause (ck proof : Slice U8) :
 NLP_InputDomain.Root0 ck proof ↔ NLW_Root0.Binds ck proof := Iff.rfl
#print root0
#print caller_clause
#print axioms root0
#print axioms caller_clause
end NMF_InputTransport
