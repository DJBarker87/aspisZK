import NJQ_Identity
import NJQ_Carrier
set_option autoImplicit false
noncomputable section
namespace NJY_Identity
open Aeneas Aeneas.Std Result
/-- ReviewedTranscription NJY-RT149: NJQ's hand reference, reused verbatim.
Native full-Result association is NJQ K006/K007, width guard K019/K020.
This definition is a reference, not an emitted frozen body. -/
abbrev reference := NJQ_Identity.reference
abbrev model := NJQ_Identity.model
/-- Every slice, including all rejection arms; no successful endpoint premise. -/
theorem source (b : Slice U8) : reference b = model b := NJQ_Identity.source b
/-- The carrier transport is reversible on complete Results. -/
theorem result_roundtrip
 (r : core.result.Result NJQ_Carrier.I NJI_PolicyPort.F) :
 NJQ_Carrier.from_identity_result (NJQ_Carrier.identity_result r) = r := by
 exact NJQ_Carrier.identity_result_roundtrip r
set_option pp.proofs false in
#print source
#print axioms source
set_option pp.proofs false in
#print result_roundtrip
#print axioms result_roundtrip
end NJY_Identity
