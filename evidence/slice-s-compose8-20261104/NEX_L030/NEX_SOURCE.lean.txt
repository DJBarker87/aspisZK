import NED_SubtreeComposition
set_option autoImplicit false
noncomputable section
namespace NEX_InnerLaws
open Aeneas Aeneas.Std Result
/-- Explicit discharge of the inherited universal DigestDecodeAll name.
This is a checked reuse of the existing law, not a new source assumption. -/
theorem digest_decode_all : NBN_AfterDecodeTypes.NBN_Dep_DigestDecode
    (fun b => ok (NBP_DigestDecode.decoded b)) := NED_SubtreeComposition.digest_decode
#print axioms digest_decode_all
end NEX_InnerLaws
