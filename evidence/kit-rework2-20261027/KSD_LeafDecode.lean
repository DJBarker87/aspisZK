import LPn_DotClosed
import LPo_Boundary
import LPo_View
namespace KSD_LeafSelection
abbrev decode_k := r1_wire.ValidatedRecord.decode_k
abbrev claims := r1_semantic.claims
abbrev claims_owned := LPn.Claims.owned
abbrev semantic_boundary := r1_semantic.semantic_boundary
abbrev wide_view := verifier.candidate.wide_view
abbrev dot_push := fast_pairing.canonical.Dot.push
#print axioms LPn.Dot.native_result
#print axioms LPn.Claims.accepted_to_cohort
#print axioms LPo.Boundary.decoded_exact
#print axioms LPo.View.model_product
end KSD_LeafSelection
