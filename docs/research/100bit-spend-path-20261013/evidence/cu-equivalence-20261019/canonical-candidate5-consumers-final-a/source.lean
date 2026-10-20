import CuSavingsCanonicalVectorContexts
import CuSavingsCanonicalFieldStream
import CuSavingsCanonicalDotPartialsCanonical
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalCandidate5Consumers
open Aeneas Aeneas.Std Result AspisR1CanonicalDots
abbrev K := field.QM31
variable [Shared]

/-- Source-decoded field-stream replacement in any unchanged functional continuation. -/
theorem plain_pair_context {R : Type} (f : Slice U8) (scratch : Slice K) (n : Usize)
    (after : Result (core.result.Result field.wide_exact.WideExact verifier.Error) → R) :
    after (new_stream.field_stream f scratch n)=after (old_stream.field_stream f scratch n) := by
  rw [CuSavingsCanonicalFieldStream.source_equivalence]

/-- Source enumerate/final-dot replacement in any unchanged final relation continuation. -/
theorem final_relation_context {R : Type} (f : Slice U8) (weights : Slice K)
    (after : Result (core.result.Result field.wide_exact.WideExact verifier.Error) → R) :
    after (new_clients.final_stream f weights)=after (old_clients.final_stream f weights) := by
  rw [CuSavingsCanonicalDotClients.final_equivalence]

#print axioms plain_pair_context
#print axioms final_relation_context
#print axioms CuSavingsCanonicalVectorContexts.six_point_claim_context
#print axioms CuSavingsCanonicalVectorContexts.four_slot_tail_context
#print axioms CuSavingsCanonicalDotPartialsCanonical.caller_context
end AspisR1.CuSavingsCanonicalCandidate5Consumers
