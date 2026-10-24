import S9ActualEbyKFinishWordsCanonicalV1
import S9ActualPairWideCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualEbyKFinishCanonicalV1
open AspisR1S9ProductionPairCutV1
/-- Any successful actual native finish has exactly the canonical predicate
already used by the native Pair arithmetic/helper pipeline. Arbitrary state,
without a bounded-history or independently assumed output contract. -/
theorem actual_finish_success_canonical (self : fast_pairing.EbyKDot)
    (out : aspis_core.field.wide_exact.WideExact)
    (h : fast_pairing.EbyKDot.finish self = .ok out) :
    AspisR1S9ActualPairWideCanonicalV1.Canonical out := by
  change AspisR1S9ActualEbyKFinishWordsCanonicalV1.CanonicalWords out
  exact AspisR1S9ActualEbyKFinishWordsCanonicalV1.actual_finish_success_words_canonical self out h
#print axioms actual_finish_success_canonical
end AspisR1S9ActualEbyKFinishCanonicalV1
