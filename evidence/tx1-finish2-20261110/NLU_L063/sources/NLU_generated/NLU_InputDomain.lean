import NLU_TerminalDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Own-argument provenance of the prefix, recorded as a caller137 clause.
The witness is an original parser input, not a child Result hypothesis. -/
def ParsedPrefix (prefix : r1_wire.Prefix) : Prop :=
 ∃ (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix),
 AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre) ∧
 prefix=PrefixAdapter.fromOld pre
/-- Proposed caller-facing domain. Every field is on verify_finish's OWN
arguments; all internal claims/alpha/record/circle/mask domains are excluded
and must be derived by this parent's fold. Not yet a reviewed136 root domain. -/
structure InputDomain {H : Type} (i : Input H) : Prop where
 prefix : ParsedPrefix i.prefix1
 terminal : NLU_Terminal.InputDomain i.publicValue i.challenges
 eta : JFv_RoundArithmetic.Canonical i.challenges.eta
/-- Exact original parser arguments may be recovered only from own provenance.
No independent prefix value is selected to match an output. -/
theorem parsed_of_domain {H : Type} (i : Input H) (h : InputDomain i) :
 ∃ (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix),
 AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre) ∧
 i.prefix1=PrefixAdapter.fromOld pre := h.prefix
#print axioms parsed_of_domain
#print InputDomain
end AspisR1.NLU
end
