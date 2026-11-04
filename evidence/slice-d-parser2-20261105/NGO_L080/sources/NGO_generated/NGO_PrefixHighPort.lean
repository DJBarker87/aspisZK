import NGO_PrefixWidePort
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_PrefixHighPort
open NGO_PrefixWidePort
/-- Raw-coordinate comparison is preserved on every full carrier, even when
its words are noncanonical. No field arithmetic or success premise appears. -/
theorem ne (q : WireQ) :
    core.cmp.PartialEq.ne.trait_default
      AspisR1PrefixAggregateParser.field.QM31.Insts.CoreCmpPartialEqQM31 q
        AspisR1PrefixAggregateParser.field.QM31.ZERO =
    core.cmp.PartialEq.ne.trait_default
      AspisR1CandidateParser.field.QM31.Insts.CoreCmpPartialEqQM31 (toQ q)
        AspisR1CandidateParser.field.QM31.ZERO := by
  rfl
#print axioms ne
end NGO_PrefixHighPort
