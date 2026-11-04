import NGO_PrefixWidePort
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_PrefixHighPort
open NGO_PrefixWidePort
def nonzero (q : WireQ) : Bool :=
  decide (q.c0.a.val≠0 ∨ q.c0.b.val≠0 ∨ q.c1.a.val≠0 ∨ q.c1.b.val≠0)
/-- Exact high-half rejection flag on every raw carrier. -/
theorem ne (q : WireQ) :
    core.cmp.PartialEq.ne.trait_default
      AspisR1PrefixAggregateParser.field.QM31.Insts.CoreCmpPartialEqQM31 q
        AspisR1PrefixAggregateParser.field.QM31.ZERO=ok (nonzero q) := by
  simp [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    AspisR1PrefixAggregateParser.field.QM31.Insts.CoreCmpPartialEqQM31,
    AspisR1PrefixAggregateParser.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    AspisR1PrefixAggregateParser.field.CM31.Insts.CoreCmpPartialEqCM31,
    AspisR1PrefixAggregateParser.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
    AspisR1PrefixAggregateParser.field.QM31.ZERO,nonzero]
#print axioms ne
end NGO_PrefixHighPort
