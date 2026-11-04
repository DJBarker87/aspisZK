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
  have equal (a b : U32) : (a=b) ↔ (a.val=b.val) :=
    ⟨fun h=>congrArg UScalar.val h,UScalar.eq_of_val_eq⟩
  by_cases h0 : q.c0.a.val=0 <;> by_cases h1 : q.c0.b.val=0 <;>
    by_cases h2 : q.c1.a.val=0 <;> by_cases h3 : q.c1.b.val=0
  all_goals simp [equal,h0,h1,h2,h3,core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    AspisR1PrefixAggregateParser.field.QM31.Insts.CoreCmpPartialEqQM31,
    AspisR1PrefixAggregateParser.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    AspisR1PrefixAggregateParser.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
    AspisR1PrefixAggregateParser.field.M31.Insts.CoreCmpPartialEqM31.eq,
    AspisR1PrefixAggregateParser.field.QM31.ZERO,nonzero]
#print axioms ne
end NGO_PrefixHighPort
