import XSe_ValidatorStage
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_OldHighZero
def zero (q : AspisR1PrefixAggregateParser.field.QM31) : Bool :=
 q.c0.a==0#u32 && q.c0.b==0#u32 && q.c1.a==0#u32 && q.c1.b==0#u32
theorem source (q : AspisR1PrefixAggregateParser.field.QM31) :
 core.cmp.PartialEq.ne.trait_default
 AspisR1PrefixAggregateParser.field.QM31.Insts.CoreCmpPartialEqQM31 q
 AspisR1PrefixAggregateParser.field.QM31.ZERO=ok (!zero q) := by
 unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
  AspisR1PrefixAggregateParser.field.QM31.Insts.CoreCmpPartialEqQM31
  AspisR1PrefixAggregateParser.field.QM31.Insts.CoreCmpPartialEqQM31.eq
  AspisR1PrefixAggregateParser.field.CM31.Insts.CoreCmpPartialEqCM31.eq
  AspisR1PrefixAggregateParser.field.M31.Insts.CoreCmpPartialEqM31.eq
  AspisR1PrefixAggregateParser.field.QM31.ZERO
 simp only [bind_tc_ok]
 unfold zero
 by_cases a : q.c0.a=0#u32 <;> by_cases b : q.c0.b=0#u32 <;>
  by_cases c : q.c1.a=0#u32 <;> by_cases d : q.c1.b=0#u32 <;> simp [a,b,c,d]
#print axioms source
end XSe_OldHighZero
