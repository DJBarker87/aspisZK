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
 split_ifs <;> simp_all only [beq_iff_eq,Bool.and_eq_true,decide_true,decide_false,
  Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.not_true,Bool.not_false]
#print axioms source
end XSe_OldHighZero
