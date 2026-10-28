import R1Z.PV_RunJoin_OuterFuns30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CheckedAdd30
open Aeneas Aeneas.Std Result
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem option_ne (a b : Option U32) :
    PV_RunJoin_Outer30.core.option.Option.Insts.CoreCmpPartialEqOption.ne
      core.cmp.PartialEqU32 a b = ok (decide (a≠b)) := by
  cases a <;> cases b <;>
    simp [PV_RunJoin_Outer30.core.option.Option.Insts.CoreCmpPartialEqOption.ne,
      core.cmp.PartialEqU32,core.cmp.impls.PartialEqU32.ne,liftFun2]
#print axioms option_ne

theorem option_ne_false (a b : Option U32) :
    PV_RunJoin_Outer30.core.option.Option.Insts.CoreCmpPartialEqOption.ne
      core.cmp.PartialEqU32 a b = ok false ↔ a=b := by
  rw [option_ne]
  simp only [Result.ok.injEq,decide_eq_false_iff_not,not_not]
#print axioms option_ne_false

#print Aeneas.Std.core.num.checked_add_UScalar

theorem value (a b c : U32) (h : U32.checked_add a b = some c) :
    a.val+b.val=c.val := by
  unfold U32.checked_add core.num.checked_add_UScalar at h
  split at h
  · cases h
    rfl
  · cases h
#print axioms value
end R1Z.PV_RunJoin_CheckedAdd30
