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
  generalize he : (a+b : Result U32) = r at h
  cases r with
  | ok z =>
    change some z = some c at h
    cases Option.some.inj h
    have hv := UScalar.add_equiv a b
    rw [he] at hv
    exact hv.2.1.symm
  | fail e => change none = some c at h; cases h
  | div => change none = some c at h; cases h
#print axioms value

theorem iff_value (a b c : U32) : U32.checked_add a b = some c ↔ a.val+b.val=c.val := by
  constructor
  · exact value a b c
  · intro he
    obtain ⟨z,hz,hv⟩ : ∃ z : U32, (a+b : Result U32)=ok z ∧ z.val=a.val+b.val := by
      apply WP.spec_imp_exists
      apply UScalar.add_spec
      rw [he]
      scalar_tac
    have hez : z=c := UScalar.eq_of_val_eq (hv.trans he)
    unfold U32.checked_add core.num.checked_add_UScalar
    rw [hz,hez]
    rfl
#print axioms iff_value
end R1Z.PV_RunJoin_CheckedAdd30
