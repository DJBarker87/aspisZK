import RPz7_FIo_Install
set_option autoImplicit false
namespace AspisR1.FJg_GuardEquality
open Aeneas Aeneas.Std Result

theorem field (q : FIo_Native.aspis_core.field.QM31) :
    FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq q q=ok true := by
  simp only [FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    FIo_Native.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
    FIo_Native.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
    decide_true,bind_tc_ok,ite_true]

theorem not_field (q : FIo_Native.aspis_core.field.QM31) :
    FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.ne q q=ok false := by
  change (do let b ← FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq q q
             ok (!b))=ok false
  rw [field]
  rfl

theorem list (xs : List FIo_Native.aspis_core.field.QM31) :
    List.allM (fun (x,y)=>do
      let b ← FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.ne x y
      ok (decide (¬b=true))) (xs.zip xs)=ok true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.zip_cons_cons,List.allM_cons,field,bind_tc_ok,Bool.not_true,Bool.false_eq_true,not_false_eq_true,decide_true,ite_true]
    exact ih

theorem array {N : Usize} (a : Array FIo_Native.aspis_core.field.QM31 N) :
    core.array.equality.PartialEqArray.eq
      FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 a a=ok true := by
  unfold core.array.equality.PartialEqArray.eq
  rw [if_pos rfl]
  exact list a.val
#print axioms field
#print axioms not_field
#print axioms list
#print axioms array
end AspisR1.FJg_GuardEquality
