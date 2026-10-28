import RPt_JFq_Range
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_Compare
open Aeneas Aeneas.Std Result

theorem list_self (xs : List U8) : CheckpointBytes4Ops.listEq core.cmp.PartialEqU8 xs xs=ok true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [CheckpointBytes4Ops.listEq,core.cmp.PartialEqU8,core.cmp.impls.PartialEqU8.eq,bind_tc_ok]
    simp only [beq_self_eq_true,decide_true,ite_true,ih]

theorem ne {n : Usize} (s : Slice U8) (a : Array U8 n) (same : s.val=a.val) :
    CheckpointBytes4Ops.ne core.cmp.PartialEqU8 s a=ok false := by
  simp only [CheckpointBytes4Ops.ne,CheckpointBytes4Ops.eq,same,if_pos rfl,list_self,bind_tc_ok]
  rfl

#print axioms list_self
#print axioms ne
end AspisR1.JFq_Compare
end
