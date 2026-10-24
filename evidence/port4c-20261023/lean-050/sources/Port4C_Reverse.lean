import Port4C_GeometryFields

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_Reverse
open Aeneas Aeneas.Std Result

def reverse (end1 : Usize) : core.iter.adapters.rev.Rev (core.ops.range.Range Usize) :=
  ⟨{start:=0#usize,«end»:=end1}⟩

def next (end1 : Usize) := core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) (reverse end1)

theorem zero : next 0#usize=ok (none,reverse 0#usize) := by
  rfl

theorem positive (end1 : Usize) (positive : 0<end1.val) :
    ∃ i, (end1-1#usize : Result Usize)=ok i ∧ i.val+1=end1.val ∧
      next end1=ok (some i,reverse i) := by
  obtain ⟨i,hsub,hi⟩ := ExtractedCurrentReducerOps.sub_success end1 1#usize (by scalar_tac)
  have value : i.val=end1.val-1 := hi
  refine ⟨i,hsub,by omega,?_⟩
  have back : core.iter.range.StepUsize.backward_checked end1 1#usize=ok (some i) := by
    unfold core.iter.range.StepUsize.backward_checked core.iter.range.UScalarStep.backward_checked
    split
    · congr 2
      apply UScalar.eq_of_val_eq
      exact value.symm
    · rename_i bad
      exact False.elim (bad (by change 1≤end1.val; omega))
  unfold next reverse core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  change (do
    let lt ← ok (decide ((0#usize : Usize)<end1))
    let r ← (if lt then do
      let b ← core.iter.range.StepUsize.backward_checked end1 1#usize
      match b with
      | none => fail .panic
      | some e => ok (some e,{start:=0#usize,«end»:=e})
    else ok (none,{start:=0#usize,«end»:=end1}))
    ok (r.1,⟨r.2⟩))=ok (some i,⟨{start:=0#usize,«end»:=i}⟩)
  have active : (0#usize : Usize)<end1 := positive
  simp only [active,decide_true,bind_tc_ok,if_true,back]

#print axioms zero
#print axioms positive
end AspisR1.Port4C_Reverse
end
