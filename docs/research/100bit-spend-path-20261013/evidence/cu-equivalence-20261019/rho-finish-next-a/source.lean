import CuSavingsRhoFinishModel

/-! Successful concrete mutable enumeration, with the counter synchronized to
the slice cursor. The slice bound discharges checked counter overflow. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoFinishNext
open Aeneas Aeneas.Std Result
open AspisR1CuRho
open AspisR1.CuSavingsRhoFinishModel

abbrev instanceQM := AspisR1CuRho.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT field.QM31
abbrev next := AspisR1CuRho.core.iter.adapters.enumerate.IteratorEnumerate.next instanceQM

def handback (position : Nat) (out : Enum) (value : Option (Usize × field.QM31)) : Enum :=
  match value with
  | none => out
  | some (_,x) => {out with iter := {out.iter with slice := out.iter.slice.setAtNat position x}}

theorem next_done (iter : Enum) (hend : iter.iter.i = iter.iter.slice.val.length) :
    next iter = .ok (none,iter,fun out _ => out) := by
  have hlen : iter.iter.slice.len.val = iter.iter.slice.val.length := by
    simpa only [Slice.length] using Slice.len_val iter.iter.slice
  have hn : Aeneas.Std.core.slice.iter.IteratorIterMut.next iter.iter =
      .ok (none,iter.iter,fun out _ => out) := by
    unfold Aeneas.Std.core.slice.iter.IteratorIterMut.next
    split
    · rename_i hi;exact False.elim (by omega)
    · rfl
  unfold next AspisR1CuRho.core.iter.adapters.enumerate.IteratorEnumerate.next
  change (do
    let (value,state,back) ← Aeneas.Std.core.slice.iter.IteratorIterMut.next iter.iter
    let hb : Enum → Option (Usize × field.QM31) → Enum :=
      fun out item => {out with iter := back out.iter (item.map Prod.snd)}
    match value with
    | none => .ok (none,{iter with iter := state},hb)
    | some item => do
      let count ← UScalar.add iter.count 1#usize
      .ok (some (iter.count,item),{iter := state,count := count},hb)) = _
  rw [hn]
  simp only [bind_tc_ok]
  rfl

theorem next_step (iter : Enum) (hi : iter.iter.i < iter.iter.slice.val.length)
    (hcount : iter.count.val = iter.iter.i) :
    ∃ count : Usize,
      count.val = iter.iter.i+1 ∧
      next iter = .ok (some (iter.count,iter.iter.slice.val[iter.iter.i]'hi),
        {iter := {iter.iter with i := iter.iter.i+1},count := count},handback iter.iter.i) := by
  have hlen : iter.iter.slice.len.val = iter.iter.slice.val.length := by
    simpa only [Slice.length] using Slice.len_val iter.iter.slice
  have hbound : iter.count.val+(1#usize).val < 2^UScalarTy.Usize.numBits := by
    have hb := iter.iter.slice.len.bv.isLt
    change iter.iter.slice.len.val < 2^UScalarTy.Usize.numBits at hb
    change iter.count.val+1 < 2^UScalarTy.Usize.numBits
    omega
  obtain ⟨count,hadd,hval⟩ := AspisR1.ExtractedCurrentReducerOps.tryMk_success
    (iter.count.val+(1#usize).val) hbound
  change UScalar.add iter.count 1#usize = .ok count at hadd
  have hc : count.val = iter.iter.i+1 := by simpa only [hcount] using hval
  let innerBack : Iter → Option field.QM31 → Iter := fun out value =>
    match value with
    | none => out
    | some x => {out with slice := out.slice.setAtNat iter.iter.i x}
  have hn : Aeneas.Std.core.slice.iter.IteratorIterMut.next iter.iter =
      .ok (some (iter.iter.slice.val[iter.iter.i]'hi),
        {iter.iter with i := iter.iter.i+1},innerBack) := by
    unfold Aeneas.Std.core.slice.iter.IteratorIterMut.next
    split
    · apply congrArg Result.ok
      apply Prod.ext
      · apply congrArg some
        exact Slice.getElem_Nat_eq iter.iter.slice iter.iter.i hi
      · apply Prod.ext
        · rfl
        · funext out value
          cases value <;> rfl
    · rename_i hbad;exact False.elim (hbad (by rw [hlen];exact hi))
  refine ⟨count,hc,?_⟩
  unfold next AspisR1CuRho.core.iter.adapters.enumerate.IteratorEnumerate.next
  change (do
    let (value,state,back) ← Aeneas.Std.core.slice.iter.IteratorIterMut.next iter.iter
    let hb : Enum → Option (Usize × field.QM31) → Enum :=
      fun out item => {out with iter := back out.iter (item.map Prod.snd)}
    match value with
    | none => .ok (none,{iter with iter := state},hb)
    | some item => do
      let count ← UScalar.add iter.count 1#usize
      .ok (some (iter.count,item),{iter := state,count := count},hb)) = _
  rw [hn]
  simp only [bind_tc_ok,hadd]
  apply congrArg Result.ok
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · funext out value
      cases value <;> rfl

#print axioms next_done
#print axioms next_step
end AspisR1.CuSavingsRhoFinishNext
