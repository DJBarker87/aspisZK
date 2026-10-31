import R1Z.PV_RunJoin_QueryWordTotal64
set_option autoImplicit false
namespace R1Z.PV_RunJoin_QueryReadBounds64
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

theorem vector {T : Type} (v : alloc.vec.Vec T) (i : Usize) (x : T)
    (success : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) v i=ok x) :
    i.val<v.length := by
  by_contra denied
  change (match v.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some y => Result.ok y)=ok x at success
  have hnone : v.val[i.val]?=none := by
    exact List.getElem?_eq_none (Nat.le_of_not_gt denied)
  rw [hnone] at success
  cases success

theorem word (w : host_commitment.Word) (i : Usize)
    (x : aspis_core.field.wide_exact.WideExact) (success : host_commitment.Word.value w i=ok x) :
    i.val<PV_RunJoin_QueryWordTotal64.length w := by
  cases w with
  | Base v =>
    unfold host_commitment.Word.value at success
    obtain ⟨m,hm,rest⟩ := PV_RunJoin_ResultPost41.bind_success _ _ _ success
    exact vector v i m hm
  | Secure v =>
    unfold host_commitment.Word.value at success
    obtain ⟨q,hq,rest⟩ := PV_RunJoin_ResultPost41.bind_success _ _ _ success
    exact vector v i q hq

#print axioms vector
#print axioms word
end R1Z.PV_RunJoin_QueryReadBounds64
