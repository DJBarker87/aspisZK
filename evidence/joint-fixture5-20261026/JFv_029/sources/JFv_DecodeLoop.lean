import JFv_Value
import OccupancyRangeTraversal
set_option autoImplicit false
namespace AspisR1.JFv_DecodeLoop
open Aeneas Aeneas.Std Result WP ControlFlow
open AspisR1DecodeKFullV10

theorem update {N : Usize} (out : Array aspis_core.field.QM31 N) (i : Usize)
    (q : aspis_core.field.QM31) (bound : i.val<N.val) : ∃ updated,Array.update out i q=ok updated := by
  have h : Array.update out i q ⦃ _ => True ⦄ := by step* 
  obtain ⟨updated,call,_⟩ := WP.spec_imp_exists h
  exact ⟨updated,call⟩

theorem success {N : Usize} (fuel : Nat) (self : r1_wire.ValidatedRecord)
    (row : U8) (offset byteOffset : Usize) (iter : core.ops.range.Range Usize)
    (out : Array aspis_core.field.QM31 N)
    (stop : iter.end=N) (span : iter.start.val+fuel=N.val)
    (values : ∀ value : Usize,value.val<N.val → ∃ q,
      r1_wire.ValidatedRecord.decode_k_value {self with row:=row} byteOffset value offset=ok (.Ok q)) :
    ∃ updated,r1_wire.ValidatedRecord.decode_k_loop self iter row offset byteOffset out=ok (updated,none) := by
  induction fuel generalizing iter out with
  | zero =>
    have done := OccupancyRangeTraversal.next_done iter (by rw [stop];omega)
    have body : r1_wire.ValidatedRecord.decode_k_loop.body self row offset byteOffset iter out=ok (.done (out,none)) := by
      simp only [r1_wire.ValidatedRecord.decode_k_loop.body,done,bind_tc_ok]
    refine ⟨out,?_⟩
    unfold r1_wire.ValidatedRecord.decode_k_loop loop
    dsimp only
    rw [body]
  | succ fuel ih =>
    have active : iter.start.val<N.val := by omega
    obtain ⟨next,advance,start,endEq,_⟩ := OccupancyRangeTraversal.next_step iter (by rw [stop];exact active)
    obtain ⟨q,read⟩ := values iter.start active
    obtain ⟨updated,set⟩ := update out iter.start q active
    have body : r1_wire.ValidatedRecord.decode_k_loop.body self row offset byteOffset iter out=ok (.cont (next,updated)) := by
      simp only [r1_wire.ValidatedRecord.decode_k_loop.body,advance,bind_tc_ok,read,
        core.result.Result.Insts.CoreOpsTry.branch,set]
    obtain ⟨final,tail⟩ := ih next updated (endEq.trans stop) (by omega)
    refine ⟨final,?_⟩
    unfold r1_wire.ValidatedRecord.decode_k_loop at tail ⊢
    unfold loop
    dsimp only
    rw [body]
    exact tail

#print axioms update
#print axioms success
end AspisR1.JFv_DecodeLoop
