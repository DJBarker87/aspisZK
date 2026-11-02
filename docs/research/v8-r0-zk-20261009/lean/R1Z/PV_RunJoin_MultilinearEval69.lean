import R1Z.PV_RunJoin_MultilinearSparse69
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MultilinearEval69
open Aeneas Aeneas.Std Result PV_B3_Copy_222 PV_RunJoin_MultilinearField69

theorem loop (column : Slice Q) (size : column.length=1024)
    (weights : host_multilinear.SparseWeights) (bound : weights.len.val≤1024)
    (valid : PV_RunJoin_MultilinearData69.Valid weights.data)
    (n : Nat) (i : Usize) (sum : Q) (rank : i.val+n=weights.len.val) :
    ∃ out,host_multilinear.multilinear_evaluate_qm31_loop column weights sum i=ok out := by
  induction n generalizing i sum with
  | zero =>
    have stop : ¬i<weights.len := by change ¬i.val<weights.len.val;omega
    unfold host_multilinear.multilinear_evaluate_qm31_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_multilinear.multilinear_evaluate_qm31_loop.body,stop,if_false,bind_tc_ok]
    exact ⟨sum,rfl⟩
  | succ n ih =>
    have more : i<weights.len := by change i.val<weights.len.val;omega
    have inside : i.val<weights.data.val.length := by rw [weights.data.property];change i.val<1024;omega
    let pair := weights.data.val[i.val]
    have pairmem : pair∈weights.data.val := List.getElem_mem inside
    have read : host_multilinear.sparse_weight_at weights i=ok pair := by
      simp only [host_multilinear.sparse_weight_at,Array.index_usize,Array.getElem?_Usize_eq,
        List.getElem?_eq_getElem inside]
    have rowbound : pair.1.val<column.val.length := by rw [size];exact valid pair pairmem
    obtain ⟨q,hq,_⟩ := WP.spec_imp_exists (Slice.index_usize_spec column pair.1 rowbound)
    obtain ⟨product,hp⟩ := qmul pair.2 q
    obtain ⟨next,hn⟩ := qadd sum product
    have inc := PV_B3_EvalRank222.increment i weights.len more
    obtain ⟨out,ho⟩ := ih (Usize.wrapping_add i 1#usize) next (by rw [inc];omega)
    refine ⟨out,?_⟩
    unfold host_multilinear.multilinear_evaluate_qm31_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_multilinear.multilinear_evaluate_qm31_loop.body,more,if_true,read,hq,hp,hn,lift,bind_tc_ok,Aeneas.Std.uncurry]
    exact ho

theorem complete (column : Slice Q) (point : Array Q 10#usize) (size : column.length=1024) :
    ∃ out,host_multilinear.multilinear_evaluate_qm31 column point=ok (some out) := by
  obtain ⟨weights,hw,hb,hv⟩ := PV_RunJoin_MultilinearSparse69.complete point
  obtain ⟨out,ho⟩ := loop column size weights hb hv weights.len.val 0#usize
    aspis_core.field.QM31.ZERO (by simp)
  have len : Slice.len column=1024#usize := by apply UScalar.eq_of_val_eq;exact size
  exact ⟨out,by simp only [host_multilinear.multilinear_evaluate_qm31,len,bne_self_eq_false,if_false,hw,ho,bind_tc_ok]⟩

#print axioms loop
#print axioms complete
end R1Z.PV_RunJoin_MultilinearEval69
