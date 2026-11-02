import R1Z.PV_RunJoin_MultilinearRows69
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MultilinearData69
open Aeneas Aeneas.Std Result PV_B3_Copy_222 PV_RunJoin_MultilinearField69
abbrev Data := Array (Usize × Q) 1024#usize
def Valid (a : Data) : Prop := ∀ pair∈a.val,pair.1.val<1024

theorem complete (point : Array Q 10#usize) (pref trailing suffix bound : Usize)
    (hp : pref.val≤10) (hb : bound.val≤1024)
    (rows : ∀ i : Usize,i.val<bound.val →
      ((Usize.wrapping_shl i (UScalar.cast .U32 trailing)) ||| suffix).val<1024)
    (n : Nat) (i : Usize) (a : Data) (rank : i.val+n=bound.val) (valid : Valid a) :
    ∃ out,host_multilinear.sparse_eq_weights_loop2 point pref trailing suffix a bound i=ok out ∧ Valid out := by
  induction n generalizing i a with
  | zero =>
    have stop : ¬i<bound := by change ¬i.val<bound.val;omega
    refine ⟨a,?_,valid⟩
    unfold host_multilinear.sparse_eq_weights_loop2
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_multilinear.sparse_eq_weights_loop2.body,stop,if_false,bind_tc_ok]
  | succ n ih =>
    have more : i<bound := by change i.val<bound.val;omega
    obtain ⟨weight,hw⟩ := PV_RunJoin_MultilinearWeight69.complete point pref i hp
      pref.val 0#usize aspis_core.field.QM31.ONE (by simp)
    let row := (Usize.wrapping_shl i (UScalar.cast .U32 trailing)) ||| suffix
    obtain ⟨next,hn,hset⟩ := WP.spec_imp_exists (Array.update_spec a i (row,weight)
      (by simp only [Array.length,a.property];change i.val<1024;omega))
    have vnext : Valid next := by
      intro pair member
      rw [hset] at member
      rcases List.mem_or_eq_of_mem_set member with h|h
      · exact valid pair h
      · rw [h]
        exact rows i more
    have inc := PV_B3_EvalRank222.increment i bound more
    obtain ⟨out,ho,vo⟩ := ih (Usize.wrapping_add i 1#usize) next (by rw [inc];omega) vnext
    refine ⟨out,?_,vo⟩
    unfold host_multilinear.sparse_eq_weights_loop2
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_multilinear.sparse_eq_weights_loop2.body,more,if_true,lift,hw,hn,bind_tc_ok]
    exact ho

#print axioms Valid
#print axioms complete
end R1Z.PV_RunJoin_MultilinearData69
