import R1Z.PV_RunJoin_NativeQuarticTotal69
import R1Z.PV_RunJoin_WeightArrayUpdate47
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MergeTotal72
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Q := aspis_core.field.QM31
abbrev Evaluations := Slice (core.result.Result Q r1_wire.Error)

theorem loop (add : ∀ a b : Q,∃ c,aspis_core.field.QM31.add a b=ok c)
    (evaluations : Evaluations) (a : Usize) (positive : a.val≠0)
    (count : Usize) (size : count.val=evaluations.length) (small : count.val≤14336)
    (samples : ∀ j,j<count.val → j/a.val<28)
    (valid : ∀ (i : Usize),i.val<count.val → ∃ q,Slice.index_usize evaluations i=ok (.Ok q))
    (values : Array Q 28#usize) (n : Nat) (i : Usize) (rank : i.val+n=count.val) :
    ∃ out,host_sumcheck.merge_evaluations_loop evaluations a values count i=ok (out,none) := by
  induction n generalizing i values with
  | zero =>
    have stop : ¬i<count := by change ¬i.val<count.val;omega
    unfold host_sumcheck.merge_evaluations_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_sumcheck.merge_evaluations_loop.body,stop,if_false,bind_tc_ok]
    exact ⟨values,rfl⟩
  | succ n ih =>
    have more : i<count := by change i.val<count.val;omega
    obtain ⟨v,hv⟩ := valid i more
    obtain ⟨sample,hs,hsv⟩ := UScalar.div_spec i (y:=a) positive
    have bound : sample.val<(28#usize).val := by rw [hsv];exact samples i.val more
    obtain ⟨q,hq⟩ := ProverRwP6ArrayRead.read values sample bound
    obtain ⟨next,hn⟩ := add q v
    have store := PV_RunJoin_WeightArrayUpdate47.complete values sample bound next
    have inc := PV_RunJoin_MergeLoop35.increment i (by omega)
    obtain ⟨out,ho⟩ := ih (Aeneas.Std.Array.set values sample next)
      (Usize.wrapping_add i 1#usize) (by rw [inc];omega)
    refine ⟨out,?_⟩
    unfold host_sumcheck.merge_evaluations_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_sumcheck.merge_evaluations_loop.body,more,if_true,hv,
      core.result.Result.Insts.CoreOpsTry.branch,hs,hq,hn,store,lift,bind_tc_ok,Aeneas.Std.uncurry]
    exact ho

theorem complete (add : ∀ a b : Q,∃ c,aspis_core.field.QM31.add a b=ok c)
    (zero : ∃ z,aspis_core.field.QM31.ZERO=ok z)
    (evaluations : Evaluations) (a : Usize) (positive : a.val≠0)
    (small : evaluations.length≤14336)
    (samples : ∀ j,j<evaluations.length → j/a.val<28)
    (valid : ∀ (i : Usize),i.val<evaluations.length → ∃ q,Slice.index_usize evaluations i=ok (.Ok q)) :
    ∃ out,host_sumcheck.merge_evaluations evaluations a=ok (.Ok out) := by
  obtain ⟨z,hz⟩ := zero
  obtain ⟨out,ho⟩ := loop add evaluations a positive (Slice.len evaluations) rfl small samples valid
    (Array.repeat 28#usize z) evaluations.length 0#usize
    (by change 0+evaluations.length=evaluations.length;omega)
  exact ⟨out,by simp only [host_sumcheck.merge_evaluations,hz,ho,bind_tc_ok,Aeneas.Std.uncurry]⟩

#print axioms loop
#print axioms complete
end R1Z.PV_RunJoin_MergeTotal72
