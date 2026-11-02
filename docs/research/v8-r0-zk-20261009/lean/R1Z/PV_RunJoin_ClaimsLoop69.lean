import R1Z.PV_RunJoin_NativeQuarticTotal69
import R1Z.PV_RunJoin_SamplerCounters54
import R1Z.ProverRwP6ArrayRead
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ClaimsLoop69
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Q := aspis_core.field.QM31

/-- The evaluator obligation is on each column actually read by the source. -/
theorem complete
    (some_ok : ∀ q : Q,core.option.Option.ok_or (some q) r1_wire.Error.Public=ok (.Ok q))
    (columns : Array (alloc.vec.Vec Q) 29#usize)
    (point : Array Q 10#usize)
    (evaluates : ∀ (lane : Usize) (v : alloc.vec.Vec Q), lane.val<29 →
      Array.index_usize columns lane=ok v →
      ∃ q,aspis_statement.constraints_v4.multilinear_evaluate_qm31 (alloc.vec.Vec.deref v) point=ok (some q))
    (n : Nat) (lane : Usize) (claims : Array Q 29#usize) (rank : lane.val+n=29) :
    ∃ out,host_semantic.claims_at_point_loop columns point claims lane=ok (out,none) := by
  induction n generalizing lane claims with
  | zero =>
    have stop : ¬lane<29#usize := by change ¬lane.val<29;omega
    unfold host_semantic.claims_at_point_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_semantic.claims_at_point_loop.body,stop,if_false,bind_tc_ok]
    exact ⟨claims,rfl⟩
  | succ n ih =>
    have more : lane<29#usize := by change lane.val<29;omega
    obtain ⟨v,hv⟩ := ProverRwP6ArrayRead.read columns lane more
    obtain ⟨q,hq⟩ := evaluates lane v more hv
    obtain ⟨next,hn,_⟩ := WP.spec_imp_exists (Array.update_spec claims lane q (by simp only [Array.length,claims.property];change lane.val<29;omega))
    have inc := PV_RunJoin_SamplerCounters54.increment lane (by change lane.val<32;omega)
    obtain ⟨out,ho⟩ := ih (Usize.wrapping_add lane 1#usize) next (by rw [inc];omega)
    refine ⟨out,?_⟩
    unfold host_semantic.claims_at_point_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_semantic.claims_at_point_loop.body,more,if_true,hv,hq,
      some_ok,core.result.Result.Insts.CoreOpsTry.branch,
      hn,lift,bind_tc_ok]
    exact ho

#print axioms complete
end R1Z.PV_RunJoin_ClaimsLoop69
