import R1Z.PV_RunJoin_PointsReverse72
import R1Z.PV_RunJoin_PointsArithmetic72
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PointsTotal72
open Aeneas Aeneas.Std Result ControlFlow
open PV_RunJoin_PointsReverse72
abbrev Q := ProverRwDictionaryTower.Q
abbrev Points := Array Q 10#usize
abbrev source := ProverRwSuccessPointsSource.state_only_prefix.state_only_statement_points
abbrev sourceLoop := ProverRwSuccessPointsSource.state_only_prefix.state_only_statement_points_loop

theorem update {T : Type} {N : Usize} (a : Array T N) (i : Usize) (x : T)
    (hi : i.val<N.val) : ∃ out,Array.update a i x=ok out := by
  obtain ⟨out,hout,_⟩ := WP.spec_imp_exists
    (Array.update_spec a i x (by change i.val<a.val.length;rw [a.property];exact hi))
  exact ⟨out,hout⟩

theorem loop (z out : Points) (carry : Q) (fuel : Nat) (e : Usize)
    (size : e.val=fuel) (bound : fuel≤10) :
    ∃ result,sourceLoop (before e) z out carry=ok result := by
  induction fuel generalizing e out carry with
  | zero =>
    have he : e=0#usize := UScalar.eq_of_val_eq size
    subst e
    unfold sourceLoop ProverRwSuccessPointsSource.state_only_prefix.state_only_statement_points_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [ProverRwSuccessPointsSource.state_only_prefix.state_only_statement_points_loop.body,
      next_zero,bind_tc_ok]
    exact ⟨out,rfl⟩
  | succ fuel ih =>
    have hi : (pred e).val<(10#usize).val := by rw [pred_val];change e.val-1<10;omega
    obtain ⟨bit,hbit⟩ := ProverRwP6ArrayRead.read z (pred e) hi
    obtain ⟨bc,hbc⟩ := PV_RunJoin_PointsArithmetic72.mul bit carry
    obtain ⟨sum,hsum⟩ := PV_RunJoin_PointsArithmetic72.add bit carry
    obtain ⟨twice,htwice⟩ := PV_RunJoin_PointsArithmetic72.add bc bc
    obtain ⟨value,hvalue⟩ := PV_RunJoin_PointsArithmetic72.sub sum twice
    obtain ⟨updated,hupdated⟩ := update out (pred e) value hi
    obtain ⟨result,hresult⟩ := ih updated bc (pred e) (by rw [pred_val];omega) (by omega)
    have step := next_pos e (by omega)
    unfold next at step
    refine ⟨result,?_⟩
    unfold sourceLoop ProverRwSuccessPointsSource.state_only_prefix.state_only_statement_points_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [ProverRwSuccessPointsSource.state_only_prefix.state_only_statement_points_loop.body,
      step,hbit,hbc,hsum,htwice,hvalue,hupdated,bind_tc_ok,
      ProverRwSuccessPointsSource.field.QM31.mul,ProverRwSuccessPointsSource.field.QM31.add,
      ProverRwSuccessPointsSource.field.QM31.sub,Aeneas.Std.uncurry]
    exact hresult

theorem complete (z : Points) : ∃ out,source z=ok out := by
  have len : Slice.len (Array.to_slice z)=10#usize := by
    apply UScalar.eq_of_val_eq
    exact z.property
  obtain ⟨successor,hs⟩ := loop z z ProverRwSuccessPointsSource.field.QM31.ONE 10 10#usize rfl (by decide)
  obtain ⟨q,hq⟩ := ProverRwP6ArrayRead.read z 7#usize (by decide)
  obtain ⟨q1,hq1⟩ := PV_RunJoin_PointsArithmetic72.sub ProverRwSuccessPointsSource.field.QM31.ONE q
  obtain ⟨absorption,ha⟩ := update z 7#usize q1 (by decide)
  obtain ⟨q2,hq2⟩ := ProverRwP6ArrayRead.read absorption 6#usize (by decide)
  obtain ⟨q3,hq3⟩ := PV_RunJoin_PointsArithmetic72.sub ProverRwSuccessPointsSource.field.QM31.ONE q2
  obtain ⟨final,hf⟩ := update absorption 6#usize q3 (by decide)
  refine ⟨Array.make 3#usize [z,successor,final],?_⟩
  simp only [source,ProverRwSuccessPointsSource.state_only_prefix.state_only_statement_points,
    lift,bind_tc_ok,len,core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default,hs,hq,hq1,ha,hq2,hq3,hf,
    ProverRwSuccessPointsSource.field.QM31.sub]
  rfl

#print axioms update
#print axioms loop
#print axioms complete
end R1Z.PV_RunJoin_PointsTotal72
