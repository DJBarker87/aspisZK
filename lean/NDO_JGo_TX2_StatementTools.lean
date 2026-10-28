import RPz7_FIn_WeightsInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_StatementTools
open Aeneas Aeneas.Std Result FIn_WeightsExtract
attribute [local irreducible] state_only_prefix.state_only_statement_points_loop

theorem source (alpha successor first absorbed : Array field.QM31 10#usize)
    (old7 old6 diff7 diff6 : field.QM31)
    (run : state_only_prefix.state_only_statement_points_loop
      ⟨{start:=0#usize,«end»:=10#usize}⟩ alpha alpha field.QM31.ONE=ok successor)
    (read7 : Array.index_usize alpha 7#usize=ok old7)
    (sub7 : field.QM31.sub field.QM31.ONE old7=ok diff7)
    (write7 : Array.update alpha 7#usize diff7=ok first)
    (read6 : Array.index_usize first 6#usize=ok old6)
    (sub6 : field.QM31.sub field.QM31.ONE old6=ok diff6)
    (write6 : Array.update first 6#usize diff6=ok absorbed) :
    state_only_prefix.r0.statement_points alpha=ok (Array.make 3#usize [alpha,successor,absorbed]) := by
  have length : Slice.len (Array.to_slice alpha)=10#usize := by
    apply UScalar.eq_of_val_eq
    exact alpha.property
  have rev : core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      ({start:=0#usize,«end»:=10#usize} : core.ops.range.Range Usize)=
        ok (⟨{start:=0#usize,«end»:=10#usize}⟩ : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) := by rfl
  unfold state_only_prefix.r0.statement_points state_only_prefix.state_only_statement_points
  simp only [lift,bind_tc_ok,length]
  rw [rev,bind_tc_ok,run,bind_tc_ok,read7,bind_tc_ok,sub7,bind_tc_ok,write7,bind_tc_ok,
    read6,bind_tc_ok,sub6,bind_tc_ok,write6,bind_tc_ok]
#print axioms source
end AspisR1.JGo_TX2_StatementTools
end
