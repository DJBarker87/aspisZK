import R1Z.PV_RunJoin_QueryEmptyWords57
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryInRangeFailure57
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_QueryEmptyWords57

def queries : Array U32 22#usize :=
  ProverCommitArray49.array 22#usize (fun _ => 0#u32)

theorem first : Array.index_usize queries 0#usize=ok 0#u32 :=
  ProverCommitArray49.index _ _ _ (by scalar_tac)

theorem range : PV_RunJoin_PublishSkeleton57.QueryRange queries := by
  intro q hq
  simp only [queries,ProverCommitArray49.array,List.mem_ofFn] at hq
  obtain ⟨i,hi⟩ := hq
  subst q
  scalar_tac

variable [ExternalTypes] [ExternalFuns]
theorem body (out : alloc.vec.Vec U8) (tree : host_tree.BinaryTree)
    (cc2 : host_commitment.Commitment) (word1 : Slice aspis_core.field.wide_exact.WideExact)
    (salts : host_commitment.PrivateSalts) (zero : aspis_core.field.wide_exact.WideExact)
    (hz : aspis_core.field.wide_exact.WideExact.ZERO=ok zero)
    (hi : aspis_core.r0.domain.FibreIndex.new 0#usize=ok (.Ok 0#usize)) :
    prover.append_query_openings_loop.body (broken tree) cc2 queries word1 salts out 0#usize=fail .arrayOutOfBounds := by
  simp only [prover.append_query_openings_loop.body,
    show (0#usize)<22#usize from by scalar_tac,if_true,first,lift,bind_tc_ok,
    show UScalar.cast .Usize 0#u32=0#usize from by rfl,hi,unwrapSlice,hz,fill,bind_tc_fail]

theorem source (out : alloc.vec.Vec U8) (tree : host_tree.BinaryTree)
    (cc2 : host_commitment.Commitment) (word1 : Slice aspis_core.field.wide_exact.WideExact)
    (salts : host_commitment.PrivateSalts) (zero : aspis_core.field.wide_exact.WideExact)
    (hz : aspis_core.field.wide_exact.WideExact.ZERO=ok zero)
    (hi : aspis_core.r0.domain.FibreIndex.new 0#usize=ok (.Ok 0#usize)) :
    prover.append_query_openings out (broken tree) cc2 queries word1 salts=fail .arrayOutOfBounds := by
  unfold prover.append_query_openings prover.append_query_openings_loop
  rw [ProverRw19LoopBind.loop_bind]
  simp only [body out tree cc2 word1 salts zero hz hi,bind_tc_fail]

#print axioms queries
#print axioms first
#print axioms range
#print axioms body
#print axioms source
end R1Z.PV_RunJoin_QueryInRangeFailure57
