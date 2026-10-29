import R1Z.PV_RunJoin_PublishSkeleton54
import R1Z.ProverRw19LoopBind
import R1Z.PV_B2_D_SmallScalar
import R1Z.ProverRwDictionaryDomain
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryInvalidIndex56
open Aeneas Aeneas.Std Result ProverRwFull

def badQueries : Array U32 22#usize :=
  ProverCommitArray49.array 22#usize (fun _ => 262144#u32)

theorem first : Array.index_usize badQueries 0#usize=ok 262144#u32 :=
  ProverCommitArray49.index _ _ _ (by scalar_tac)

theorem cast : UScalar.cast .Usize 262144#u32=262144#usize := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.cast_val]
  have hb := PV_B2_D_SmallScalar.size_bound
  rw [UScalar.size] at hb
  change 262144 % UScalar.size .Usize=262144
  apply Nat.mod_eq_of_lt
  rw [UScalar.size]
  omega

variable [ExternalTypes] [ExternalFuns]
theorem body (out : alloc.vec.Vec U8) (cc1 cc2 : host_commitment.Commitment)
    (word : Slice aspis_core.field.wide_exact.WideExact) (salts : host_commitment.PrivateSalts)
    (reject : aspis_core.r0.domain.FibreIndex.new 262144#usize=ok (.Err .IndexOutOfRange)) :
    prover.append_query_openings_loop.body cc1 cc2 badQueries word salts out 0#usize=fail .panic := by
  simp only [prover.append_query_openings_loop.body,
    show (0#usize)<22#usize from by scalar_tac,if_true,first,lift,bind_tc_ok,cast,reject,unwrapSlice,bind_tc_fail]

theorem source (out : alloc.vec.Vec U8) (cc1 cc2 : host_commitment.Commitment)
    (word : Slice aspis_core.field.wide_exact.WideExact) (salts : host_commitment.PrivateSalts)
    (reject : aspis_core.r0.domain.FibreIndex.new 262144#usize=ok (.Err .IndexOutOfRange)) :
    prover.append_query_openings out cc1 cc2 badQueries word salts=fail .panic := by
  unfold prover.append_query_openings prover.append_query_openings_loop
  rw [ProverRw19LoopBind.loop_bind]
  simp only [body out cc1 cc2 word salts reject,bind_tc_fail]
#print axioms badQueries
#print axioms first
#print axioms cast
#print axioms body
#print axioms source
end R1Z.PV_RunJoin_QueryInvalidIndex56
