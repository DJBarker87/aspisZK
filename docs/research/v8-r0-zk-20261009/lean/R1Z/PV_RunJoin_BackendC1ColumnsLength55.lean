import R1Z.PV_RunJoin_BackendC1BaseLength55
import R1Z.PV_RunJoin_RecordAppend41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendC1ColumnsLength55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
open prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
variable [ExternalTypes] [ExternalFuns]

theorem complete (columns : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (n : Nat) (lane : Usize) (self : prover.Backend) (bound : lane.val+n=26)
    (hlen : self.messages.length=29) :
    Post (fun next : prover.Backend => next.messages.length=29) (c1_loop0 self columns lane) := by
  induction n generalizing lane self with
  | zero =>
    unfold c1_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [c1_loop0.body,show ¬lane<26#usize from (by change ¬lane.val<26;omega),if_neg,bind_tc_ok]
    exact hlen
  | succ n ih =>
    have hi : lane<26#usize := by change lane.val<26;omega
    have inc := PV_RunJoin_MergeLoop35.increment lane (by omega)
    unfold c1_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [c1_loop0.body,if_pos hi,bind_assoc_eq]
    apply PV_RunJoin_RecordAppend41.bind_post (PV_RunJoin_BackendC1BaseLength55.complete columns lane (by omega) 1024 0#usize self rfl hlen)
    intro next hn
    simp only [lift,bind_tc_ok]
    exact ih (Usize.wrapping_add lane 1#usize) next (by rw [inc];omega) hn
#print axioms complete
end R1Z.PV_RunJoin_BackendC1ColumnsLength55
