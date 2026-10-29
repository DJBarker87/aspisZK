import R1Z.PV_RunJoin_BackendStoreSafe55
import R1Z.PV_RunJoin_ResultPost41
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendC1BaseLength55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
open prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
variable [ExternalTypes] [ExternalFuns]

theorem complete (columns : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (lane : Usize) (hlane : lane.val<26) (n : Nat) (row : Usize)
    (self : prover.Backend) (bound : row.val+n=1024) (hlen : self.messages.length=29) :
    Post (fun next : prover.Backend => next.messages.length=29) (c1_loop0_loop0 self columns lane row) := by
  induction n generalizing row self with
  | zero =>
    unfold c1_loop0_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [c1_loop0_loop0.body,show ¬row<1024#usize from (by change ¬row.val<1024;omega),if_neg,bind_tc_ok]
    exact hlen
  | succ n ih =>
    have hi : row<1024#usize := by change row.val<1024;omega
    have inc := PV_RunJoin_MergeLoop35.increment row (by omega)
    unfold c1_loop0_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [c1_loop0_loop0.body,if_pos hi,bind_assoc_eq]
    apply PV_RunJoin_ResultPost41.bind
    intro column
    apply PV_RunJoin_ResultPost41.bind
    intro q
    apply PV_RunJoin_ResultPost41.bind
    intro we
    obtain ⟨a,back,hr,hback⟩ := PV_RunJoin_BackendStoreSafe55.index_mut self.messages lane (by rw [hlen];omega)
    rw [hr]
    simp only [bind_tc_ok,Aeneas.Std.uncurry,bind_assoc_eq]
    apply PV_RunJoin_ResultPost41.bind
    intro a1
    simp only [lift,bind_tc_ok]
    have length : (back a1).length=29 := by rw [hback,PV_RunJoin_BackendStoreSafe55.length,hlen]
    have next := ih (Usize.wrapping_add row 1#usize) {self with messages:=back a1} (by rw [inc];omega) length
    simpa only [c1_loop0_loop0,c1_loop0_loop0.body,lift,bind_tc_ok] using next
#print axioms complete
end R1Z.PV_RunJoin_BackendC1BaseLength55
