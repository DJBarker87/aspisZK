import R1Z.PV_RunJoin_BackendStoreSafe55
import R1Z.PV_RunJoin_ResultPost41
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendC2HLength55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
open prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
variable [ExternalTypes] [ExternalFuns]

theorem complete (h1 : Slice aspis_core.field.QM31) (n : Nat) (row : Usize)
    (self : prover.Backend) (bound : row.val+n=1024) (hlen : self.messages.length=29) :
    Post (fun next : prover.Backend => next.messages.length=29) (c2_loop0 self h1 row) := by
  induction n generalizing row self with
  | zero =>
    unfold c2_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [c2_loop0.body,show ¬row<1024#usize from (by change ¬row.val<1024;omega),if_neg,bind_tc_ok]
    exact hlen
  | succ n ih =>
    have hi : row<1024#usize := by change row.val<1024;omega
    have inc := PV_RunJoin_MergeLoop35.increment row (by omega)
    unfold c2_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [c2_loop0.body,if_pos hi,bind_assoc_eq]
    apply PV_RunJoin_ResultPost41.bind
    intro q
    apply PV_RunJoin_ResultPost41.bind
    intro we
    obtain ⟨a,back,hr,hback⟩ := PV_RunJoin_BackendStoreSafe55.index_mut self.messages 26#usize (by rw [hlen];decide)
    rw [hr]
    simp only [bind_tc_ok,Aeneas.Std.uncurry,bind_assoc_eq]
    apply PV_RunJoin_ResultPost41.bind
    intro a1
    simp only [lift,bind_tc_ok]
    have length : (back a1).length=29 := by rw [hback,PV_RunJoin_BackendStoreSafe55.length,hlen]
    have next := ih (Usize.wrapping_add row 1#usize) {self with messages:=back a1} (by rw [inc];omega) length
    simpa only [c2_loop0,c2_loop0.body,lift,bind_tc_ok] using next
#print axioms complete
end R1Z.PV_RunJoin_BackendC2HLength55
