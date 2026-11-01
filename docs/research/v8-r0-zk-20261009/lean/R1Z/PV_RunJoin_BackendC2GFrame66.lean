import R1Z.PV_RunJoin_ResultPost41
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendC2GFrame66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
open prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
variable [ExternalTypes] [ExternalFuns]

theorem complete (g : Array aspis_core.field.QM31 1024#usize) (n : Nat) (row : Usize)
    (self : prover.Backend) (bound : row.val+n=1024) :
    Post (fun next : prover.Backend => next.c1=self.c1) (c2_loop1 self g row) := by
  induction n generalizing row self with
  | zero =>
    unfold c2_loop1
    rw [ProverRw19LoopBind.loop_bind]
    simp only [c2_loop1.body,show ¬row<1024#usize from (by change ¬row.val<1024;omega),if_neg,bind_tc_ok]
    rfl
  | succ n ih =>
    have hi : row<1024#usize := by change row.val<1024;omega
    have inc := PV_RunJoin_MergeLoop35.increment row (by omega)
    unfold c2_loop1
    rw [ProverRw19LoopBind.loop_bind]
    simp only [c2_loop1.body,if_pos hi,bind_assoc_eq]
    apply PV_RunJoin_ResultPost41.bind
    intro q
    apply PV_RunJoin_ResultPost41.bind
    intro we
    apply PV_RunJoin_ResultPost41.bind
    rintro ⟨a,back⟩
    simp only [Aeneas.Std.uncurry,bind_assoc_eq]
    apply PV_RunJoin_ResultPost41.bind
    intro a1
    simp only [lift,bind_tc_ok]
    have next := ih (Usize.wrapping_add row 1#usize) {self with messages:=back a1} (by rw [inc];omega)
    simpa only [c2_loop1,c2_loop1.body,lift,bind_tc_ok] using next
#print axioms complete
end R1Z.PV_RunJoin_BackendC2GFrame66
