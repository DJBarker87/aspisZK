from pathlib import Path
R=Path(__file__).resolve().parents[2]; L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
for tag,loop,param,typ in [('H','c2_loop0','h1','Slice aspis_core.field.QM31'),('G','c2_loop1','g','Array aspis_core.field.QM31 1024#usize')]:
 name='PV_RunJoin_BackendC2'+tag+'Frame66'
 text=f'''import R1Z.PV_RunJoin_ResultPost41
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
namespace R1Z.{name}
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
open prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
variable [ExternalTypes] [ExternalFuns]

theorem complete ({param} : {typ}) (n : Nat) (row : Usize)
    (self : prover.Backend) (bound : row.val+n=1024) :
    Post (fun next : prover.Backend => next.c1=self.c1) ({loop} self {param} row) := by
  induction n generalizing row self with
  | zero =>
    unfold {loop}
    rw [ProverRw19LoopBind.loop_bind]
    simp only [{loop}.body,show ¬row<1024#usize from (by change ¬row.val<1024;omega),if_neg,bind_tc_ok]
    rfl
  | succ n ih =>
    have hi : row<1024#usize := by change row.val<1024;omega
    have inc := PV_RunJoin_MergeLoop35.increment row (by omega)
    unfold {loop}
    rw [ProverRw19LoopBind.loop_bind]
    simp only [{loop}.body,if_pos hi,bind_assoc_eq]
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
    have next := ih (Usize.wrapping_add row 1#usize) {{self with messages:=back a1}} (by rw [inc];omega)
    simpa only [{loop},{loop}.body,lift,bind_tc_ok] using next
#print axioms complete
end R1Z.{name}
'''
 (L/(name+'.lean')).write_text(text)
