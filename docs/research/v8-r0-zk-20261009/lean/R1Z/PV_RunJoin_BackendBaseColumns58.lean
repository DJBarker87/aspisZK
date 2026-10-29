import R1Z.PV_RunJoin_BackendMRows58
import R1Z.PV_RunJoin_BackendBasePrefix58
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendBaseColumns58
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMatrix58 PV_RunJoin_BackendMRows58 PV_RunJoin_BackendBasePrefix58
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (p : Nat → Nat → W) (n : Nat) (lane : Usize) (bound : lane.val+n=26)
    (self : prover.Backend) (hp : self.messages=matrix (bases p (values columns hlen) lane.val)) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0
      (types base) (selected base heap box ops) self columns lane=
      ok {self with messages:=matrix (bases p (values columns hlen) 26)} := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  induction n generalizing lane self with
  | zero =>
    have he : lane.val=26 := by omega
    have hn : ¬lane<26#usize := by change ¬lane.val<26;omega
    unfold prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0.body,if_neg hn,bind_tc_ok]
    rw [he] at hp
    rw [←hp]
  | succ n ih =>
    have hi : lane.val<26 := by omega
    have hir : lane<26#usize := hi
    have inc := PV_RunJoin_MergeLoop35.increment lane (by omega)
    unfold prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0.body,if_pos hir]
    rw [PV_RunJoin_BackendMRows58.complete base heap box ops self _ hp columns hlen lane hi]
    simp only [bind_tc_ok,lift]
    rw [PV_RunJoin_BackendBasePrefix58.step]
    have next := ih (Usize.wrapping_add lane 1#usize) (by rw [inc];omega)
      {self with messages:=matrix (bases p (values columns hlen) (lane.val+1))}
      (by rw [inc])
    simpa only [prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0,
      prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0.body,lift,bind_tc_ok] using next

#print axioms complete
end R1Z.PV_RunJoin_BackendBaseColumns58
