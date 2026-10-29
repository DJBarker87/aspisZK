import R1Z.PV_RunJoin_BackendRows58
import R1Z.PV_RunJoin_BackendPrefix58
import R1Z.PV_RunJoin_SemanticEmbed50
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendFill58
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMatrix58 PV_RunJoin_BackendPrefix58

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (read : Usize → Result W)
    (input : Nat → W)
    (hread : ∀ row : Usize,row.val<1024 → read row=ok (input row.val))
    (p : Nat → Nat → W) (lane : Usize) (hl : lane.val<29)
    (n : Nat) (row : Usize) (bound : row.val+n=1024) (self : prover.Backend)
    (messages : self.messages=matrix (filled p lane.val input row.val)) :
    @PV_RunJoin_BackendRows58.run (types base) (selected base heap box ops) read lane self row=
      ok {self with messages:=matrix (filled p lane.val input 1024)} := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  induction n generalizing row self with
  | zero =>
    have he : row.val=1024 := by omega
    have hn : ¬row<1024#usize := by change ¬row.val<1024;omega
    unfold PV_RunJoin_BackendRows58.run
    rw [ProverRw19LoopBind.loop_bind]
    simp only [PV_RunJoin_BackendRows58.body,if_neg hn,bind_tc_ok]
    rw [he] at messages
    rw [←messages]
  | succ n ih =>
    have hi : row.val<1024 := by omega
    have hir : row<1024#usize := by exact hi
    have inc := PV_RunJoin_MergeLoop35.increment row (by omega)
    have hw := PV_RunJoin_BackendWrite58.complete self _ messages lane row hl hi (input row.val)
    rw [PV_RunJoin_BackendPrefix58.step] at hw
    unfold PV_RunJoin_BackendRows58.run
    rw [ProverRw19LoopBind.loop_bind]
    simp only [PV_RunJoin_BackendRows58.body,if_pos hir,hread row hi,bind_tc_ok]
    rw [hw]
    simp only [bind_tc_ok,lift]
    have next := ih (Usize.wrapping_add row 1#usize)
      {self with messages:=matrix (filled p lane.val input (row.val+1))}
      (by rw [inc];omega) (by rw [inc])
    simpa only [PV_RunJoin_BackendRows58.run] using next

#print axioms complete
end R1Z.PV_RunJoin_BackendFill58
