import R1Z.PV_RunJoin_LiftRowValue66
import R1Z.PV_RunJoin_LiftArray66
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LiftColumnsLoop66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMRows58 (Columns column)
open PV_RunJoin_LiftArray66 (Row matrix filled)
open PV_RunJoin_LiftRowValue66 (row)
attribute [local irreducible] PV_RunJoin_LiftPayload66.payload

theorem step (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : Columns)
    (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (p : Nat → Row) (lane : Usize) (hl : lane.val<26) :
    @host_semantic.lift_columns_loop0.body (types base) (selected base heap box ops)
      columns (matrix (filled p (row columns hlen) lane.val)) lane=
      ok (.cont (matrix (filled p (row columns hlen) (lane.val+1)),Usize.wrapping_add lane 1#usize)) := by
  have h26 : lane<26#usize := hl
  have h29 : lane<29#usize := by change lane.val<29;omega
  simp only [host_semantic.lift_columns_loop0.body,h26,if_true]
  rw [PV_RunJoin_LiftRowValue66.complete base heap box ops columns hlen lane hl]
  simp only [bind_tc_ok,massert,h29,if_true]
  rw [Array.index_mut_usize,PV_RunJoin_LiftArray66.read _ lane h29]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_LiftArray66.restore _ lane h29,
    PV_RunJoin_WeightArrayUpdate47.complete _ lane h29,
    PV_RunJoin_LiftArray66.step _ _ lane h29]
  rfl

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : Columns)
    (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (p : Nat → Row) (n : Nat) (lane : Usize) (rank : lane.val+n=26) :
    @host_semantic.lift_columns_loop0 (types base) (selected base heap box ops)
      columns (matrix (filled p (row columns hlen) lane.val)) lane=
      ok (matrix (filled p (row columns hlen) 26)) := by
  induction n generalizing lane with
  | zero =>
    have he : lane.val=26 := by omega
    have stop : ¬lane<26#usize := by change ¬lane.val<26;omega
    unfold host_semantic.lift_columns_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_semantic.lift_columns_loop0.body,stop,if_false,bind_tc_ok,he]
  | succ n ih =>
    have hl : lane.val<26 := by omega
    have inc := ProverCommitPairCounter47.next_val lane (by omega)
    unfold host_semantic.lift_columns_loop0
    rw [ProverRw19LoopBind.loop_bind]
    rw [step base heap box ops columns hlen p lane hl]
    simp only [bind_tc_ok]
    have next := ih (Usize.wrapping_add lane 1#usize) (by rw [inc];omega)
    simpa only [host_semantic.lift_columns_loop0,inc] using next

#print axioms step
#print axioms complete
end R1Z.PV_RunJoin_LiftColumnsLoop66
